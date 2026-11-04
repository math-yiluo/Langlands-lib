import Langlands.GroupScheme.PseudoComplete
import Mathlib.AlgebraicGeometry.Stalk

/-! # Extending fraction-field points along a dominating local extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Langlands.GroupScheme.PseudoComplete

section Algebra

variable {R R' : Type*} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

/-- The map of fraction fields induced by an injective map of domains. -/
abbrev fractionRingMap (f : R →+* R') (hf : Function.Injective f) :
    FractionRing R →+* FractionRing R' :=
  IsLocalization.map (S := FractionRing R) (FractionRing R') f
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hf)

omit [IsDomain R] in
theorem fractionRingMap_algebraMap (f : R →+* R') (hf : Function.Injective f) (r : R) :
    fractionRingMap f hf (algebraMap R (FractionRing R) r) =
      algebraMap R' (FractionRing R') (f r) :=
  IsLocalization.map_eq _ _

theorem isLocalHom_fractionRingMap (f : R →+* R') (hf : Function.Injective f) :
    IsLocalHom (fractionRingMap f hf) :=
  ⟨fun a ha => isUnit_iff_ne_zero.mpr fun h => by simp [h] at ha⟩

/-- Domination: if `R` is a valuation ring and `f : R → R'` is injective and local, an element
of the fraction field of `R` whose image in the fraction field of `R'` lies in `R'` already
lies in `R`. -/
theorem isInteger_of_fractionRingMap [ValuationRing R] (f : R →+* R') (hf : Function.Injective f)
    [IsLocalHom f] (a : FractionRing R)
    (ha : IsLocalization.IsInteger R' (fractionRingMap f hf a)) :
    IsLocalization.IsInteger R a := by
  rcases ValuationRing.isInteger_or_isInteger R a with h | ⟨b, hb⟩
  · exact h
  by_cases ha0 : a = 0
  · exact ⟨0, by simp [ha0]⟩
  obtain ⟨c, hc⟩ := ha
  have h1 : algebraMap R' (FractionRing R') (f b * c) = 1 := by
    rw [map_mul, hc, ← fractionRingMap_algebraMap f hf, hb, ← map_mul, inv_mul_cancel₀ ha0,
      map_one]
  have hbu : IsUnit (f b) :=
    IsUnit.of_mul_eq_one c (IsFractionRing.injective R' (FractionRing R') (by rw [h1, map_one]))
  obtain ⟨u, rfl⟩ := (isUnit_map_iff f b).mp hbu
  exact ⟨↑u⁻¹, by rw [map_units_inv, hb, inv_inv]⟩

end Algebra

section Scheme

variable {X : Scheme.{u}}

/-- A morphism from an affine scheme into `X` whose image lies in an affine open `U` is
`Spec` of the induced map on sections of `U`, followed by `U.fromSpec`. -/
theorem SpecMap_appLE_comp_fromSpec {A : CommRingCat.{u}} (g : Spec A ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) (h : g ⁻¹ᵁ U = ⊤) :
    Spec.map (g.appLE U ⊤ h.ge ≫ (Scheme.ΓSpecIso A).hom) ≫ hU.fromSpec = g := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec g hU (isAffineOpen_top _) h.ge
  rw [IsAffineOpen.fromSpec_top, Iso.eq_inv_comp, Scheme.isoSpec_Spec_hom] at this
  rw [Spec.map_comp, Category.assoc, this]

set_option backward.isDefEq.respectTransparency false in
/-- If a morphism from a local spectrum, precomposed with `Spec` of a local homomorphism of
local rings, maps everything into an open `U`, then so does the morphism itself. -/
theorem preimage_eq_top_of_comp {A B : CommRingCat.{u}} [IsLocalRing A] [IsLocalRing B]
    (φ : A ⟶ B) [IsLocalHom φ.hom] (x : Spec A ⟶ X) {U : X.Opens}
    (h : (Spec.map φ ≫ x) ⁻¹ᵁ U = ⊤) : x ⁻¹ᵁ U = ⊤ := by
  apply Scheme.preimage_eq_top_of_closedPoint_mem
  rw [← Spec_closedPoint (f := φ)]
  change closedPoint B ∈ (Spec.map φ ≫ x) ⁻¹ᵁ U
  rw [h]
  trivial

/-- Domination lemma for scheme points. Let `R` be a valuation ring, `R'` a local domain and
`f : R → R'` an injective local homomorphism. If the restriction of a fraction-field point
`x : Spec (Frac R) → X` to `Spec (Frac R')` extends over `Spec R'`, then `x` extends over
`Spec R`. No separatedness of `X` is needed. -/
theorem exists_comp_eq_of_dominates {R R' : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing R'] [IsDomain R'] [IsLocalRing R'] (f : R →+* R') (hf : Function.Injective f)
    [IsLocalHom f] (x : Spec (CommRingCat.of (FractionRing R)) ⟶ X)
    (y : Spec (CommRingCat.of R') ⟶ X)
    (hxy : Spec.map (CommRingCat.ofHom (algebraMap R' (FractionRing R'))) ≫ y =
      Spec.map (CommRingCat.ofHom (fractionRingMap f hf)) ≫ x) :
    ∃ z : Spec (CommRingCat.of R) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ z = x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (y (closedPoint (CommRingCat.of R')))) isOpen_univ
  have hU : IsAffineOpen U := hU
  have hyU : y ⁻¹ᵁ U = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem y hpU
  have : IsLocalHom (CommRingCat.ofHom (fractionRingMap f hf)).hom :=
    isLocalHom_fractionRingMap f hf
  have hxU : x ⁻¹ᵁ U = ⊤ := by
    refine preimage_eq_top_of_comp (CommRingCat.ofHom (fractionRingMap f hf)) x ?_
    rw [← hxy, Scheme.Hom.comp_preimage, hyU, Scheme.Hom.preimage_top]
  obtain ⟨χ, hx⟩ : ∃ χ, Spec.map χ ≫ hU.fromSpec = x :=
    ⟨_, SpecMap_appLE_comp_fromSpec x hU hxU⟩
  obtain ⟨ψ, hy⟩ : ∃ ψ, Spec.map ψ ≫ hU.fromSpec = y :=
    ⟨_, SpecMap_appLE_comp_fromSpec y hU hyU⟩
  have key : ψ ≫ CommRingCat.ofHom (algebraMap R' (FractionRing R')) =
      χ ≫ CommRingCat.ofHom (fractionRingMap f hf) := by
    apply Spec.map_injective
    rw [← cancel_mono hU.fromSpec]
    simp only [Spec.map_comp, Category.assoc, hx, hy]
    exact hxy
  have hint : ∀ s, χ.hom s ∈ (Algebra.ofId R (FractionRing R)).range := by
    intro s
    obtain ⟨r, hr⟩ := isInteger_of_fractionRingMap f hf (χ.hom s)
      ⟨ψ.hom s, by simpa using congr(($key).hom s)⟩
    exact ⟨r, hr⟩
  let e := AlgEquiv.ofInjective (Algebra.ofId R (FractionRing R))
    (IsFractionRing.injective R (FractionRing R))
  let χ' := e.symm.toRingHom.comp (χ.hom.codRestrict _ hint)
  have hχ' : ∀ s, algebraMap R (FractionRing R) (χ' s) = χ.hom s := by
    intro s
    change Algebra.ofId R (FractionRing R) (e.symm _) = _
    rw [← AlgEquiv.ofInjective_apply _ (IsFractionRing.injective R (FractionRing R)),
      AlgEquiv.apply_symm_apply]
    rfl
  refine ⟨Spec.map (CommRingCat.ofHom χ') ≫ hU.fromSpec, ?_⟩
  rw [← Spec.map_comp_assoc, ← hx]
  refine congrArg (· ≫ hU.fromSpec) (congrArg Spec.map ?_)
  ext s
  simpa using hχ' s

end Scheme

section Over

variable {k : Type u} [Field k]

/-- A scheme map `Spec R → X` whose restriction to the generic point is a `k`-point of `X` is
itself a `k`-point. -/
theorem exists_extension_of_comp_eq (X : Over (Spec (CommRingCat.of k))) (R : Type u)
    [CommRing R] [IsDomain R] [Algebra k R] (x : algebraSpec k (FractionRing R) ⟶ X)
    (z : Spec (CommRingCat.of R) ⟶ X.left)
    (hz : Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ z = x.left) :
    ∃ xR : algebraSpec k R ⟶ X, genericPoint (k := k) R ≫ xR = x := by
  have hp : Spec.preimage (z ≫ X.hom) = CommRingCat.ofHom (algebraMap k R) := by
    have h1 : Spec.map (Spec.preimage (z ≫ X.hom) ≫
          CommRingCat.ofHom (algebraMap R (FractionRing R))) =
        Spec.map (CommRingCat.ofHom (algebraMap k R) ≫
          CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
      rw [Spec.map_comp, Spec.map_preimage, reassoc_of% hz]
      refine (Over.w x).trans ?_
      rw [algebraSpec_hom, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq k R (FractionRing R)]
    have h2 := Spec.map_injective h1
    ext c
    apply IsFractionRing.injective R (FractionRing R)
    simpa using congr(($h2).hom c)
  have hw : z ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k R)) := by
    rw [← hp, Spec.map_preimage]
  exact ⟨Over.homMk z hw, Over.OverMorphism.ext hz⟩

/-- The `k`-algebra map of fraction fields induced by an injective `k`-algebra map of
domains. -/
def fractionAlgHom {R R' : Type u} [CommRing R] [IsDomain R] [Algebra k R] [CommRing R']
    [IsDomain R'] [Algebra k R'] (φ : R →ₐ[k] R') (hφ : Function.Injective φ) :
    FractionRing R →ₐ[k] FractionRing R' :=
  AlgHom.mk (fractionRingMap (φ : R →+* R') hφ) fun c => by
    change fractionRingMap (φ : R →+* R') hφ (algebraMap k (FractionRing R) c) = _
    rw [IsScalarTower.algebraMap_apply k R (FractionRing R),
      fractionRingMap_algebraMap (φ : R →+* R') hφ]
    simp only [AlgHom.coe_toRingHom, AlgHom.commutes]
    exact (IsScalarTower.algebraMap_apply k R' (FractionRing R') c).symm

/-- Domination lemma over `Spec k`. Let `φ : R → R'` be an injective local `k`-algebra map from a
valuation ring to a local domain. If the restriction of a fraction-field point `x` of `X`
along `Frac R → Frac R'` extends over `R'`, then `x` extends over `R`. -/
theorem exists_extension_of_dominates (X : Over (Spec (CommRingCat.of k))) {R R' : Type u}
    [CommRing R] [IsDomain R] [ValuationRing R] [Algebra k R] [CommRing R'] [IsDomain R']
    [IsLocalRing R'] [Algebra k R'] (φ : R →ₐ[k] R') (hφ : Function.Injective φ)
    [IsLocalHom (φ : R →+* R')] (x : algebraSpec k (FractionRing R) ⟶ X)
    (y : algebraSpec k R' ⟶ X)
    (hxy : genericPoint (k := k) R' ≫ y =
      (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (fractionAlgHom φ hφ)).op ≫ x) :
    ∃ xR : algebraSpec k R ⟶ X, genericPoint (k := k) R ≫ xR = x := by
  obtain ⟨z, hz⟩ := exists_comp_eq_of_dominates (φ : R →+* R') hφ x.left y.left
    congr(($hxy).left)
  exact exists_extension_of_comp_eq X R x z hz

end Over

end Langlands.GroupScheme.PseudoComplete
