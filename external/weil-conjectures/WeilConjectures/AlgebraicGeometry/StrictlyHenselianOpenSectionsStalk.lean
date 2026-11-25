/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.ProEtale.HenselianLocalRing

/-!
# Sections over a strictly henselian local open and geometric stalks

Source: Stacks Project, Lemma 59.55.1 (Tag 03QO), applied inside an open subscheme
(blueprint: lem-weil-pbc-sets-strictly-henselian-open-sections-stalk).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme


set_option backward.isDefEq.respectTransparency false in
/-- The pointed form of the section construction in Stacks Tag 03QO. Shrink the
marked point to an affine Spec B, localize B at its marked prime q, and use Olivier's
theorem (Tag 092Z) to identify B_q with R. The geometric point's ring map extends
uniquely to B_q, so the resulting section passes through that geometric point. -/
private theorem exists_pointed_section_spec
    {R : Type u} [CommRing R] [IsStrictlyHenselianLocalRing R]
    {Ω : Type u} [Field Ω] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [AlgebraicGeometry.Etale f]
    (a : Spec (.of Ω) ⟶ X) (t : Spec (.of Ω) ⟶ Spec (.of R))
    (hat : a ≫ f = t) (ht : t default = IsLocalRing.closedPoint R) :
    ∃ σ : Spec (.of R) ⟶ X, σ ≫ f = 𝟙 _ ∧ t ≫ σ = a := by
  obtain ⟨B, j, hj, haj, _⟩ :=
    exists_affine_mem_range_and_range_subset (x := a default) (U := ⊤) (by simp)
  let : IsOpenImmersion j := hj
  let l : Spec (.of Ω) ⟶ Spec B := IsOpenImmersion.lift j a (by
    rintro _ ⟨z, rfl⟩
    simpa only [Subsingleton.elim z default] using haj)
  have hl : l ≫ j = a := IsOpenImmersion.lift_fac j a _
  let φ : CommRingCat.of R ⟶ B := Spec.preimage (j ≫ f)
  have hφ : Spec.map φ = j ≫ f := Spec.map_preimage _
  have hφe : φ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale), hφ]
    infer_instance
  algebraize [φ.hom]
  let q : PrimeSpectrum B := l default
  have hq : q.asIdeal.comap φ.hom = IsLocalRing.maximalIdeal R := by
    have h : (Spec.map φ) q = IsLocalRing.closedPoint R := by
      rw [hφ]
      change (l ≫ (j ≫ f)) default = _
      rw [← Category.assoc, hl, hat, ht]
    exact congrArg PrimeSpectrum.asIdeal h
  let Bq := Localization.AtPrime q.asIdeal
  have : Algebra.WeaklyEtale R B := inferInstance
  have : Algebra.WeaklyEtale R Bq := Algebra.WeaklyEtale.trans R B Bq
  have : IsLocalHom (algebraMap R Bq) := by
    refine ⟨fun z hz ↦ ?_⟩
    rw [IsScalarTower.algebraMap_apply R B Bq,
      IsLocalization.AtPrime.isUnit_to_map_iff Bq q.asIdeal] at hz
    by_contra hn
    exact hz (by
      have : z ∈ IsLocalRing.maximalIdeal R := hn
      rw [← hq] at this
      exact this)
  let er : R ≃+* Bq := RingEquiv.ofBijective (algebraMap R Bq)
    (Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing (R := R) (S := Bq))
  let ψ : B ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (er.symm.toRingHom.comp (algebraMap B Bq))
  have hψ : φ ≫ ψ = 𝟙 _ := by
    ext z
    change er.symm (algebraMap B Bq (algebraMap R B z)) = z
    rw [← IsScalarTower.algebraMap_apply R B Bq]
    exact er.symm_apply_apply z
  let χ : B ⟶ CommRingCat.of Ω := Spec.preimage l
  let θ : CommRingCat.of R ⟶ CommRingCat.of Ω := Spec.preimage t
  have hχ : Spec.map χ = l := Spec.map_preimage _
  have hθ : Spec.map θ = t := Spec.map_preimage _
  have hφχ : φ ≫ χ = θ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hχ, hφ, hθ, ← Category.assoc, hl, hat]
  have hunit : ∀ z : q.asIdeal.primeCompl, IsUnit (χ.hom z) := by
    intro z
    apply isUnit_iff_ne_zero.mpr
    intro hz
    apply z.property
    change z.val ∈ (l default).asIdeal
    rw [← hχ, Spec.map_apply]
    simpa only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, default_asIdeal,
      Ideal.mem_bot] using hz
  let χq : Bq →+* Ω := IsLocalization.lift hunit
  have hχq : χq.comp (algebraMap R Bq) = θ.hom := by
    ext z
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply R B Bq,
      IsLocalization.lift_eq]
    exact congrArg (fun m : CommRingCat.of R ⟶ CommRingCat.of Ω ↦ m.hom z) hφχ
  have hψθ : ψ ≫ θ = χ := by
    ext z
    change θ.hom (er.symm (algebraMap B Bq z)) = χ.hom z
    rw [← hχq, RingHom.comp_apply]
    change χq (er (er.symm (algebraMap B Bq z))) = _
    rw [er.apply_symm_apply]
    exact IsLocalization.lift_eq hunit z
  refine ⟨Spec.map ψ ≫ j, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp, hψ, Spec.map_id]
  · rw [← hθ, ← Spec.map_comp_assoc, hψθ, hχ, hl]

set_option backward.isDefEq.respectTransparency false in
/-- A pointed section over the open U, obtained by pulling back to U and applying
`exists_pointed_section_spec`. This is the geometric step of Stacks Tag 03QO. -/
private theorem strictlyHenselianOpen_pointedSection
    {T : Scheme.{u}} (U : T.Opens) {R : Type u} [CommRing R] [IsLocalRing R]
    (hR : IsStrictlyHenselianLocalRing R) (e : U.toScheme ≅ Spec (.of R))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ T)
    (t : Spec (.of Ω) ⟶ U.toScheme) (ht : t ≫ U.ι = s)
    (hclosed : (t ≫ e.hom) default = IsLocalRing.closedPoint R)
    (X : T.Etale) (x : (pointSmallEtale s).fiber.obj X) :
    ∃ f : Etale.mk U.ι ⟶ X,
      (pointSmallEtale s).fiber.map f (Over.homMk t ht) = x := by
  let : IsStrictlyHenselianLocalRing R := hR
  let Y := Limits.pullback X.hom U.ι
  let p : Y ⟶ U.toScheme := Limits.pullback.snd X.hom U.ι
  let a : Spec (.of Ω) ⟶ Y := Limits.pullback.lift x.left t (by
    have hx : x.left ≫ X.hom = s := x.w
    rw [hx, ht])
  have ha : a ≫ (p ≫ e.hom) = t ≫ e.hom := by
    simp [a, p]
  obtain ⟨σ, hσ, htσ⟩ := exists_pointed_section_spec (p ≫ e.hom) a
    (t ≫ e.hom) ha hclosed
  let g : U.toScheme ⟶ X.left :=
    e.hom ≫ σ ≫ Limits.pullback.fst X.hom U.ι
  have hg : g ≫ X.hom = U.ι := by
    have hp : e.hom ≫ σ ≫ p = 𝟙 U.toScheme := by
      apply (cancel_mono e.hom).mp
      simp only [Category.assoc, Category.id_comp, hσ, Category.comp_id]
    dsimp [g]
    rw [Category.assoc, Category.assoc, Limits.pullback.condition]
    change (e.hom ≫ σ ≫ p) ≫ U.ι = U.ι
    rw [hp, Category.id_comp]
  refine ⟨MorphismProperty.Over.homMk g hg, ?_⟩
  apply Over.OverMorphism.ext
  change t ≫ g = x.left
  dsimp [g]
  rw [← Category.assoc t e.hom, ← Category.assoc, htσ]
  simp [a]



/-- For a sheaf of sets on `T`, the germ map from sections over a strictly henselian
local open `U` to the geometric stalk at its closed point is bijective.
Source: Stacks Project, Lemma 59.55.1 (Tag 03QO)
(blueprint: lem-weil-pbc-sets-strictly-henselian-open-sections-stalk).

Proof:
1. Represent a germ over a pointed etale neighbourhood `V`. Shrink around its marked
point to an affine open contained in the inverse image of `U`, using
`lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink`. This gives an etale algebra
`R → A` and a prime above the maximal ideal of `R`.
2. The residue extension is finite separable by
`lem-weil-pbc-etale-algebra-residue-field-separable`, and is trivial by
`lem-pc-sepclosed-finite-sep-trivial`. The root-lifting criterion
`lem-weil-pbc-henselian-local-root-lifting` and the retraction lemma
`lem-weil-pbc-root-lifting-etale-retraction` give an algebra retraction `A → R`.
Its spectrum yields a section `U → V` over `T` through the marked geometric point:
the residue-field maps agree because the retraction inverts the residue isomorphism.
3. Pointed etale neighbourhoods are cofiltered by
`definition-torsion-sheaves--3`. The full subcategory consisting
of `(U, t)` has only its identity endomorphism, since `U.ι` is a monomorphism, and
maps to every neighbourhood by step 2. Apply
`lem-weil-pbc-colimit-initial-full-subcategory` and
`definition-torsion-sheaves--3` to compute the stalk as `G(U)`.
The colimit coprojection is precisely the germ map written below. -/
theorem strictlyHenselianOpen_toPresheafFiber_bijective
    {T : Scheme.{u}} (U : T.Opens) {R : Type u} [CommRing R] [IsLocalRing R]
    (hR : IsStrictlyHenselianLocalRing R) (e : U.toScheme ≅ Spec (.of R))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ T)
    (t : Spec (.of Ω) ⟶ U.toScheme) (ht : t ≫ U.ι = s)
    (hclosed : (t ≫ e.hom) default = IsLocalRing.closedPoint R)
    (G : Sheaf (smallEtaleTopology T) (Type (max u v))) :
    Function.Bijective
      ((pointSmallEtale s).toPresheafFiber (Etale.mk U.ι) (Over.homMk t ht) G.obj) := by
  let Φ := pointSmallEtale s
  let xU : Φ.fiber.obj (Etale.mk U.ι) := Over.homMk t ht
  have hsec := strictlyHenselianOpen_pointedSection U hR e s t ht hclosed
  constructor
  · intro a b hab
    obtain ⟨Y, f, y, _, heq⟩ := (Φ.toPresheafFiber_eq_iff' (P := G.obj) _ xU a b).mp hab
    obtain ⟨g, _⟩ := hsec Y y
    have hgf : g ≫ f = 𝟙 _ := by
      apply MorphismProperty.Over.Hom.ext
      apply (cancel_mono U.ι).mp
      change (g.left ≫ f.left) ≫ U.ι = (𝟙 U.toScheme) ≫ U.ι
      have hf' : f.left ≫ U.ι = Y.hom := f.w
      have hg' : g.left ≫ Y.hom = U.ι := g.w
      rw [Category.assoc, hf', hg', Category.id_comp]
    have h := congrArg (G.obj.map g.op) heq
    simpa [← types_comp_apply, ← Functor.map_comp, ← op_comp, hgf] using h
  · intro z
    obtain ⟨X, x, a, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := G.obj) z
    obtain ⟨f, hf⟩ := hsec X x
    refine ⟨G.obj.map f.op a, ?_⟩
    rw [Φ.toPresheafFiber_w_apply, hf]

end AlgebraicGeometry.Scheme
