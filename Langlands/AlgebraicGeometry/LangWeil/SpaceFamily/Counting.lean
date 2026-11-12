import Langlands.AlgebraicGeometry.LangWeil.SpaceFamily.DegreePoints
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker

/-!
# Counting finite-field points of a separated algebraic space by degree strata

Let `X` be a separated algebraic space with an affine étale chart (a `SepChart`) and
`g : X → M` a morphism to a scheme. For a finite field `κ` and `m ∈ M(κ)`, the `κ`-points of `X`
over `m` are in bijection with the disjoint union over `n` below the tuple-length bound of the
`κ`-points of the exact-degree scheme `D_n` over `m`, through the étale maps `e_n : V_n → X`.
Injectivity uses the uniqueness of degree representatives over an algebraic closure `Ω` of
`κ`; surjectivity descends the unique representative of a point from `Ω` to `κ` by Galois
invariance, and uses that `κ`-points of a separated algebraic space are determined by their
`Ω`-points.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.LangWeil.SpaceFamily

open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry (EtaleEquivalenceRelation)

set_option backward.isDefEq.respectTransparency false

/-- Points of a separated algebraic space with values in a field are determined by their
values in an extension field: the represented equalizer of two such points is a closed
subscheme of the spectrum of the field with a point, hence everything. -/
theorem eq_of_specMap_comp_eq {X : AlgebraicSpace S0.{u}} (hX : AlgebraicSpace.IsSeparated X)
    {κ Ω : Type u} [Field κ] [Field Ω] [Algebra κ Ω]
    {z₁ z₂ : (schemeYoneda S0).obj (toOver (Spec (CommRingCat.of κ))) ⟶ X.presheaf}
    (h : (schemeYoneda S0).map (toOverHom (specMap κ Ω)) ≫ z₁ =
      (schemeYoneda S0).map (toOverHom (specMap κ Ω)) ≫ z₂) :
    z₁ = z₂ := by
  have hr : (schemeYoneda S0).relativelyRepresentable z₁ := X.representable_from_scheme z₁
  have hpb := hr.isPullback' z₂
  have hci := closedImmersion_pair_of_isPullback hX z₁ z₂ (hr.fst' z₂) (hr.snd z₂) hpb
  let ρ := hr.lift' (toOverHom (specMap κ Ω)) (toOverHom (specMap κ Ω)) h
  have hρ : ρ ≫ prod.lift (hr.fst' z₂) (hr.snd z₂) =
      toOverHom (specMap κ Ω) ≫ prod.lift (𝟙 _) (𝟙 _) := by
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, Category.assoc, prod.lift_fst, Category.comp_id]
      exact hr.lift'_fst _ _ _
    · rw [Category.assoc, prod.lift_snd, Category.assoc, prod.lift_snd, Category.comp_id]
      exact hr.lift'_snd _ _ _
  obtain ⟨σ, hσ⟩ := exists_lift_of_isClosedImmersion (prod.lift (hr.fst' z₂) (hr.snd z₂)).left
    (prod.lift (𝟙 (toOver (Spec (CommRingCat.of κ)))) (𝟙 _)).left ρ.left (by
      rw [← Over.comp_left, hρ, Over.comp_left]
      rfl)
  let σ' : toOver (Spec (CommRingCat.of κ)) ⟶ hr.pullback z₂ :=
    Over.homMk σ (specULiftZIsTerminal.hom_ext _ _)
  have hσ' : σ' ≫ prod.lift (hr.fst' z₂) (hr.snd z₂) = prod.lift (𝟙 _) (𝟙 _) :=
    Over.OverMorphism.ext hσ
  have h1 : σ' ≫ hr.fst' z₂ = 𝟙 _ := by
    simpa using congrArg (· ≫ prod.fst) hσ'
  have h2 : σ' ≫ hr.snd z₂ = 𝟙 _ := by
    simpa using congrArg (· ≫ prod.snd) hσ'
  calc z₁ = (schemeYoneda S0).map (σ' ≫ hr.fst' z₂) ≫ z₁ := by
        rw [h1, CategoryTheory.Functor.map_id, Category.id_comp]
    _ = (schemeYoneda S0).map (σ' ≫ hr.snd z₂) ≫ z₂ := by
        rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hpb.w]
    _ = z₂ := by rw [h2, CategoryTheory.Functor.map_id, Category.id_comp]

/-- A morphism of schemes is determined by the morphism of functors of points over the
terminal base that it induces. -/
theorem eq_of_map_toOverHom_eq {T T' : Scheme.{u}} {f f' : T ⟶ T'}
    (h : (schemeYoneda S0).map (toOverHom f) = (schemeYoneda S0).map (toOverHom f')) :
    f = f' :=
  congrArg CommaMorphism.left ((schemeYoneda S0).map_injective h)

namespace SepChart

variable (c : SepChart.{u}) {M : Scheme.{u}}
  (g : c.X.presheaf ⟶ (schemeYoneda S0).obj (toOver M))

/-- The morphism `V_n → M` through which `e_n` followed by `g` factors. -/
def p (n : ℕ) : c.E.tupleSymmetricScheme n ⟶ M :=
  ((schemeYoneda S0).preimage (c.e n ≫ g)).left

/-- The image in `M` of the image in `X` of a point of `V_n`. -/
theorem ptE_g (n : ℕ) {T : Scheme.{u}} (v : T ⟶ c.E.tupleSymmetricScheme n) :
    c.ptE n v ≫ g = (schemeYoneda S0).map (toOverHom (v ≫ c.p g n)) := by
  have h : toOverHom (v ≫ c.p g n) =
      homOver (Y := c.quot n) v ≫ (schemeYoneda S0).preimage (c.e n ≫ g) := by
    ext; rfl
  rw [h, Functor.map_comp, Functor.map_preimage, ptE, Category.assoc]

/-- The `κ`-points of `X` over a `κ`-point `m` of `M`. -/
def fibrePoints (κ : Type u) [Field κ] (m : Spec (CommRingCat.of κ) ⟶ M) : Type (u + 1) :=
  {z : (schemeYoneda S0).obj (toOver (Spec (CommRingCat.of κ))) ⟶ c.X.presheaf //
    z ≫ g = (schemeYoneda S0).map (toOverHom m)}

/-- The `κ`-points of `V_n` over a `κ`-point `m` of `M` outside the next threshold. -/
def degreePoints (κ : Type u) [Field κ] (m : Spec (CommRingCat.of κ) ⟶ M) (n : ℕ) : Type u :=
  {v : Spec (CommRingCat.of κ) ⟶ c.E.tupleSymmetricScheme n //
    v (IsLocalRing.closedPoint κ) ∉ c.E.tupleSymmetricThresholdOpen n (n + 1) ∧
      v ≫ c.p g n = m}

/-- The image in `X` of a point of some `V_n` outside the next threshold. -/
def degreeToFibre (κ : Type u) [Field κ] (m : Spec (CommRingCat.of κ) ⟶ M) :
    (Σ n : Fin c.N, c.degreePoints g κ m n) → c.fibrePoints g κ m :=
  fun v => ⟨c.ptE v.1 v.2.1, by rw [ptE_g, v.2.2.2]⟩

variable {c g}

theorem degreeToFibre_injective (κ : Type u) [Field κ] (m : Spec (CommRingCat.of κ) ⟶ M) :
    Function.Injective (c.degreeToFibre g κ m) := by
  rintro ⟨n, v, hv, hvm⟩ ⟨k, w, hw, hwm⟩ h
  have h' : c.ptE n v = c.ptE k w := congrArg Subtype.val h
  let Ω := AlgebraicClosure κ
  have hΩ : c.ptE n (specMap κ Ω ≫ v) = c.ptE k (specMap κ Ω ≫ w) := by
    rw [ptE_comp, ptE_comp, h']
  have hv' : (specMap κ Ω ≫ v) (IsLocalRing.closedPoint Ω) ∉
      c.E.tupleSymmetricThresholdOpen n (n + 1) := by
    rw [specMap_comp_apply]; exact hv
  have hw' : (specMap κ Ω ≫ w) (IsLocalRing.closedPoint Ω) ∉
      c.E.tupleSymmetricThresholdOpen k (k + 1) := by
    rw [specMap_comp_apply]; exact hw
  have hkn := le_of_ptE_eq _ hv' _ hΩ
  have hnk := le_of_ptE_eq _ hw' _ hΩ.symm
  have hnk' : n = k := Fin.ext (le_antisymm hnk hkn)
  subst hnk'
  have hvw := eq_of_ptE_eq _ hv' _ hΩ
  have : v = w := spec_hom_ext hvw
  subst this
  rfl

theorem degreeToFibre_surjective (κ : Type u) [Field κ] [Finite κ]
    (m : Spec (CommRingCat.of κ) ⟶ M) :
    Function.Surjective (c.degreeToFibre g κ m) := by
  rintro ⟨z, hz⟩
  let Ω := AlgebraicClosure κ
  have : IsSepClosure κ Ω := IsSepClosure.of_isAlgClosure_of_perfectField κ Ω
  have : IsGalois κ Ω := IsSepClosure.isGalois
  obtain ⟨n, hn, w, hw, hwz⟩ :=
    exists_ptE_eq (c := c) ((schemeYoneda S0).map (toOverHom (specMap κ Ω)) ≫ z)
  have hinv : ∀ σ : Ω ≃ₐ[κ] Ω, Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ w = w := by
    intro σ
    refine (eq_of_ptE_eq w hw _ ?_).symm
    rw [ptE_comp, hwz, ← Category.assoc, ← Functor.map_comp, ← toOverHom_comp,
      specMap_aut_comp]
  obtain ⟨v, hv⟩ := exists_desc_of_aut_invariant w hinv
  have hvz : c.ptE n v = z := by
    apply eq_of_specMap_comp_eq c.sep (Ω := Ω)
    rw [← ptE_comp, hv, hwz]
  refine ⟨⟨⟨n, hn⟩, v, ?_, ?_⟩, Subtype.ext hvz⟩
  · rw [← specMap_comp_apply (Ω := Ω), hv]
    exact hw
  · apply eq_of_map_toOverHom_eq
    rw [← ptE_g, hvz, hz]

/-- The `κ`-points of `X` over `m` correspond to the points of the `V_n`, `n` below the
tuple-length bound, over `m` and outside the next threshold. -/
def degreeFibreEquiv (κ : Type u) [Field κ] [Finite κ] (m : Spec (CommRingCat.of κ) ⟶ M) :
    (Σ n : Fin c.N, c.degreePoints g κ m n) ≃ c.fibrePoints g κ m :=
  Equiv.ofBijective _ ⟨degreeToFibre_injective κ m, degreeToFibre_surjective κ m⟩

/-- The degree points of `V_n` over `m` are the points of the exact-degree scheme `D_n`
over `m`. -/
def degreePointsEquiv (κ : Type u) [Field κ] (m : Spec (CommRingCat.of κ) ⟶ M) (n : ℕ) :
    {d : Spec (CommRingCat.of κ) ⟶ c.E.tupleSymmetricDegreeScheme n //
      d ≫ c.E.tupleSymmetricDegreeι n ≫ c.p g n = m} ≃ c.degreePoints g κ m n where
  toFun d := ⟨d.1 ≫ c.E.tupleSymmetricDegreeι n,
    c.E.tupleSymmetricDegreeι_not_mem_threshold n _, by rw [Category.assoc]; exact d.2⟩
  invFun v := ⟨IsClosedImmersion.lift (c.E.tupleSymmetricDegreeι n) v.1 (by
      change (Scheme.IdealSheafData.vanishingIdeal
        (c.E.tupleSymmetricDegreeClosed n)).subschemeι.ker ≤ _
      rw [Scheme.IdealSheafData.ker_subschemeι]
      refine (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker _).2 v.1 ?_
      rintro _ ⟨x, rfl⟩
      have hx : x = IsLocalRing.closedPoint κ := Subsingleton.elim _ _
      subst hx
      exact v.2.1), by
    rw [IsClosedImmersion.lift_fac_assoc]; exact v.2.2⟩
  left_inv d := Subtype.ext (by
    rw [← cancel_mono (c.E.tupleSymmetricDegreeι n), IsClosedImmersion.lift_fac])
  right_inv v := Subtype.ext (IsClosedImmersion.lift_fac _ _ _)

/-- The number of `κ`-points of `X` over `m` is the sum over `n` below the tuple-length
bound of the numbers of `κ`-points of `D_n` over `m`, when these are finite. -/
theorem card_fibrePoints (κ : Type u) [Field κ] [Finite κ] (m : Spec (CommRingCat.of κ) ⟶ M)
    (hfin : ∀ n, Finite (Spec (CommRingCat.of κ) ⟶ c.E.tupleSymmetricScheme n)) :
    Nat.card (c.fibrePoints g κ m) = ∑ n : Fin c.N,
      Nat.card {d : Spec (CommRingCat.of κ) ⟶ c.E.tupleSymmetricDegreeScheme n //
        d ≫ c.E.tupleSymmetricDegreeι n ≫ c.p g n = m} := by
  have : ∀ n, Finite (c.degreePoints g κ m n) := fun n =>
    Finite.of_injective (fun v : c.degreePoints g κ m n => v.1) Subtype.val_injective
  rw [← Nat.card_congr (degreeFibreEquiv κ m), Nat.card_sigma]
  exact Finset.sum_congr rfl fun n _ => Nat.card_congr (degreePointsEquiv κ m n).symm

end SepChart

end Langlands.AlgebraicGeometry.LangWeil.SpaceFamily
