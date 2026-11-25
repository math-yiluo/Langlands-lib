/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology
public import WeilConjectures.EtaleCohomology.Purity.Smooth.CartierKummerClass
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.OpenClosed.Conservative
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Local

/-!
# The purity hypothesis is local

The purity hypothesis `AlgebraicGeometry.Etale.SupportedTatePure` for a closed immersion
`i : Z ⟶ X` asks that `Ri_! Ri^! (Λ_X(c)[2c])` be a sheaf placed in degree zero. We show:

* it holds as soon as `Ri^! (Λ_X(c)[2c])` is isomorphic to a complex concentrated in degree zero,
  for instance to `Λ_Z` (`AlgebraicGeometry.Etale.supportedTatePure_of_iso_constantComplex`), as
  `Ri_! = i_*` is exact;
* it can be checked on open subschemes covering `Z`
  (`AlgebraicGeometry.Etale.SupportedTatePure.of_isOpenImmersion_cover`): it amounts to the
  vanishing of the cohomology sheaves in nonzero degrees, which is local, and the object vanishes
  on the complement of `Z`.

Together with the stability under étale base change
(`AlgebraicGeometry.Etale.SupportedTatePure.of_etale`), which covers isomorphisms, this lets one
transport the hypothesis along local models.
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- An object of `D(X_ét, Λ)` vanishes if its derived pullbacks along a jointly surjective
family vanish. -/
theorem isZero_of_isZero_leftDerivedUpperStar_of_jointlySurjective (Λ : Type (u + 1))
    [CommRing Λ] {X : Scheme.{u}} {ι : Type u} {U : ι → Scheme.{u}} (a : ∀ i, U i ⟶ X)
    (ha : ∀ x : X, ∃ (i : ι) (y : U i), (a i).base y = x)
    {M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h : ∀ i, IsZero ((L((a i)^*[ModuleCat.{u + 1} Λ])).obj M)) : IsZero M := by
  have : IsIso (0 : M ⟶ 0) := isIso_of_isIso_leftDerivedUpperStar_map_of_jointlySurjective Λ a ha _
    fun i ↦ isIso_of_source_target_iso_zero _ (h i).isoZero
      (Functor.map_isZero _ (isZero_zero _)).isoZero
  exact (isZero_zero _).of_iso (asIso (0 : M ⟶ 0))

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Z : Scheme.{u}} [HasTateTwist Λ]

/-- The constant complex `Λ_X` is concentrated in degree `0`. -/
instance isGE_constantComplex : (constantComplex Λ X).IsGE 0 :=
  (_root_.DerivedCategory.isGE_iff _ 0).2 fun n hn ↦ isZero_homology_constantComplex Λ X n hn.ne

/-- The constant complex `Λ_X` is concentrated in degree `0`. -/
instance isLE_constantComplex : (constantComplex Λ X).IsLE 0 :=
  (_root_.DerivedCategory.isLE_iff _ 0).2 fun n hn ↦ isZero_homology_constantComplex Λ X n hn.ne'

/-- **Purity from a computation of `Ri^!`.** If `Ri^! (Λ_X(c)[2c])` is isomorphic to a complex
concentrated in degree zero, then the purity hypothesis holds for `i`: `Ri_! = i_*` is exact. -/
theorem supportedTatePure_of_iso (c : ℕ) (i : Z ⟶ X) [IsClosedImmersion i]
    [HasInvertibleExponent Λ X] (K : DerivedCategory (Sheaf Z.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))) [K.IsGE 0] [K.IsLE 0]
    (e : (R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧) ≅ K) :
    SupportedTatePure Λ c i := by
  have := Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom Λ i
  obtain ⟨e₀⟩ := nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar
    (ModuleCat.{u + 1} Λ) i
  have : (((i)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K).IsGE 0 :=
    ((i)_*[ModuleCat.{u + 1} Λ]).isGE_mapDerivedCategory_obj K 0
  have : (((i)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K).IsLE 0 :=
    ((i)_*[ModuleCat.{u + 1} Λ]).isLE_mapDerivedCategory_obj K 0
  obtain ⟨G, ⟨e'⟩⟩ := _root_.DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (((i)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K) 0
  exact ⟨G, ⟨(R(i)_![ModuleCat.{u + 1} Λ]).mapIso e ≪≫ e₀.app K ≪≫
    ((i)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorIsoMapDerivedCategory.app K ≪≫ e'⟩⟩

/-- **Purity from a fundamental class.** If `Ri^! (Λ_X(c)[2c]) ≅ Λ_Z`, the purity hypothesis
holds for `i`. -/
theorem supportedTatePure_of_iso_constantComplex (c : ℕ) (i : Z ⟶ X) [IsClosedImmersion i]
    [HasInvertibleExponent Λ X]
    (e : (R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧) ≅ constantComplex Λ Z) :
    SupportedTatePure Λ c i :=
  supportedTatePure_of_iso Λ c i _ e

/-- The purity hypothesis in terms of cohomology sheaves: it holds if and only if the cohomology
sheaves of `Ri_! Ri^! (Λ_X(c)[2c])` vanish in nonzero degrees. -/
theorem supportedTatePure_iff_isZero_homology (c : ℕ) (i : Z ⟶ X) [IsClosedImmersion i]
    [HasInvertibleExponent Λ X] :
    SupportedTatePure Λ c i ↔ ∀ n : ℤ, n ≠ 0 →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
        ((R(i)_![ModuleCat.{u + 1} Λ]).obj
          ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)))) := by
  constructor
  · rintro ⟨G, ⟨e⟩⟩ n hn
    exact _root_.DerivedCategory.isZero_homologyFunctor_obj_of_iso_singleFunctor e hn
  · intro h
    set K := (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))
    have : K.IsGE 0 := (_root_.DerivedCategory.isGE_iff K 0).2 fun n hn ↦ h n hn.ne
    have : K.IsLE 0 := (_root_.DerivedCategory.isLE_iff K 0).2 fun n hn ↦ h n hn.ne'
    exact _root_.DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K 0

variable {Λ} in
/-- **The purity hypothesis is local.** Let `e_a : U_a ⟶ X` be open immersions whose images
cover `Z`, and `i_a : Z_a ⟶ U_a` the base changes of `i`. If the purity hypothesis holds for
every `i_a`, it holds for `i`. Indeed the cohomology sheaves of `Ri_! Ri^! (Λ_X(c)[2c])` in
nonzero degrees vanish on every `U_a`, where this object restricts to
`Ri_a! Ri_a^! (Λ_{U_a}(c)[2c])`
(`AlgebraicGeometry.Etale.isIso_supportedRestriction_of_isOpenImmersion`),
and on the complement of `Z`, where it vanishes. -/
theorem SupportedTatePure.of_isOpenImmersion_cover {c : ℕ} {i : Z ⟶ X} [IsClosedImmersion i]
    [HasInvertibleExponent Λ X] {ι : Type u} {U Z' : ι → Scheme.{u}} (e : ∀ a, U a ⟶ X)
    [∀ a, IsOpenImmersion (e a)] [∀ a, HasInvertibleExponent Λ (U a)] (i' : ∀ a, Z' a ⟶ U a)
    [∀ a, IsClosedImmersion (i' a)] (g : ∀ a, Z' a ⟶ Z) (hg : ∀ a, IsPullback (g a) (i' a) i (e a))
    (hcov : Set.range i.base ⊆ ⋃ a, Set.range (e a).base)
    (h : ∀ a, SupportedTatePure Λ c (i' a)) : SupportedTatePure Λ c i := by
  rw [supportedTatePure_iff_isZero_homology]
  intro n hn
  set K := (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))
  have hK (V : Scheme.{u}) (f : V ⟶ X)
      (hf : IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K))) :
      IsZero (((f)^*[ModuleCat.{u + 1} Λ]).obj
        ((_root_.DerivedCategory.homologyFunctor _ n).obj K)) :=
    hf.of_iso ((((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso n).app K ≪≫
      (_root_.DerivedCategory.homologyFunctor _ n).mapIso
        ((leftDerivedUpperStarIsoMapDerivedCategory _ f).app K).symm)
  let V : Option ι → Scheme.{u} := fun o ↦ o.elim i.openComplement.toScheme U
  let a : ∀ o, V o ⟶ X := fun o ↦ match o with
    | none => i.openComplement.ι
    | some b => e b
  have : IsIso (0 : (_root_.DerivedCategory.homologyFunctor _ n).obj K ⟶ 0) := by
    refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ) a ?_ _
      fun o ↦ isIso_of_source_target_iso_zero _ (IsZero.isoZero ?_)
        (Functor.map_isZero _ (isZero_zero _)).isoZero
    · intro x
      by_cases hx : x ∈ Set.range i.base
      · obtain ⟨b, y, hy⟩ := Set.mem_iUnion.1 (hcov hx)
        exact ⟨some b, y, hy⟩
      · rw [i.range_eq_compl_range_openComplement_ι, Set.mem_compl_iff, not_not] at hx
        obtain ⟨y, hy⟩ := hx
        exact ⟨none, y, hy⟩
    · rcases o with _ | b
      · refine hK _ _ (Functor.map_isZero _ ?_)
        exact isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint _ i
          i.openComplement.ι
          (by rw [i.range_eq_compl_range_openComplement_ι]; exact disjoint_compl_left) _ le_rfl _
      · refine hK _ _ ?_
        obtain ⟨G, ⟨eG⟩⟩ := h b
        have := isIso_supportedRestriction_of_isOpenImmersion Λ (e b) i (i' b) (g b) (hg b) _ _
          (leftDerivedUpperStarTateShiftIso Λ (e b) c)
        exact _root_.DerivedCategory.isZero_homologyFunctor_obj_of_iso_singleFunctor
          (asIso (supportedRestriction Λ (e b) i (i' b) (g b) (hg b) _ _
            (leftDerivedUpperStarTateShiftIso Λ (e b) c)) ≪≫ eG) hn
  exact (isZero_zero _).of_iso (asIso (0 : (_root_.DerivedCategory.homologyFunctor _ n).obj K ⟶ 0))

end Etale

end AlgebraicGeometry
