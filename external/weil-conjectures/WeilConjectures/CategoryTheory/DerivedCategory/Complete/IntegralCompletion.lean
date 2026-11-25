/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Completion
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# The derived completion at the integral stage

For a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` and a site `(C, J)`, this file specializes
the derived completion `DerivedCategory.derivedCompletion` to the coefficient ring `𝒪_E` and
its maximal ideal: the functor

```
  (-)^ : D(J, 𝒪_E) ⥤ D_comp(J, 𝒪_E),   K ↦ R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ),
```

left adjoint to the inclusion `DerivedCategoryDerivedCompleteIntegral.ι`. It is a triangulated
`𝒪_E`-linear functor. The operations of the integral stage are defined by applying an operation
of `D(J, 𝒪_E)` to derived complete objects and completing the result; the lemmas at the end of
the file compare such completed composites
(`DerivedCategoryDerivedCompleteIntegral.completionCompIso`).

## Main definitions

- `DerivedCategoryDerivedCompleteIntegral.completion`: the derived completion functor.
- `DerivedCategoryDerivedCompleteIntegral.completionAdjunction`: `(-)^ ⊣ ι`.
- `DerivedCategoryDerivedCompleteIntegral.completionCompIso`: for a triangulated functor `Φ`
  preserving the objects on which `ϖ` acts invertibly, `(Φ (ι K^))^ ≅ (Φ K)^`.
-/

@[expose] public section

universe w u

open CategoryTheory Category Limits Pretriangulated

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {R : Type (u + 1)} [CommRing R]

/-- If `ϖ` acts invertibly on `X` and `ϖ'` divides `ϖ`, then `ϖ'` acts invertibly on `X`. -/
lemma smulInvertible.of_dvd {ϖ ϖ' : R} (h : ϖ' ∣ ϖ)
    {X : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))} (hX : smulInvertible J ϖ X) :
    smulInvertible J ϖ' X := by
  obtain ⟨c, rfl⟩ := h
  have hX' : IsIso ((ϖ' • 𝟙 X) ≫ (c • 𝟙 X)) := by
    rw [Linear.smul_comp, id_comp, smul_smul]
    exact hX
  have hX'' : IsIso ((c • 𝟙 X) ≫ (ϖ' • 𝟙 X)) := by
    rw [Linear.smul_comp, id_comp, smul_smul, mul_comm]
    exact hX
  have : Mono (ϖ' • 𝟙 X) := mono_of_mono _ (c • 𝟙 X)
  have : Epi (ϖ' • 𝟙 X) := epi_of_epi (c • 𝟙 X) _
  exact isIso_of_mono_of_epi _

variable (J) in
/-- The objects of `D(J, R)` on which some element of the ideal `I` acts invertibly. For
`I = (ϖ)` these are the objects on which `ϖ` acts invertibly
(`DerivedCategory.idealInvertible_iff`), the objects killed by the derived completion. -/
def idealInvertible (I : Ideal R) :
    ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  fun X ↦ ∃ a ∈ I, smulInvertible J a X

lemma idealInvertible_iff {I : Ideal R} {ϖ : R} (hI : I = Ideal.span {ϖ})
    (X : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    idealInvertible J I X ↔ smulInvertible J ϖ X := by
  refine ⟨fun ⟨a, ha, hX⟩ ↦ hX.of_dvd ?_, fun hX ↦ ⟨ϖ, hI ▸ Ideal.mem_span_singleton_self ϖ, hX⟩⟩
  rw [hI, Ideal.mem_span_singleton] at ha
  exact ha

section CompIso

variable {C' : Type (u + 1)} [Category.{u} C'] [EssentiallySmall.{u + 1} C']
  {J' : GrothendieckTopology C'} {R' : Type (u + 1)} [CommRing R']
  (I : Ideal R) (h : ∃ ϖ ∈ nonZeroDivisors R, I = Ideal.span {ϖ})
  (I' : Ideal R') (h' : ∃ ϖ ∈ nonZeroDivisors R', I' = Ideal.span {ϖ})
  (Φ : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) ⥤
    DerivedCategory (Sheaf J' (ModuleCat.{u + 1} R'))) [Φ.CommShift ℤ] [Φ.IsTriangulated]
  (hΦ : ∀ X, idealInvertible J I X → idealInvertible J' I' (Φ.obj X))

include hΦ in
/-- A triangulated functor `Φ` carrying the objects on which `I` acts invertibly to objects on
which `I'` acts invertibly is inverted, after completion, at the unit `K ⟶ K^`. -/
lemma isIso_derivedCompletion_map_map_unit_app
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    IsIso ((derivedCompletion J' I' h').map
      (Φ.map ((derivedCompletionAdjunction J I h).unit.app K))) := by
  obtain ⟨X, g, h₃, hT, hX⟩ := exists_distinguished_derivedCompletionAdjunction_unit_app h K
  have hX' := hΦ X ((idealInvertible_iff h.choose_spec.2 X).2 hX)
  exact isIso_derivedCompletion_map h' h'.choose_spec.2 (Φ.map_distinguished _ hT)
    ((idealInvertible_iff h'.choose_spec.2 _).1 hX')

/-- For a triangulated functor `Φ` carrying the objects on which `I` acts invertibly to objects
on which `I'` acts invertibly, completing `Φ` after completing its argument is completing `Φ`:
`(Φ (K^))^ ≅ (Φ K)^`, through the unit `K ⟶ K^`. -/
noncomputable def derivedCompletionCompIso :
    derivedCompletion J I h ⋙ (derivedComplete J I).ι ⋙ Φ ⋙ derivedCompletion J' I' h' ≅
      Φ ⋙ derivedCompletion J' I' h' :=
  have : IsIso (Functor.whiskerRight (derivedCompletionAdjunction J I h).unit
      (Φ ⋙ derivedCompletion J' I' h')) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact isIso_derivedCompletion_map_map_unit_app I h I' h' Φ hΦ
  (asIso (Functor.whiskerRight (derivedCompletionAdjunction J I h).unit
    (Φ ⋙ derivedCompletion J' I' h'))).symm

lemma derivedCompletionCompIso_inv_app (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    (derivedCompletionCompIso I h I' h' Φ hΦ).inv.app K =
      (derivedCompletion J' I' h').map
        (Φ.map ((derivedCompletionAdjunction J I h).unit.app K)) :=
  rfl

end CompIso

end DerivedCategory

section Integral

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) (l : ℕ) [Fact l.Prime] (E : Type w) [Field E]
  [Algebra E (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E] [Small.{u + 1} E]

namespace DerivedCategoryDerivedCompleteIntegral

noncomputable instance : (ι J l E).CommShift ℤ :=
  inferInstanceAs ((DerivedCategory.derivedCompleteIntegral J l E).ι.CommShift ℤ)

instance : (ι J l E).IsTriangulated :=
  inferInstanceAs ((DerivedCategory.derivedCompleteIntegral J l E).ι.IsTriangulated)

instance : (ι J l E).Linear (Shrink.{u + 1} (PadicAlgCl.integers l E)) :=
  inferInstanceAs ((DerivedCategory.derivedCompleteIntegral J l E).ι.Linear
    (Shrink.{u + 1} (PadicAlgCl.integers l E)))

instance : (ι J l E).Full := inferInstanceAs (DerivedCategory.derivedCompleteIntegral J l E).ι.Full

instance : (ι J l E).Faithful :=
  inferInstanceAs (DerivedCategory.derivedCompleteIntegral J l E).ι.Faithful

/-- The derived completion `K ↦ K^ = R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ)` of `D(J, 𝒪_E)` into
`D_comp(J, 𝒪_E)`, the specialization of `DerivedCategory.derivedCompletion` to the maximal ideal
of `𝒪_E`, generated by a uniformizer. -/
noncomputable def completion :
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))) ⥤
      DerivedCategoryDerivedCompleteIntegral J l E :=
  DerivedCategory.derivedCompletion J _
    (PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E)

/-- The derived completion is left adjoint to the inclusion of `D_comp(J, 𝒪_E)`. -/
noncomputable def completionAdjunction : completion J l E ⊣ ι J l E :=
  DerivedCategory.derivedCompletionAdjunction J _ _

noncomputable instance : (completion J l E).CommShift ℤ :=
  (completionAdjunction J l E).leftAdjointCommShift ℤ

instance : (completionAdjunction J l E).CommShift ℤ :=
  (completionAdjunction J l E).commShift_of_rightAdjoint ℤ

instance : (completion J l E).IsTriangulated :=
  (completionAdjunction J l E).isTriangulated_leftAdjoint

instance : (completion J l E).Linear (Shrink.{u + 1} (PadicAlgCl.integers l E)) :=
  (completionAdjunction J l E).left_adjoint_linear

instance : IsIso (completionAdjunction J l E).counit :=
  inferInstanceAs (IsIso (DerivedCategory.derivedCompletionAdjunction J _ _).counit)

end DerivedCategoryDerivedCompleteIntegral

end Integral
