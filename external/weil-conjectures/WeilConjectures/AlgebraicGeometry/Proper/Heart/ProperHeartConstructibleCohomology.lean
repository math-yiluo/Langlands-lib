/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeRational
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralIndConstructibleHeartClosure

/-!
# Constructibility of proper higher direct images with rational coefficients
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private lemma constantModelBoundedConstructible_eq_rational
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) [IsCommMonObj Λ.X]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Λ = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (k : Type u) [Field k]
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))] :
    constantModelBoundedConstructible Λ.X T = boundedConstructible (condensedRingObj Λ.X T) := by
  rcases hΛ with ⟨E, hE⟩ | hQ
  · subst Λ
    exact constantModelBoundedConstructible_eq_boundedConstructible_subfield_of_finiteType k ℓ E T
  · subst Λ
    exact constantModelBoundedConstructible_eq_boundedConstructible_padicAlgCl_of_finiteType k ℓ T

attribute [local irreducible] Functor.rightDerivedFunctor

/-- Proper higher direct images of finite constant-model constructible rational modules
are again finite constant-model constructible, for finite extensions and the condensed
algebraic closure. -/
theorem properHeart_constructible_cohomology
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] :
    ∀ M, IsConstantModelConstructible Λ X M → ∀ q : ℤ, 0 ≤ q →
      IsConstantModelConstructible Λ Y ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  have hEq (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [IsSeparated (T ↘ Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
      [QuasiCompact (T ↘ Spec (.of k))] :
      constantModelBoundedConstructible Λ T = boundedConstructible (condensedRingObj Λ T) :=
    constantModelBoundedConstructible_eq_rational ℓ (Mon.mk Λ) hΛ k T
  have : Fact (ringChar k).Prime := ⟨by
    rw [ringChar.eq k p₀]
    exact (CharP.char_is_prime_or_zero k p₀).resolve_right hp₀.ne'⟩
  have : Fact (ringChar k ≠ ℓ) := ⟨by rw [ringChar.eq k p₀]; exact hpℓ⟩
  intro M hM q _
  have hK := constantModelConstructible_single Λ X M hM
  have hK' := (congrFun (hEq X) _).mp hK
  let XOver := Over.mk (X ↘ Spec (.of k))
  let YOver := Over.mk (Y ↘ Spec (.of k))
  have : LocallyOfFiniteType XOver.hom :=
    inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of k)))
  have : QuasiCompact XOver.hom := inferInstanceAs (QuasiCompact (X ↘ Spec (.of k)))
  have : IsSeparated XOver.hom := inferInstanceAs (IsSeparated (X ↘ Spec (.of k)))
  have : LocallyOfFiniteType YOver.hom :=
    inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of k)))
  have : QuasiCompact YOver.hom := inferInstanceAs (QuasiCompact (Y ↘ Spec (.of k)))
  have : IsSeparated YOver.hom := inferInstanceAs (IsSeparated (Y ↘ Spec (.of k)))
  let pOver : XOver ⟶ YOver := Over.homMk p
  have : IsProper pOver.left := inferInstanceAs (IsProper p)
  have hP := CondensedRing.properPushforward_boundedConstructible_rational ℓ
    (k := k) (X := XOver) (Y := YOver) pOver (Mon.mk Λ) hΛ _ hK'
  exact ((congrFun (hEq Y) _).mpr hP).2 q

end AlgebraicGeometry.ProEtale
