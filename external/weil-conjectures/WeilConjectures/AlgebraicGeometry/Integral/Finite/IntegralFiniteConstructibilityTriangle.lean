/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Finite.IntegralFiniteResidueNormalization
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.FiniteConstructibilityLocalTriangle
public import WeilConjectures.AlgebraicGeometry.FiniteConstructibilityOuterLocalTransfer
public import WeilConjectures.AlgebraicGeometry.FiniteConstructibilityOuterTransfer

/-! # Finite constructibility through one quotient-linear triangle -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Finite constant local models in every degree on one fixed stratum.
This generic predicate keeps the coefficient ring explicit in changes of presentation. -/
def finiteLocalModelsOnStratum
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (S : Scheme.Stratification X) (i : Fin S.n)
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) : Prop :=
  ∀ q : ℤ, HasFiniteConstantLocalModel Λ (S.domain i)
    ((CondensedRing.upperStar Λ (S.immersion i)).obj
      ((DerivedCategory.homologyFunctor _ q).obj L))

private theorem scalarFiniteLocalModelsOnStratum_iff
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (S : Scheme.Stratification X) (i : Fin S.n)
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    scalarFiniteLocalModelsOnStratum Λ X S i L ↔
      finiteLocalModelsOnStratum Λ X S i L := Iff.rfl

/-- All homology sheaves have finite constant local models on this specified stratum.
This is the generic predicate at the actual positive finite coefficient quotient. -/
def integralFiniteLocalOnStratum
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (n : ℕ) (S : Scheme.Stratification X) (i : Fin S.n)
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.finiteRing l E X n))) : Prop :=
  finiteLocalModelsOnStratum (DerivedNakayama.quotientRing l E (n + 1)) X S i L

/-- Constructibility and fixed-stratum finite local models pass through one finite
quotient-linear distinguished triangle. -/
theorem integral_finite_constructibility_triangle
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (n : ℕ)
    (L₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.finiteRing l E X 0)))
    (Lₙ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.finiteRing l E X n)))
    (Δ : CategoryTheory.Pretriangulated.Triangle
      (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (AdicCompletion.finiteRing l E X (n + 1)))))
    (hΔ : Δ ∈ distTriang _)
    (e₀ : Δ.obj₁ ≅
      (Mod.comap (integralResidueTransition l E X (n + 1))).mapDerivedCategory.obj L₀)
    (eₙ : Δ.obj₃ ≅
      (Mod.comap (AdicCompletion.transition l E X n)).mapDerivedCategory.obj Lₙ)
    (h₀ : constantModelBoundedConstructible
      (DerivedNakayama.quotientRing l E 1) X L₀)
    (hₙ : constantModelBoundedConstructible
      (DerivedNakayama.quotientRing l E (n + 1)) X Lₙ) :
    constantModelBoundedConstructible
      (DerivedNakayama.quotientRing l E (n + 1 + 1)) X Δ.obj₂ ∧
    (∀ (S : Scheme.Stratification X) (i : Fin S.n),
      integralFiniteLocalOnStratum l E X 0 S i L₀ →
      integralFiniteLocalOnStratum l E X n S i Lₙ →
      integralFiniteLocalOnStratum l E X (n + 1) S i Δ.obj₂) := by
  constructor
  · exact finite_constructibility_outer_transfer l E X n L₀ Lₙ Δ hΔ e₀ eₙ h₀ hₙ
  · intro S i hS₀ hSₙ
    obtain ⟨h₁, h₃⟩ :=
      finite_constructibility_outer_local_transfer l E X n L₀ Lₙ Δ e₀ eₙ S i
    apply (scalarFiniteLocalModelsOnStratum_iff _ X S i Δ.obj₂).mp
    apply finite_constructibility_local_triangle l E X (n + 1) S i Δ hΔ
    · exact h₁ ((scalarFiniteLocalModelsOnStratum_iff _ X S i L₀).mpr hS₀)
    · exact h₃ ((scalarFiniteLocalModelsOnStratum_iff _ X S i Lₙ).mpr hSₙ)

end AlgebraicGeometry.ProEtale
