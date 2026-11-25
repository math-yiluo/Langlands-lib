/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.AlgebraicGeometry.RestrictionOfScalarsExact
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Normalized DVR towers

Source: Weil conjectures blueprint, `chap-The-six-operations-on-Dbctf`,
`sk-prop-sf-biduality-general`, node `def-coef-normalized-dvr-tower`, order 2131
(blueprint: def-coef-normalized-dvr-tower).

## Main definitions

- `normalizedDVRQuotient`: the actual quotient map of the coefficient system.
- `normalizedDVRRes` and `normalizedDVRResCompleted`: exact derived scalar restriction.
- `NormalizedDVRTower`: finite-level objects and transitions with a coherent derived tower.

Normalization uses the universal property of derived change of rings: composition
with the specified transition is a Hom bijection. Under the tensor-restriction
adjunction this says exactly that the adjoint of that transition is an isomorphism.
It neither chooses an unrelated map nor adds an arbitrary scalar-extension functor.
All module universes are `max u (t+1)`, retaining the small site's independent sizes.
-/

@[expose] public section

set_option autoImplicit false

universe d t u uC vC r s

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

/-- Scalar restriction composes by the identity on every underlying section.
This general helper avoids unfolding finite coefficient rings to identify the two actions.
Source: blueprint order 2131, canonical successive restriction
(blueprint: def-coef-normalized-dvr-tower). -/
noncomputable def normalizedDVRRestrictionCompIso
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{r}} (f : R ⟶ S) (g : S ⟶ T) :
    SheafOfModules.restrictScalars.{s} g ⋙ SheafOfModules.restrictScalars.{s} f ≅
      SheafOfModules.restrictScalars.{s} (f ≫ g) := Iso.refl _

private theorem normalizedDVRRestrictionExact
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (f : R ⟶ S)
    [HasSheafify J AddCommGrpCat.{s}] [J.WEqualsLocallyBijective AddCommGrpCat.{s}] :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{s} f) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{s} f) := by
  let U := SheafOfModules.toSheaf.{s} R
  have : PreservesFiniteLimits (SheafOfModules.restrictScalars.{s} f ⋙ U) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{s} S))
  have : PreservesFiniteColimits (SheafOfModules.restrictScalars.{s} f ⋙ U) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{s} S))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ U,
    preservesFiniteColimits_of_reflects_of_preserves _ U⟩

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})

/-- The quotient `B_(m+1) → B_(n+1)`, obtained from the actual inverse system.
Source: blueprint order 2131 (blueprint: def-coef-normalized-dvr-tower). -/
noncomputable def normalizedDVRQuotient {m n : ℕ} (h : n ≤ m) :
    integralCoefficientSheaf l E X m ⟶ integralCoefficientSheaf l E X n :=
  (integralCoefficientSheafSystem l E X).map (homOfLE h).op

/-- The finite-level module category, with the recorded coefficient sheaf and size.
Source: blueprint order 2131 (blueprint: def-coef-normalized-dvr-tower). -/
abbrev normalizedDVRModules (n : ℕ) :=
  scalarReductionTarget l E X n

/-- The standard localization of finite-level module complexes.
Source: blueprint order 2131 (blueprint: def-coef-normalized-dvr-tower). -/
@[reducible]
noncomputable def normalizedDVRDerived (n : ℕ) :=
  @DerivedCategory (normalizedDVRModules l E X n) _ _ (HasDerivedCategory.standard _)

/-- Restriction along the actual quotient, on module sheaves.
Source: blueprint order 2131 (blueprint: def-coef-normalized-dvr-tower). -/
@[reducible]
noncomputable def normalizedDVRModuleRes {m n : ℕ} (h : n ≤ m) :
    scalarReductionTarget l E X n ⥤ scalarReductionTarget l E X m :=
  SheafOfModules.restrictScalars (normalizedDVRQuotient l E X h)

/-- Additivity of scalar restriction along a finite quotient.
Source: blueprint order 2131 (blueprint: def-coef-normalized-dvr-tower). -/
instance normalizedDVRModuleRes_additive {m n : ℕ} (h : n ≤ m) :
    (normalizedDVRModuleRes l E X h).Additive := by
  unfold normalizedDVRModuleRes
  infer_instance

/-- Exactness of finite-level restriction, asserted in the definition's second paragraph.
Source: blueprint order 2131; Stacks Tag 03DA
(blueprint: def-coef-normalized-dvr-tower).
Proof: restriction leaves the underlying abelian sheaf and every underlying map unchanged.
Kernels are sectionwise kernels with the restricted scalar action. Cokernels are the
sheafifications of sectionwise cokernels, with that same restricted action. Thus the
kernel and cokernel comparisons are identities on underlying sheaves. The functor is
additive, so it preserves all finite limits and finite colimits. This also applies to
identity quotients and to the empty scheme; no flatness is required. -/
theorem normalizedDVRModuleRes_exact {m n : ℕ} (h : n ≤ m) :
    PreservesFiniteLimits (normalizedDVRModuleRes l E X h) ∧
      PreservesFiniteColimits (normalizedDVRModuleRes l E X h) := by
  exact normalizedDVRRestrictionExact (normalizedDVRQuotient l E X h)

/-- The finite-limit part of exact scalar restriction.
Source: blueprint order 2131 (blueprint: def-coef-normalized-dvr-tower). -/
noncomputable instance normalizedDVRModuleRes_limits {m n : ℕ} (h : n ≤ m) :
    PreservesFiniteLimits (normalizedDVRModuleRes l E X h) :=
  (normalizedDVRModuleRes_exact l E X h).1

/-- The finite-colimit part of exact scalar restriction.
Source: blueprint order 2131 (blueprint: def-coef-normalized-dvr-tower). -/
noncomputable instance normalizedDVRModuleRes_colimits {m n : ℕ} (h : n ≤ m) :
    PreservesFiniteColimits (normalizedDVRModuleRes l E X h) :=
  (normalizedDVRModuleRes_exact l E X h).2

/-- Termwise restriction descended through the actual derived localization.
Source: blueprint order 2131 (blueprint: def-coef-normalized-dvr-tower). -/
@[reducible]
noncomputable def normalizedDVRRes {m n : ℕ} (h : n ≤ m) :
    normalizedDVRDerived l E X n ⥤ normalizedDVRDerived l E X m :=
  letI := HasDerivedCategory.standard (normalizedDVRModules l E X n)
  letI := HasDerivedCategory.standard (normalizedDVRModules l E X m)
  (normalizedDVRModuleRes l E X h).mapDerivedCategory

variable (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/-- Restriction along the completion projection, descended termwise to derived categories.
Source: blueprint order 2131 (blueprint: def-coef-normalized-dvr-tower). -/
@[reducible]
noncomputable def normalizedDVRResCompleted (n : ℕ) :
    normalizedDVRDerived l E X n ⥤ completedIntegralDerivedCategory l E X D hl :=
  letI := HasDerivedCategory.standard (normalizedDVRModules l E X n)
  letI := HasDerivedCategory.standard (completedIntegralModuleSheaves l E X D hl)
  letI := (completedIntegralRestrictScalars_exact l E X D hl n).1
  letI := (completedIntegralRestrictScalars_exact l E X D hl n).2
  letI : (completedIntegralRestrictScalars l E X D hl n).Additive :=
    inferInstanceAs (SheafOfModules.restrictScalars.{max u (t + 1)}
      (completedIntegralCoefficientProjection l E X D hl n)).Additive
  (completedIntegralRestrictScalars l E X D hl n).mapDerivedCategory

/-- The canonical composition identification from the limit projection equation.
Source: blueprint order 2131 (blueprint: def-coef-normalized-dvr-tower). -/
noncomputable def normalizedDVRResCompletedComp {m n : ℕ} (h : n ≤ m) :
    normalizedDVRRes l E X h ⋙ normalizedDVRResCompleted l E X D hl m ≅
      normalizedDVRResCompleted l E X D hl n :=
  letI := HasDerivedCategory.standard (normalizedDVRModules l E X n)
  letI := HasDerivedCategory.standard (normalizedDVRModules l E X m)
  letI := HasDerivedCategory.standard (completedIntegralModuleSheaves l E X D hl)
  letI := (completedIntegralRestrictScalars_exact l E X D hl m).1
  letI := (completedIntegralRestrictScalars_exact l E X D hl m).2
  letI := (completedIntegralRestrictScalars_exact l E X D hl n).1
  letI := (completedIntegralRestrictScalars_exact l E X D hl n).2
  letI : (completedIntegralRestrictScalars l E X D hl m).Additive :=
    inferInstanceAs (SheafOfModules.restrictScalars.{max u (t + 1)}
      (completedIntegralCoefficientProjection l E X D hl m)).Additive
  letI : (completedIntegralRestrictScalars l E X D hl n).Additive :=
    inferInstanceAs (SheafOfModules.restrictScalars.{max u (t + 1)}
      (completedIntegralCoefficientProjection l E X D hl n)).Additive
  let e₀ : normalizedDVRModuleRes l E X h ⋙
      completedIntegralRestrictScalars l E X D hl m ≅
      SheafOfModules.restrictScalars.{max u (t + 1)}
        (completedIntegralCoefficientProjection l E X D hl m ≫
          normalizedDVRQuotient l E X h) :=
    normalizedDVRRestrictionCompIso (completedIntegralCoefficientProjection l E X D hl m)
      (normalizedDVRQuotient l E X h)
  let he : completedIntegralCoefficientProjection l E X D hl m ≫
      normalizedDVRQuotient l E X h = completedIntegralCoefficientProjection l E X D hl n :=
    limit.w (integralCoefficientSheafSystem l E X) (homOfLE h).op
  let e : normalizedDVRModuleRes l E X h ⋙
      completedIntegralRestrictScalars l E X D hl m ≅
      completedIntegralRestrictScalars l E X D hl n :=
    e₀ ≪≫ eqToIso (congrArg
      (fun f : completedIntegralCoefficientSheaf l E X D hl ⟶
          integralCoefficientSheaf l E X n ↦
        SheafOfModules.restrictScalars.{max u (t + 1)} f) he)
  Functor.mapDerivedCategoryCompIso (normalizedDVRModuleRes l E X h)
    (completedIntegralRestrictScalars l E X D hl m) ≪≫
      Functor.mapDerivedCategoryNatIso e

end WeilConjectures
