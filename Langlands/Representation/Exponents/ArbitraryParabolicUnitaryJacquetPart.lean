import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Plancherel.SplitTorusRealPart
import Langlands.Representation.SubrepresentationLattice
import Langlands.Representation.Category.Subquotients

/-! # Unitary and nonunitary parts of a normalized Jacquet module

Renard 2026, VII.2.3 (printed p.229/PDF p.235): the normalized Jacquet module `r_P^G V`
contains `(r_P^G V)_0`, the sum of the characteristic spaces of the split component for
the exponents with zero real part, and `(r_P^G V)_+`, the sum for the exponents with
nonzero real part. The real part is the published normalized `q^(-s)` parameter. Both
parts are also transported to smooth representations of `M(F)` itself.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance unitaryPartAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

section Parts

/-- Renard's `(r_P^G V)_0`: the sum of the normalized Jacquet weight spaces of the
exponents whose normalized real part vanishes. -/
def unitaryJacquetPart :
    Subrepresentation ((jacquetFunctor p l r hp hr hl hmul).obj π).representation :=
  ⨆ (χ : rationalPoints A.toGrp →* ℂˣ)
    (_ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ)
    (_ : Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ = 0),
    normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ

/-- Renard's `(r_P^G V)_+`: the sum of the normalized Jacquet weight spaces of the
exponents whose normalized real part is nonzero. -/
def nonunitaryJacquetPart :
    Subrepresentation ((jacquetFunctor p l r hp hr hl hmul).obj π).representation :=
  ⨆ (χ : rationalPoints A.toGrp →* ℂˣ)
    (_ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ)
    (_ : Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ≠ 0),
    normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- A character that is not an exponent has zero weight space. -/
theorem normalizedJacquetWeightSpace_eq_bot_of_not_isNormalizedJacquetExponent
    {χ : rationalPoints A.toGrp →* ℂˣ}
    (hχ : ¬ IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ) :
    normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ = ⊥ := by
  by_contra hne
  exact hχ ((isNormalizedJacquetExponent_iff p l r hp hl hr hmul ha π χ).mpr
    ((normalizedJacquetWeightSpace_ne_bot_iff p l r hp hl hr hmul ha π χ).mp hne))

/-- The weight space of an exponent with zero real part lies in the unitary part. -/
theorem normalizedJacquetWeightSpace_le_unitaryJacquetPart
    {χ : rationalPoints A.toGrp →* ℂˣ}
    (hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ)
    (h0 : Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ = 0) :
    normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ ≤
      unitaryJacquetPart p l r hp hl hr hmul ha π :=
  le_iSup₂_of_le (f := fun χ (_ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ) =>
    ⨆ (_ : Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ = 0),
      normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ) χ hχ (le_iSup_of_le h0 le_rfl)

/-- The weight space of an exponent with nonzero real part lies in the nonunitary part. -/
theorem normalizedJacquetWeightSpace_le_nonunitaryJacquetPart
    {χ : rationalPoints A.toGrp →* ℂˣ}
    (hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ)
    (h0 : Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ≠ 0) :
    normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ ≤
      nonunitaryJacquetPart p l r hp hl hr hmul ha π :=
  le_iSup₂_of_le (f := fun χ (_ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ) =>
    ⨆ (_ : Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ≠ 0),
      normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ) χ hχ (le_iSup_of_le h0 le_rfl)

/-- The exponent condition is redundant: the unitary part is the sum of all weight
spaces of characters with zero normalized real part. -/
theorem unitaryJacquetPart_eq_iSup :
    unitaryJacquetPart p l r hp hl hr hmul ha π =
      ⨆ (χ : rationalPoints A.toGrp →* ℂˣ)
        (_ : Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ = 0),
        normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ := by
  apply le_antisymm
  · exact iSup_le fun χ => iSup_le fun _ => iSup_le fun h0 => le_iSup₂_of_le χ h0 le_rfl
  · refine iSup_le fun χ => iSup_le fun h0 => ?_
    by_cases hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ
    · exact normalizedJacquetWeightSpace_le_unitaryJacquetPart p l r hp hl hr hmul ha π hχ h0
    · rw [normalizedJacquetWeightSpace_eq_bot_of_not_isNormalizedJacquetExponent
        p l r hp hl hr hmul ha π hχ]
      exact bot_le

/-- The exponent condition is redundant for the nonunitary part as well. -/
theorem nonunitaryJacquetPart_eq_iSup :
    nonunitaryJacquetPart p l r hp hl hr hmul ha π =
      ⨆ (χ : rationalPoints A.toGrp →* ℂˣ)
        (_ : Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ≠ 0),
        normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ := by
  apply le_antisymm
  · exact iSup_le fun χ => iSup_le fun _ => iSup_le fun h0 => le_iSup₂_of_le χ h0 le_rfl
  · refine iSup_le fun χ => iSup_le fun h0 => ?_
    by_cases hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ
    · exact normalizedJacquetWeightSpace_le_nonunitaryJacquetPart p l r hp hl hr hmul ha π hχ h0
    · rw [normalizedJacquetWeightSpace_eq_bot_of_not_isNormalizedJacquetExponent
        p l r hp hl hr hmul ha π hχ]
      exact bot_le

/-- The underlying submodule of the unitary part is the submodule sum over the same
exponents. -/
theorem unitaryJacquetPart_toSubmodule :
    (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule =
      ⨆ (χ : rationalPoints A.toGrp →* ℂˣ)
        (_ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ)
        (_ : Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ = 0),
        (normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ).toSubmodule := by
  simp only [unitaryJacquetPart, Langlands.Subrepresentation.toSubmodule_iSup]

/-- The underlying submodule of the nonunitary part is the submodule sum over the same
exponents. -/
theorem nonunitaryJacquetPart_toSubmodule :
    (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule =
      ⨆ (χ : rationalPoints A.toGrp →* ℂˣ)
        (_ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ)
        (_ : Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ≠ 0),
        (normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ).toSubmodule := by
  simp only [nonunitaryJacquetPart, Langlands.Subrepresentation.toSubmodule_iSup]

end Parts

section Levi

/-- `(r_P^G π)_0` as a smooth representation of `M(F)`: the actual subrepresentation of
the Jacquet module, pulled back along the Levi-point isomorphism. -/
def leviUnitaryJacquetModule :
    letI := leviPointTopology l hl
    SmoothRep.{0, u, v} ℂ (rationalPoints M) :=
  letI := leviPointTopology l hl
  SmoothRep.pullback (leviPointsEquiv p l hp hl)
    (SmoothRep.subrepresentation ((jacquetFunctor p l r hp hr hl hmul).obj π)
      (unitaryJacquetPart p l r hp hl hr hmul ha π))

/-- `(r_P^G π)_+` as a smooth representation of `M(F)`. -/
def leviNonunitaryJacquetModule :
    letI := leviPointTopology l hl
    SmoothRep.{0, u, v} ℂ (rationalPoints M) :=
  letI := leviPointTopology l hl
  SmoothRep.pullback (leviPointsEquiv p l hp hl)
    (SmoothRep.subrepresentation ((jacquetFunctor p l r hp hr hl hmul).obj π)
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π))

/-- The inclusion of `(r_P^G π)_0` into the transported Jacquet module `r_P^G π` of
`M(F)`. -/
def leviUnitaryJacquetModuleι :
    letI := leviPointTopology l hl
    leviUnitaryJacquetModule p l r hp hl hr hmul ha π ⟶
      (leviJacquetFunctor p l r hp hr hl hmul).obj π :=
  letI := leviPointTopology l hl
  (SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl)).map
    (SmoothRep.subtype ((jacquetFunctor p l r hp hr hl hmul).obj π)
      (unitaryJacquetPart p l r hp hl hr hmul ha π))

/-- The inclusion of `(r_P^G π)_+` into the transported Jacquet module `r_P^G π` of
`M(F)`. -/
def leviNonunitaryJacquetModuleι :
    letI := leviPointTopology l hl
    leviNonunitaryJacquetModule p l r hp hl hr hmul ha π ⟶
      (leviJacquetFunctor p l r hp hr hl hmul).obj π :=
  letI := leviPointTopology l hl
  (SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl)).map
    (SmoothRep.subtype ((jacquetFunctor p l r hp hr hl hmul).obj π)
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π))

/-- The inclusion is the actual submodule inclusion. -/
theorem leviUnitaryJacquetModuleι_injective :
    letI := leviPointTopology l hl
    Function.Injective (SmoothRep.hom (leviUnitaryJacquetModuleι p l r hp hl hr hmul ha π)) :=
  Submodule.injective_subtype _

/-- The inclusion is the actual submodule inclusion. -/
theorem leviNonunitaryJacquetModuleι_injective :
    letI := leviPointTopology l hl
    Function.Injective (SmoothRep.hom (leviNonunitaryJacquetModuleι p l r hp hl hr hmul ha π)) :=
  Submodule.injective_subtype _

/-- A Levi point acts on `(r_P^G π)_0` through its image in `G(F)`. -/
theorem leviUnitaryJacquetModule_representation (m : rationalPoints M) :
    letI := leviPointTopology l hl
    (leviUnitaryJacquetModule p l r hp hl hr hmul ha π).representation m =
      (SmoothRep.subrepresentation ((jacquetFunctor p l r hp hr hl hmul).obj π)
        (unitaryJacquetPart p l r hp hl hr hmul ha π)).representation
          (leviPointsEquiv p l hp hl m) :=
  rfl

/-- A Levi point acts on `(r_P^G π)_+` through its image in `G(F)`. -/
theorem leviNonunitaryJacquetModule_representation (m : rationalPoints M) :
    letI := leviPointTopology l hl
    (leviNonunitaryJacquetModule p l r hp hl hr hmul ha π).representation m =
      (SmoothRep.subrepresentation ((jacquetFunctor p l r hp hr hl hmul).obj π)
        (nonunitaryJacquetPart p l r hp hl hr hmul ha π)).representation
          (leviPointsEquiv p l hp hl m) :=
  rfl

end Levi

end Langlands.Aubert.General.RepresentedParabolic
