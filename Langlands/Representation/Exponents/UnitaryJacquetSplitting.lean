import Langlands.Representation.Exponents.ArbitraryParabolicUnitaryJacquetPart
import Langlands.Representation.Exponents.SplitComponentDecomposition
import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.LinearAlgebra.Projection

/-! # Splitting the normalized Jacquet weight spaces by their real parts

This is the algebraic direct-sum step in Renard 2026, VII.2.3. Disjointness
does not need admissibility. Spanning, and hence complementarity, follows
when the actual normalized Jacquet module is admissible.
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

local instance splittingAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

/-- Index the unitary part by the actual normalized Jacquet exponents. -/
theorem unitaryJacquetPart_toSubmodule_eq_iSup_exponents :
    (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule =
      ⨆ (χ : normalizedJacquetExponents p l r hp hl hr hmul ha π)
        (_ : Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ = 0),
        (normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ).toSubmodule := by
  rw [iSup_subtype]
  exact unitaryJacquetPart_toSubmodule p l r hp hl hr hmul ha π

/-- Index the nonunitary part by the actual normalized Jacquet exponents. -/
theorem nonunitaryJacquetPart_toSubmodule_eq_iSup_exponents :
    (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule =
      ⨆ (χ : normalizedJacquetExponents p l r hp hl hr hmul ha π)
        (_ : Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ≠ 0),
        (normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ).toSubmodule := by
  rw [iSup_subtype]
  exact nonunitaryJacquetPart_toSubmodule p l r hp hl hr hmul ha π

/-- The two parts have zero intersection for every smooth representation. -/
theorem unitaryJacquetPart_disjoint_nonunitaryJacquetPart :
    Disjoint (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule := by
  rw [unitaryJacquetPart_toSubmodule_eq_iSup_exponents,
    nonunitaryJacquetPart_toSubmodule_eq_iSup_exponents]
  have hi := normalizedJacquetWeightSpace_independent p l r hp hl hr hmul ha π
  exact hi.disjoint_biSup_biSup (Set.disjoint_left.mpr (fun _ h0 hn => hn h0))

/-- The sum of the two parts is exactly the span of all normalized Jacquet
characteristic spaces, without a spanning hypothesis. -/
theorem unitaryJacquetPart_sup_nonunitaryJacquetPart :
    (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule ⊔
        (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule =
      ⨆ χ : normalizedJacquetExponents p l r hp hl hr hmul ha π,
        (normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ).toSubmodule := by
  rw [unitaryJacquetPart_toSubmodule_eq_iSup_exponents,
    nonunitaryJacquetPart_toSubmodule_eq_iSup_exponents]
  exact (iSup_split
    (fun χ : normalizedJacquetExponents p l r hp hl hr hmul ha π =>
      (normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ).toSubmodule)
    (fun χ => Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ = 0)).symm

/-- Complementarity is equivalent to spanning by the normalized Jacquet
characteristic spaces. -/
theorem unitaryJacquetPart_isCompl_nonunitaryJacquetPart_iff :
    IsCompl (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule
        (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule ↔
      (⨆ χ : normalizedJacquetExponents p l r hp hl hr hmul ha π,
        (normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ).toSubmodule) = ⊤ := by
  rw [isCompl_iff, codisjoint_iff, unitaryJacquetPart_sup_nonunitaryJacquetPart]
  exact and_iff_right (unitaryJacquetPart_disjoint_nonunitaryJacquetPart
    p l r hp hl hr hmul ha π)

/-- Admissibility of the actual normalized Jacquet module supplies the
spanning needed for the direct-sum step of VII.2.3. -/
theorem unitaryJacquetPart_isCompl_nonunitaryJacquetPart_of_admissible
    (hJ : ((jacquetFunctor p l r hp hr hl hmul).obj π).IsAdmissible) :
    IsCompl (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule :=
  (unitaryJacquetPart_isCompl_nonunitaryJacquetPart_iff p l r hp hl hr hmul ha π).mpr
    (normalizedJacquetWeightSpace_decomposition_of_admissible
      p l r hp hl hr hmul ha π hJ).2

/-- The addition equivalence from the unitary and nonunitary parts to the
actual normalized Jacquet module, assuming its admissibility. -/
def unitaryJacquetProdEquivOfAdmissible
    (hJ : ((jacquetFunctor p l r hp hr hl hmul).obj π).IsAdmissible) :
    ((unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule ×
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule) ≃ₗ[ℂ]
        ((jacquetFunctor p l r hp hr hl hmul).obj π) :=
  Submodule.prodEquivOfIsCompl _ _
    (unitaryJacquetPart_isCompl_nonunitaryJacquetPart_of_admissible
      p l r hp hl hr hmul ha π hJ)

@[simp]
theorem unitaryJacquetProdEquivOfAdmissible_apply
    (hJ : ((jacquetFunctor p l r hp hr hl hmul).obj π).IsAdmissible)
    (x : (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule ×
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule) :
    unitaryJacquetProdEquivOfAdmissible p l r hp hl hr hmul ha π hJ x =
      (x.1 : ((jacquetFunctor p l r hp hr hl hmul).obj π)) + x.2 :=
  rfl

end Langlands.Aubert.General.RepresentedParabolic
