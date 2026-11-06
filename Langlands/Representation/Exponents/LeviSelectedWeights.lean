import Langlands.Representation.Exponents.SelectedWeights
import Langlands.Representation.Exponents.ArbitraryParabolicUnitaryJacquetPart

/-! Selected weights on the actual Levi Jacquet module. -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance selectedLeviAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- Transport to the actual Levi points preserves each literal weight subspace.
Both sides retain the same uniform nilpotence power. -/
theorem leviJacquetWeightSpace_toSubmodule (χ : rationalPoints A.toGrp →* ℂˣ) :
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    (generalizedWeightSpace
      ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation
      (rationalPoints.map a) χ ha.isCentralSplitTorus.isCentral.map_mem_center).toSubmodule =
      (normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ).toSubmodule := by
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  change (generalizedWeightSpace
    (((jacquetFunctor p l r hp hr hl hmul).obj π).representation.comp
      (leviPointsEquiv p l hp hl).toMonoidHom)
    (rationalPoints.map a) χ ha.isCentralSplitTorus.isCentral.map_mem_center).toSubmodule = _
  ext x
  change x ∈ generalizedWeightSpace _ _ χ _ ↔
    x ∈ normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ
  exact (mem_generalizedWeightSpace_of_isSmooth (rationalPoints.map a) χ
    ha.isCentralSplitTorus.isCentral.map_mem_center
    ((leviJacquetFunctor p l r hp hr hl hmul).obj π).isSmooth x).trans
    (mem_normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ x).symm

/-- The zero-real-part selection on the actual Levi Jacquet action is exactly
the underlying subspace used by the published unitary Jacquet module. -/
theorem selectedWeightPart_leviJacquet_toSubmodule :
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    (selectedWeightPart
      ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation
      (rationalPoints.map a) ha.isCentralSplitTorus.isCentral.map_mem_center
      (fun χ => Plancherel.SplitTorus.normalizedRealPart
        ha.isCentralSplitTorus.1.1 χ = 0)).toSubmodule =
      (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule := by
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  rw [selectedWeightPart_toSubmodule, unitaryJacquetPart_eq_iSup]
  simp only [Langlands.Subrepresentation.toSubmodule_iSup,
    leviJacquetWeightSpace_toSubmodule p l r hp hl hr hmul ha π]
  rfl

/-- The identity on ambient vectors identifies the selected Levi Jacquet
representation with the published actual unitary Jacquet representation. -/
def selectedLeviJacquetEquivUnitary :
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    (selectedWeightPart
      ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation
      (rationalPoints.map a) ha.isCentralSplitTorus.isCentral.map_mem_center
      (fun χ => Plancherel.SplitTorus.normalizedRealPart
        ha.isCentralSplitTorus.1.1 χ = 0)).toRepresentation.Equiv
      (leviUnitaryJacquetModule p l r hp hl hr hmul ha π).representation := by
  letI := leviPointTopology l hl
  haveI := leviPoints_locallyCompactSpace p l hp hl
  haveI := leviPoints_nonarchimedeanGroup p l hp hl
  exact Representation.Equiv.mk
    (LinearEquiv.ofEq _ _
      (selectedWeightPart_leviJacquet_toSubmodule p l r hp hl hr hmul ha π))
    (fun _ => by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      rfl)

@[simp]
theorem selectedLeviJacquetEquivUnitary_apply :
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ x, (selectedLeviJacquetEquivUnitary p l r hp hl hr hmul ha π x).val = x.val :=
  fun _ => rfl

end Langlands.Aubert.General.RepresentedParabolic
