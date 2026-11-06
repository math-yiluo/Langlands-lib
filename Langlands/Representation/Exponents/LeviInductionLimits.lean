import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Exponents.LeviRadicalCompactSubgroups
import Langlands.Representation.Aubert.General.InductionLimits
import Langlands.Representation.Aubert.General.CuspidalRemainderTransport

/-! # Limit cones under induction on the actual Levi points

The radical modulus input is supplied by the actual unipotent radical over a
nonarchimedean local field. The indexing category retains the source carrier
universe in both its objects and morphisms.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance leviInductionPointTopology : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology

variable [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

/-- Normalized induction on the actual Levi points preserves small limits. -/
theorem leviInductionFunctor_preservesLimits
    [ValuativeRel k] [IsNonarchimedeanLocalField k]
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r)) :
    let := leviPointTopology l hl
    PreservesLimitsOfSize.{v, v} (leviInductionFunctor.{u, v} p l r hp hr hl hmul) := by
  let := leviPointTopology l hl
  let e := leviPointsEquiv p l hp hl
  have : (SmoothRep.pullbackFunctor.{u, u, v} e.symm).IsEquivalence :=
    (SmoothRep.pullbackEquivalence e.symm).isEquivalence_functor
  have := normalizedInductionFunctor_preservesLimits.{u, v}
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (isUnimodularModulus_pointImage_radical p r hp.isClosedSubgroup hr.1)
  change PreservesLimitsOfSize.{v, v}
    (SmoothRep.pullbackFunctor e.symm ⋙ normalizedInductionFunctor _ _)
  infer_instance

/-- Transport a supplied small limit cone through actual Levi-point induction. -/
noncomputable def leviInductionLimitCone
    [ValuativeRel k] [IsNonarchimedeanLocalField k]
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r)) :
    let := leviPointTopology l hl
    ∀ {J : Type v} [Category.{v} J]
      (F : J ⥤ SmoothRep.{0, u, v} ℂ (rationalPoints M)),
      LimitCone F → LimitCone (F ⋙ leviInductionFunctor.{u, v} p l r hp hr hl hmul) := by
  let := leviPointTopology l hl
  dsimp only
  intro J _ F c
  have := leviInductionFunctor_preservesLimits.{u, v} p l r hp hr hl hmul
  exact ⟨Functor.mapCone (leviInductionFunctor p l r hp hr hl hmul) c.cone,
    isLimitOfPreserves (leviInductionFunctor p l r hp hr hl hmul) c.isLimit⟩

end Langlands.Aubert.General.RepresentedParabolic
