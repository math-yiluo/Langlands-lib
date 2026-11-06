import Langlands.Representation.Aubert.General.StandardIrreducibleInductionFiniteLength
import Langlands.Representation.Aubert.General.DynamicStandardPresentation
import Langlands.Representation.Aubert.General.IrreducibleInductionFiniteLengthStatement
import Langlands.Representation.Aubert.General.RationalLeviQuotientCompactness
import Langlands.Representation.Aubert.General.RationalInvolutivityReduction
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups

/-! # Finite-length embeddings for actual dynamic induction from standard inputs -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Aubert.General

/-- An actual coefficient and an injective map into its finite-length
normalized induction, allowing an independent source carrier universe. -/
structure FiniteLengthInductionEmbedding
    {H : Type u} [Group H] [TopologicalSpace H]
    [LocallyCompactSpace H] [NonarchimedeanGroup H]
    {P M U : Subgroup H} (h : IsSemidirectDecomposition P M U)
    (hc : IsClosed (U : Set H)) (A : SmoothRep.{0, u, uV} ℂ M) where
  coefficient : SmoothRep.{0, u, max (u + 1) uV} ℂ M
  map : ((normalizedInductionFunctor.{u, uV} h hc).obj A).representation.IntertwiningMap
    ((normalizedInductionFunctor.{u, max (u + 1) uV} h hc).obj coefficient).representation
  injective : Function.Injective map
  finiteLength :
    ((normalizedInductionFunctor.{u, max (u + 1) uV} h hc).obj coefficient).HasFiniteLength

/-- Construct an actual finite-length induced ambient representation for the
original dynamic triple, retaining the named structural and cuspidal inputs. -/
def dynamicIrreducibleInductionEmbedding_of_standard_inputs
    (hSuper : RationalPointFamily.RationalSupercuspidalInductionFiniteLengthStatement.{u, max (u + 1) uV})
    (hStandard : StandardCocharacterStatement.{u})
    (hInter : StandardLeviIntersectionStatement.{u})
    (hRoots : RelativeRootSystemStatement.{u})
    (hcompact : BruhatTits.DynamicParabolicQuotientCompactStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    ∀ [LocallyCompactSpace (RationalPoint F G.X)]
      [NonarchimedeanGroup (RationalPoint F G.X)]
      (hU : IsClosed ((Dynamic.unipotent χ).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F)))) : Set (RationalPoint F G.X)))
      (A : SmoothRep.{0, u, uV} ℂ
        ((Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))))),
      A.IsIrreducible →
        FiniteLengthInductionEmbedding
          (dynamic_isSemidirectDecomposition χ
            (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hU A := by
  haveI := hG.isAffineHom
  haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
  intro _ _ hU A hA
  haveI : T2Space F := BruhatTits.localField_t2Space F
  haveI : T2Space (RationalPoint F G.X) := rationalPoint_t2Space F G
  let S := dynamicStandardPresentation hStandard F G hG χ
  let i := S.torusHom
  let ν := S.direction
  let K := S.index
  have hUs : ∀ I, IsClosed
      (RationalPointFamily.unipotent i ν I : Set (RationalPoint F G.X)) :=
    RationalPointFamily.standardUnipotent_isClosed_of_standardCocharacterStatement
      i ν hStandard hG S.maximal S.generic
  have hMs : ∀ I, IsClosed
      (RationalPointFamily.levi i ν I : Set (RationalPoint F G.X)) :=
    RationalPointFamily.levi_isClosed i ν hStandard hG S.maximal S.generic
      (RationalPointFamily.standardParabolic_isClosed_of_standardCocharacterStatement
        i ν hStandard hG S.maximal S.generic)
      (RationalPointFamily.continuous_standard_projection
        i ν hStandard hG S.maximal S.generic)
  have hKs : ∀ I : Finset K, CompactSpace (Induction.LeftQuotient
      ((RationalPointFamily.parabolic i ν (leviIndex K I)).subgroupOf
        (RationalPointFamily.levi i ν K))) :=
    RationalPointFamily.compactSpace_leftQuotient_in_levi_of_dynamic
      i ν hInter hG S.maximal S.generic hStandard hcompact K
  have key :
      ∀ (h : IsSemidirectDecomposition (RationalPointFamily.parabolic i ν K)
          (RationalPointFamily.levi i ν K) (RationalPointFamily.unipotent i ν K))
        (hc : IsClosed (RationalPointFamily.unipotent i ν K : Set (RationalPoint F G.X)))
        (τ : SmoothRep.{0, u, uV} ℂ (RationalPointFamily.levi i ν K)),
        τ.IsIrreducible → Nonempty (FiniteLengthInductionEmbedding h hc τ) := by
    intro h hc τ hτ
    let E := RationalPointFamily.standardIrreducibleInductionEmbedding
      i ν hG S.maximal S.generic hSuper hStandard hInter
      (hRoots F G hG S.torus i S.maximal) hUs hMs K hKs τ hτ
    exact ⟨⟨E.coefficient, E.map, E.injective, E.finiteLength⟩⟩
  have hP : RationalPointFamily.parabolic i ν K =
      (Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) :=
    congrArg (fun Q : SubgroupFunctor G =>
      Q.carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))) S.parabolic_eq
  have hM : RationalPointFamily.levi i ν K =
      (Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) :=
    congrArg (fun Q : SubgroupFunctor G =>
      Q.carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))) S.levi_eq
  have hN : RationalPointFamily.unipotent i ν K =
      (Dynamic.unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) :=
    congrArg (fun Q : SubgroupFunctor G =>
      Q.carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))) S.unipotent_eq
  rw [hP, hM, hN] at key
  exact Classical.choice (key _ hU A hA)

/-- The same inputs imply the exact published dynamic irreducible
finite-length proposition, with its original independent universes. -/
theorem dynamicInductionIrreducibleFiniteLength_of_standard_inputs
    (hSuper : RationalPointFamily.RationalSupercuspidalInductionFiniteLengthStatement.{u, max (u + 1) uV})
    (hStandard : StandardCocharacterStatement.{u})
    (hInter : StandardLeviIntersectionStatement.{u})
    (hRoots : RelativeRootSystemStatement.{u})
    (hcompact : BruhatTits.DynamicParabolicQuotientCompactStatement.{u}) :
    DynamicInductionIrreducibleFiniteLengthStatement.{u, uV} := by
  intro F _ _ _ _ G hG χ
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
  intro _ _ hU A hA
  let E := dynamicIrreducibleInductionEmbedding_of_standard_inputs
    hSuper hStandard hInter hRoots hcompact F G hG χ hU A hA
  exact IsFiniteLength.of_injective E.finiteLength
    (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ E.map) E.injective

end Langlands.Aubert.General
