import Langlands.Representation.Aubert.General.RationalStandardInductionNonzeroStatement
import Langlands.Representation.Aubert.General.DynamicInductionExactness
import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-! # Actual standard induction is nonzero on nonzero smooth objects -/

noncomputable section

universe u v uG uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

namespace RationalPointFamily

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Every semidirect projection on these exact standard subgroups is
continuous for the canonical point topology. -/
theorem continuous_standard_projection
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν)) :
    let : TopologicalSpace (RationalPoint k G.X) := pointTopology
    Continuous
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I).projection := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsSeparated G.X.hom := hG.isSeparated
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  obtain ⟨hexists, hcompare⟩ :=
    hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  obtain ⟨ζ, hζ⟩ := hexists
  obtain ⟨hP, hM, hU⟩ := hcompare ζ hζ
  have hP' : parabolic i ν I =
      (Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i)).carrier
        (Over.mk (𝟙 _)) := congrArg (fun H => H.carrier (Over.mk (𝟙 _))) hP
  have hM' : levi i ν I =
      (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).carrier
        (Over.mk (𝟙 _)) := congrArg (fun H => H.carrier (Over.mk (𝟙 _))) hM
  have hU' : unipotent i ν I =
      (Dynamic.unipotent (CommGroupScheme.groupHom ζ ≫ i)).carrier
        (Over.mk (𝟙 _)) := congrArg (fun H => H.carrier (Over.mk (𝟙 _))) hU
  generalize
    isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν I = h
  revert h
  rw [hP', hM', hU']
  intro h
  exact continuous_dynamic_projection k G (CommGroupScheme.groupHom ζ ≫ i)

end RationalPointFamily

section Generic

variable {H : Type uG} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [NonarchimedeanGroup H]
  {P M U : Subgroup H}

/-- Evaluation of actual normalized induction is surjective when its actual
Levi projection is continuous. -/
theorem normalizedInduction_eval_surjective
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set H))
    (hproj : Continuous h.projection) (σ : SmoothRep.{0, uG, uV} ℂ M) :
    Function.Surjective (Induction.eval P (inducingRepresentation h hU σ) · (1 : H)) := by
  have hsm : IsSmooth (inducingRepresentation h hU σ) :=
    (isSmooth_twist_iff _ _
      (HaarModulus.isOpen_ker_closedHalfCharacter U hU P h.le_normalizer)).mpr
      (isSmooth_comp h.projection hproj σ.isSmooth)
  intro v
  refine ⟨(Induction.compactLocalSection P (inducingRepresentation h hU σ)
    hsm 1 v Set.univ isOpen_univ (Set.mem_univ _)).val, ?_⟩
  exact Induction.compactLocalSection_apply P (inducingRepresentation h hU σ)
    hsm 1 v Set.univ isOpen_univ (Set.mem_univ _)

/-- A continuous actual Levi projection makes normalized induction nonzero
on every nonzero smooth object. -/
theorem nontrivial_normalizedInduction
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set H))
    (hproj : Continuous h.projection) (σ : SmoothRep.{0, uG, uV} ℂ M)
    [Nontrivial σ] :
    Nontrivial ((normalizedInductionFunctor h hU).obj σ) :=
  Function.Surjective.nontrivial (normalizedInduction_eval_surjective h hU hproj σ)

end Generic

namespace RationalPointFamily

/-- The entire actual standard nonzeroness proposition, with independent
field and carrier parameters. -/
theorem rationalStandardInductionNonzero :
    RationalStandardInductionNonzeroStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ ν hν hStandard I hU σ _
  exact nontrivial_normalizedInduction
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν I) hU
    (continuous_standard_projection i ν hStandard hG hi hν I) σ

end RationalPointFamily

end Langlands.Aubert.General
