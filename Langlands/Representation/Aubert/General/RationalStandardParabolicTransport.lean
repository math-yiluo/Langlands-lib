import Langlands.Representation.Aubert.General.PrerequisiteStatements
import Langlands.Representation.Aubert.General.RationalStandardInductionNonzero
import Langlands.Representation.Aubert.General.RationalInductionDualityReduction
import Langlands.Representation.Aubert.General.RationalAlternatingOperator

/-! # Standard parabolic structure from the dynamic statements

The actual standard parabolic `P_I(k)` is closed for the canonical point
topology, and the two dynamic finite-length statements give finite-length
preservation for the actual standard induction and Jacquet functors. Both are
transported along the subgroup equalities of the standard-cocharacter statement. -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

include hStandard hG hi hν

/-- The actual standard parabolic `P_I(k)` is closed in `G(k)` for the
canonical point topology. -/
theorem isClosed_standard_parabolic (I : Finset (SimpleRoot i ν)) :
    let : TopologicalSpace (RationalPoint k G.X) := pointTopology
    IsClosed (parabolic i ν I : Set (RationalPoint k G.X)) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : T2Space k := Langlands.BruhatTits.localField_t2Space k
  obtain ⟨χ, hχ⟩ := exists_parabolic_eq_dynamic i ν hStandard hG hi hν I
  change @IsClosed (RationalPoint k G.X) (rationalPointTopology k G.X)
    (parabolic i ν I : Set (RationalPoint k G.X))
  rw [hχ]
  exact isClosed_dynamic_parabolic k G χ

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The three standard subgroups are the dynamic subgroups of one cocharacter. -/
theorem exists_standard_eq_dynamic (I : Finset (SimpleRoot i ν)) :
    ∃ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      parabolic i ν I = (Dynamic.parabolic χ).carrier (Over.mk (𝟙 _)) ∧
      levi i ν I = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) ∧
      unipotent i ν I = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) := by
  obtain ⟨hexists, hcompare⟩ :=
    hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  obtain ⟨ζ, hζ⟩ := hexists
  obtain ⟨hP, hM, hU⟩ := hcompare ζ hζ
  exact ⟨CommGroupScheme.groupHom ζ ≫ i,
    congrArg (fun H => H.carrier (Over.mk (𝟙 _))) hP,
    congrArg (fun H => H.carrier (Over.mk (𝟙 _))) hM,
    congrArg (fun H => H.carrier (Over.mk (𝟙 _))) hU⟩

/-- Dynamic finite-length preservation by normalized induction gives it for
every actual standard parabolic. -/
theorem standard_induction_preservesFiniteLength
    (hDyn : DynamicInductionFiniteLengthStatement.{u, uV}) :
    let : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] (I : Finset (SimpleRoot i ν))
      (hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X))),
      PreservesFiniteLength (normalizedInductionFunctor.{u, uV}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I) hU) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ I hU
  obtain ⟨χ, hP, hM, hU'⟩ := exists_standard_eq_dynamic i ν hStandard hG hi hν I
  have hDU : IsClosed ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) :
      Set (RationalPoint k G.X)) := hU' ▸ hU
  have key := hDyn k G hG χ hDU
  generalize isSemidirectDecomposition_of_standardCocharacterStatement
    i ν hStandard hG hi hν I = h
  revert h hU
  rw [hP, hM, hU']
  intro _ _
  exact key

/-- Dynamic finite-length preservation by normalized Jacquet restriction gives
it for every actual standard parabolic. -/
theorem standard_jacquet_preservesFiniteLength
    (hDyn : DynamicJacquetFiniteLengthStatement.{u, uV}) :
    let : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] (I : Finset (SimpleRoot i ν))
      (hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X))),
      PreservesFiniteLength (jacquetFunctor.{u, uV}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I) hU) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ I hU
  obtain ⟨χ, hP, hM, hU'⟩ := exists_standard_eq_dynamic i ν hStandard hG hi hν I
  have hDU : IsClosed ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) :
      Set (RationalPoint k G.X)) := hU' ▸ hU
  have key := hDyn k G hG χ hDU
  generalize isSemidirectDecomposition_of_standardCocharacterStatement
    i ν hStandard hG hi hν I = h
  revert h hU
  rw [hP, hM, hU']
  intro _ _
  exact key

end Langlands.Aubert.General.RationalPointFamily
