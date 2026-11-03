import Langlands.Algebra.GradedSignIdeal
import Langlands.GroupScheme.Dynamic.CocharacterWeightCriterion
import Langlands.GroupScheme.Dynamic.WeightExclusion
import Langlands.GroupScheme.Dynamic.NestedDecomposition
import Langlands.GroupScheme.Rational.CoordinateCotangentSupportProof
import Langlands.GroupScheme.Rational.CoordinateSemigroupReduction
import Langlands.GroupScheme.Rational.RelativeRootSignSupport
import Langlands.GroupScheme.Rational.DynamicNestedParabolicDecompositionStatement
import Langlands.GroupScheme.Rational.RelativeRootNegationStatement

/-! # Root signs, dynamic unipotent inclusions, and nested decompositions from root negation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- If every actual relative root positive on `zeta` is positive on `eta`, then the dynamic
unipotent subgroup of `zeta` is contained in that of `eta`. -/
theorem unipotent_le_of_positive_rootSigns (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (zeta eta : cocharacterLattice T)
    (h : ∀ α ∈ relativeRoots i,
      0 < latticePairing T α zeta → 0 < latticePairing T α eta) :
    unipotent (CommGroupScheme.groupHom zeta ≫ i) ≤
      unipotent (CommGroupScheme.groupHom eta ≫ i) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  apply CocharacterWeights.unipotent_le_of_mem_nonpositiveIdeal i hT eta zeta
  intro w hw g hg
  have hdec := CoordinateWeights.coordinateWeightDecomposition k G inferInstance T hT
    (AutomorphicAction.conjugation i)
  refine Algebra.GradedSignIdeal.mem_nonpositiveSpan_of_cotangent_signs
    (CoordinateWeights.augmentationIdeal G)
    (CoordinateWeights.augmentationWeightSpace (AutomorphicAction.conjugation i)) hdec.2.1
    (fun _ _ _ _ hx hy =>
      (CoordinateWeights.augmentationGradedMul (AutomorphicAction.conjugation i)).mul_mem hx hy)
    ((latticePairing T).flip eta).toAddMonoidHom ((latticePairing T).flip zeta).toAddMonoidHom
    ?_ hw hg
  intro χ x hx hcot hpos
  have hsupp : χ ∈ CoordinateWeights.cotangentSupport (AutomorphicAction.conjugation i) :=
    ⟨CoordinateWeights.cotangentMk G x, hcot,
      CoordinateWeights.cotangentMk_mem_weightSpace _ χ hx⟩
  rw [CoordinateWeights.cotangentLieSupport k G inferInstance inferInstance T hT] at hsupp
  have hχ0 : χ ≠ 0 := by
    rintro rfl
    simp at hpos
  exact h χ ((RelativeRoot.mem_relativeRoots_iff_actionWeightSupport_conjugation_top i χ).mpr
    ⟨hχ0, hsupp⟩) hpos

/-- If the dynamic parabolic of `zeta` is contained in that of `eta`, then every actual relative
root nonnegative on `zeta` is nonnegative on `eta`. -/
theorem latticePairing_nonneg_of_parabolic_le (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (zeta eta : cocharacterLattice T)
    (hP : parabolic (CommGroupScheme.groupHom zeta ≫ i) ≤
      parabolic (CommGroupScheme.groupHom eta ≫ i))
    {α : characterLattice T} (hα : α ∈ relativeRoots i) (hz : 0 ≤ latticePairing T α zeta) :
    0 ≤ latticePairing T α eta := by
  obtain ⟨X, hX, hne⟩ := (Submodule.ne_bot_iff _).mp (mem_relativeRoots.mp hα).2
  have hspan : X ∈ nonnegativeWeightSpan i zeta := by
    rw [nonnegativeWeightSpan_def]
    exact Submodule.mem_iSup_of_mem α (Submodule.mem_iSup_of_mem hz hX)
  have hPz := (mem_nonnegativeWeightSpan_iff_mem_parabolic hT i zeta X).mp hspan
  exact latticePairing_nonneg_of_weight_mem_parabolic hT i eta hX hne
    (SubgroupFunctor.le_def.mp hP _ hPz)

/-- For a maximal split torus of a connected reductive group, negation stability of the actual
relative roots turns containment of dynamic parabolics into reverse containment of the dynamic
unipotent subgroups. -/
theorem unipotent_le_of_parabolic_le_of_negation
    (hNeg : RelativeRootNegationStatement.{u})
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (zeta eta : cocharacterLattice T)
    (hP : parabolic (CommGroupScheme.groupHom zeta ≫ i) ≤
      parabolic (CommGroupScheme.groupHom eta ≫ i)) :
    unipotent (CommGroupScheme.groupHom eta ≫ i) ≤
      unipotent (CommGroupScheme.groupHom zeta ≫ i) := by
  have := hG.isAffineHom
  have := hG.smooth
  have : LocallyOfFiniteType G.X.hom := inferInstance
  have hT : IsSplitTorus T.toGrp := hi.isSplitSubtorus.1
  apply unipotent_le_of_positive_rootSigns hT i eta zeta
  intro α hα hαeta
  by_contra! hαzeta
  have hz : 0 ≤ latticePairing T (-α) zeta := by
    simpa using (neg_nonneg.mpr hαzeta)
  have he := latticePairing_nonneg_of_parabolic_le hT i zeta eta hP
    (hNeg k G hG T i hi α hα) hz
  have hne : 0 ≤ -(latticePairing T α eta) := by
    simpa using he
  omega

end Dynamic

/-- Negation stability of the actual relative roots suffices for the exact nested parabolic
decomposition target. The negation statement remains an explicit premise. -/
def DynamicNestedParabolicDecompositionFromNegation : Prop :=
  RelativeRootNegationStatement.{u} → DynamicNestedParabolicDecompositionStatement.{u}

/-- Conditional assembly using the common maximal split torus supplied by compatibility. This
theorem does not discharge the negation statement. -/
theorem dynamicNestedParabolicDecomposition_of_negation :
    DynamicNestedParabolicDecompositionFromNegation.{u} := by
  intro hNeg k _ G hG χ ψ hCompat
  have := hG.isAffineHom
  obtain ⟨hP, hM, T, i, zeta, eta, hi, rfl, rfl⟩ := hCompat
  exact Dynamic.nestedLeviDecomposition_of_inclusions _ _ hP hM
    (Dynamic.unipotent_le_of_parabolic_le_of_negation hNeg hG T i hi zeta eta hP)

end Langlands.GroupScheme
