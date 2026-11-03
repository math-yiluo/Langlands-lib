import Langlands.GroupScheme.Rational.VectorCoordinateFunctions
import Langlands.GroupScheme.Rational.VectorCoordinateRealization
import Langlands.GroupScheme.Rational.TangentImage
import Mathlib.LinearAlgebra.StdBasis

/-! # Exact actual Lie support of homogeneous vector-coordinate blocks -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot.HomogeneousVectorCoordinates

variable {k : Type u} [Field k]
    {V : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom V.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {b : AutomorphicAction S.toGrp V}
    (q : HomogeneousVectorCoordinates b)

omit [IsAffineHom V.X.hom] in
/-- Diagonal coordinates are scalar-linear on every test scheme. -/
theorem isLinear : IsLinearVectorCoordinates b q.coordinates := by
  refine ⟨q.naturality, ?_⟩
  intro T s c v
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [q.action, q.action]
  simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- The actual differential has the same diagonal coefficients. -/
theorem differential_coordinates (A : CommAlgCat.{u} (CommRingCat.of k))
    (s : Lie.AffinePoints S.toGrp A) (X : Additive (lieKernel V A))
    (i : Fin q.dimension) :
    vectorLieCoordinates q.coordinates q.naturality A (b.differential s X) i =
      (Lie.characterValue (q.weight i) s : A) *
        vectorLieCoordinates q.coordinates q.naturality A X i := by
  have h := q.isLinear.coordinateAction_eq A s
    (vectorLieCoordinates q.coordinates q.naturality A X)
  change vectorLieCoordinates q.coordinates q.naturality A
    (b.differential s
      ((vectorLieCoordinates q.coordinates q.naturality A).symm
        (vectorLieCoordinates q.coordinates q.naturality A X))) = _ at h
  rw [LinearEquiv.symm_apply_apply] at h
  have hi := congrFun h i
  rw [q.affine_action] at hi
  simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using hi

/-- The genuine basis of the actual Lie kernel given by unit coordinate vectors. -/
def lieBasis : Module.Basis (Fin q.dimension) k (Additive (lieKernel V k)) :=
  (Pi.basisFun k (Fin q.dimension)).map
    (vectorLieCoordinates q.coordinates q.naturality
      (CommAlgCat.of (CommRingCat.of k) k)).symm

@[simp]
theorem lieBasis_coordinates (i j : Fin q.dimension) :
    vectorLieCoordinates q.coordinates q.naturality
      (CommAlgCat.of (CommRingCat.of k) k) (q.lieBasis i) j =
        if j = i then 1 else 0 := by
  classical
  simp [lieBasis, Pi.basisFun_apply, Pi.single_apply, eq_comm]

@[simp]
theorem lieBasis_repr (X : Additive (lieKernel V k)) (i : Fin q.dimension) :
    q.lieBasis.repr X i =
      vectorLieCoordinates q.coordinates q.naturality
        (CommAlgCat.of (CommRingCat.of k) k) X i := by
  simp [lieBasis, Module.Basis.map_repr, Pi.basisFun_repr]

/-- The coordinate basis retains its assigned character under every extension. -/
theorem lieBasis_mem_weightSpace (i : Fin q.dimension) :
    q.lieBasis i ∈ actionWeightSpace b (q.weight i) := by
  rw [actionWeightSpace_eq_lieWeightSpace]
  intro A _ _ s
  simp only [Grp.id_hom_hom, Category.comp_id]
  apply (vectorLieCoordinates q.coordinates q.naturality
    (CommAlgCat.of (CommRingCat.of k) A)).injective
  funext j
  rw [q.differential_coordinates, map_smul]
  have hn := vectorLieCoordinates_naturality q.coordinates q.naturality
    (CommAlgCat.ofHom (Algebra.ofId k A)) (q.lieBasis i)
  change vectorLieCoordinates q.coordinates q.naturality
    (CommAlgCat.of (CommRingCat.of k) A)
      (lieKernelMapLinear V (Algebra.ofId k A) (q.lieBasis i)) =
    (fun j => (Algebra.ofId k A)
      (vectorLieCoordinates q.coordinates q.naturality
        (CommAlgCat.of (CommRingCat.of k) k) (q.lieBasis i) j)) at hn
  rw [hn]
  simp only [q.lieBasis_coordinates, Pi.smul_apply, smul_eq_mul]
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

/-- Tangent membership in a coordinate block is vanishing of its other coefficients. -/
theorem mem_tangent_coordinateSubgroup_iff (I : Set (Fin q.dimension))
    (X : Additive (lieKernel V k)) :
    X ∈ tangentSubmodule (vectorCoordinateSubgroup q.coordinates q.naturality I) ↔
      ∀ i, i ∉ I →
        vectorLieCoordinates q.coordinates q.naturality
          (CommAlgCat.of (CommRingCat.of k) k) X i = 0 := by
  constructor
  · intro h i hi
    have hz := h i hi
    change ((vectorAffineCoordinates q.coordinates (DualNumber k) X.toMul.val).toAdd i).snd = 0
    change ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom
      ((q.coordinates _ X.toMul.val).toAdd i)).snd = 0
    rw [hz, map_zero]
    rfl
  · intro h i hi
    apply (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).commRingCatIsoToRingEquiv.injective
    rw [map_zero]
    change (vectorAffineCoordinates q.coordinates (DualNumber k) X.toMul.val).toAdd i = 0
    apply TrivSqZeroExt.ext
    · exact vectorAffineCoordinates_kernel_fst q.coordinates q.naturality X.toMul i
    · exact h i hi

/-- Only the assigned basis weights can occur in the tangent space of a block. -/
theorem tangent_coordinateSubgroup_le_weightSpan (I : Set (Fin q.dimension)) :
    tangentSubmodule (vectorCoordinateSubgroup q.coordinates q.naturality I) ≤
      ⨆ χ ∈ q.weight '' I, actionWeightSpace b χ := by
  intro X hX
  rw [← q.lieBasis.sum_repr X]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : i ∈ I
  · apply Submodule.smul_mem
    have hle : actionWeightSpace b (q.weight i) ≤
        ⨆ χ ∈ q.weight '' I, actionWeightSpace b χ :=
      le_iSup_of_le (q.weight i) (le_iSup_of_le ⟨i, hi, rfl⟩ le_rfl)
    exact hle (q.lieBasis_mem_weightSpace i)
  · rw [q.lieBasis_repr,
      (q.mem_tangent_coordinateSubgroup_iff I X).mp hX i hi, zero_smul]
    exact Submodule.zero_mem _

include q in
/-- Split-torus independence also follows directly from the supplied finite coordinates. -/
theorem independent_weightSpaces (hS : IsSplitTorus S.toGrp) :
    iSupIndep (actionWeightSpace b) := by
  classical
  have heq : actionWeightSpace b = b.lieWeightSpace (𝟙 S.toGrp) :=
    funext (actionWeightSpace_eq_lieWeightSpace b)
  rw [heq]
  exact (AutomorphicAction.isInternal_lieWeightSpace_of_finiteCoordinates k V
    (finiteLieCoordinatesOfVector q.coordinates q.naturality) S hS b (𝟙 _)).submodule_iSupIndep

/-- The intrinsic support of a block is precisely its occurring coordinate labels. -/
theorem actionWeightSupport_coordinateSubgroup (hS : IsSplitTorus S.toGrp)
    (I : Set (Fin q.dimension)) :
    actionWeightSupport b (vectorCoordinateSubgroup q.coordinates q.naturality I) =
      q.weight '' I := by
  classical
  ext χ
  constructor
  · rintro ⟨X, hX0, hXχ, hXI⟩
    by_contra hχ
    exact hX0 ((Submodule.disjoint_def.mp
      ((q.independent_weightSpaces hS).disjoint_biSup hχ)) X hXχ
        (q.tangent_coordinateSubgroup_le_weightSpan I hXI))
  · rintro ⟨i, hi, rfl⟩
    refine ⟨q.lieBasis i, q.lieBasis.ne_zero i, q.lieBasis_mem_weightSpace i, ?_⟩
    apply (q.mem_tangent_coordinateSubgroup_iff I _).mpr
    intro j hj
    have hji : j ≠ i := by
      rintro rfl
      exact hj hi
    rw [q.lieBasis_coordinates, ite_eq_right hji]

/-- The coordinate block selected by a semigroup is itself an admissible generator. -/
theorem isSemigroupGenerator_coordinateSubgroup (hS : IsSplitTorus S.toGrp)
    (A : AddSubsemigroup (characterLattice S)) :
    IsSemigroupGenerator b A
      (vectorCoordinateSubgroup q.coordinates q.naturality {i | q.weight i ∈ A}) := by
  refine ⟨isSmoothConnectedClosed_vectorCoordinateSubgroup q.coordinates q.naturality _,
    q.isStable_coordinateSubgroup _, ?_⟩
  rw [q.actionWeightSupport_coordinateSubgroup hS]
  rintro χ ⟨i, hi, rfl⟩
  exact hi

/-- Every coordinate block selected by a semigroup lies in the actual generated subgroup. -/
theorem coordinateSubgroup_le_semigroupSubgroup (hS : IsSplitTorus S.toGrp)
    (A : AddSubsemigroup (characterLattice S)) :
    vectorCoordinateSubgroup q.coordinates q.naturality {i | q.weight i ∈ A} ≤
      semigroupSubgroup b A :=
  generator_le_semigroupSubgroup b A _
    (q.isSemigroupGenerator_coordinateSubgroup hS A)

/-- Under the exact coordinate/Lie comparison, the semigroup subgroup is its coordinate block. -/
theorem semigroupSubgroup_eq_coordinateSubgroup
    (hContain : CoordinateWeights.AugmentationLieContainmentStatement.{u})
    (hS : IsSplitTorus S.toGrp) (A : AddSubsemigroup (characterLattice S)) :
    semigroupSubgroup b A =
      vectorCoordinateSubgroup q.coordinates q.naturality {i | q.weight i ∈ A} :=
  le_antisymm (q.semigroupSubgroup_le_coordinateSubgroup hContain hS A)
    (q.coordinateSubgroup_le_semigroupSubgroup hS A)

end Langlands.GroupScheme.RelativeRoot.HomogeneousVectorCoordinates
