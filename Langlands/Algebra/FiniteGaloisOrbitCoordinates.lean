import Langlands.Algebra.FiniteGaloisOrbits

/-! # Semilinear coordinates on a finite Galois orbit -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u v

namespace Langlands.Algebra.FiniteGaloisOrbits

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  {I : Type v} [MulAction (L ≃ₐ[k] L) I]

/-- The original point, considered as a point of its orbit. -/
def orbitBasepoint (i : I) : MulAction.orbit (L ≃ₐ[k] L) i :=
  ⟨i, MulAction.mem_orbit_self i⟩

/-- Semilinear-equivariant functions on one orbit, with pointwise algebra operations. -/
def orbitCoordinateAlgebra (i : I) :
    Subalgebra k (MulAction.orbit (L ≃ₐ[k] L) i → L) where
  carrier := {f | ∀ (σ : L ≃ₐ[k] L) j, f (σ • j) = σ (f j)}
  zero_mem' := by intro σ j; exact (map_zero σ).symm
  one_mem' := by intro σ j; exact (map_one σ).symm
  add_mem' := by
    intro f g hf hg σ j
    change f (σ • j) + g (σ • j) = σ (f j + g j)
    rw [hf, hg, map_add]
  mul_mem' := by
    intro f g hf hg σ j
    change f (σ • j) * g (σ • j) = σ (f j * g j)
    rw [hf, hg, map_mul]
  algebraMap_mem' := by
    intro x σ j
    exact (σ.commutes x).symm

omit [FiniteDimensional k L] [IsGalois k L] in
@[simp] theorem mem_orbitCoordinateAlgebra (i : I)
    (f : MulAction.orbit (L ≃ₐ[k] L) i → L) :
    f ∈ orbitCoordinateAlgebra k L i ↔
      ∀ (σ : L ≃ₐ[k] L) j, f (σ • j) = σ (f j) := Iff.rfl

/-- The embedding associated to an orbit point intertwines the Galois actions. -/
theorem orbitEmbeddingEquiv_smul (i : I) (σ : L ≃ₐ[k] L)
    (j : MulAction.orbit (L ≃ₐ[k] L) i) :
    orbitEmbeddingEquiv k L i (σ • j) =
      σ.toAlgHom.comp (orbitEmbeddingEquiv k L i j) := by
  apply (orbitEmbeddingEquiv k L i).symm.injective
  apply Subtype.ext
  simpa only [Equiv.symm_apply_apply, MulAction.orbit.coe_smul] using
    (orbitEmbeddingEquiv_symm_comp k L i σ (orbitEmbeddingEquiv k L i j)).symm

/-- The embedding at the original point is the inclusion of the fixed field. -/
@[simp] theorem orbitEmbeddingEquiv_basepoint (i : I) :
    orbitEmbeddingEquiv k L i (orbitBasepoint k L i) = (stabilizerField k L i).val := by
  apply (orbitEmbeddingEquiv k L i).symm.injective
  apply Subtype.ext
  simp only [Equiv.symm_apply_apply]
  change i = _
  have h := orbitEmbeddingEquiv_symm_restriction k L i (1 : L ≃ₐ[k] L)
  have hval : restriction k L (MulAction.stabilizer (L ≃ₐ[k] L) i) 1 =
      (stabilizerField k L i).val := by ext x; rfl
  simpa only [hval, one_smul] using h.symm

/-- Evaluation at the original point has values in its stabilizer fixed field. -/
def orbitEvaluation (i : I) :
    orbitCoordinateAlgebra k L i →ₐ[k] stabilizerField k L i where
  toFun f := ⟨f.1 (orbitBasepoint k L i), by
    change _ ∈ IntermediateField.fixedField _
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hj : σ • orbitBasepoint k L i = orbitBasepoint k L i :=
      Subtype.ext ((MulAction.mem_stabilizer_iff).mp hσ)
    exact (hj ▸ f.2 σ (orbitBasepoint k L i)).symm⟩
  map_zero' := Subtype.ext rfl
  map_one' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  commutes' _ := Subtype.ext rfl

omit [FiniteDimensional k L] [IsGalois k L] in
@[simp] theorem orbitEvaluation_coe (i : I) (f : orbitCoordinateAlgebra k L i) :
    (orbitEvaluation k L i f : L) = f.1 (orbitBasepoint k L i) := rfl

/-- An element of the fixed field gives all its conjugate orbit coordinates. -/
def orbitCoordinates (i : I) :
    stabilizerField k L i →ₐ[k] orbitCoordinateAlgebra k L i where
  toFun x := ⟨fun j => orbitEmbeddingEquiv k L i j x, by
    intro σ j
    change orbitEmbeddingEquiv k L i (σ • j) x = σ (orbitEmbeddingEquiv k L i j x)
    rw [orbitEmbeddingEquiv_smul]
    rfl⟩
  map_zero' := by apply Subtype.ext; funext j; exact map_zero _
  map_one' := by apply Subtype.ext; funext j; exact map_one _
  map_add' x y := by apply Subtype.ext; funext j; exact map_add _ x y
  map_mul' x y := by apply Subtype.ext; funext j; exact map_mul _ x y
  commutes' x := by apply Subtype.ext; funext j; exact (orbitEmbeddingEquiv k L i j).commutes x

@[simp] theorem orbitCoordinates_apply (i : I) (x : stabilizerField k L i)
    (j : MulAction.orbit (L ≃ₐ[k] L) i) :
    (orbitCoordinates k L i x).1 j = orbitEmbeddingEquiv k L i j x := rfl

@[simp] theorem orbitEvaluation_coordinates (i : I) (x : stabilizerField k L i) :
    orbitEvaluation k L i (orbitCoordinates k L i x) = x := by
  apply Subtype.ext
  change orbitEmbeddingEquiv k L i (orbitBasepoint k L i) x = (x : L)
  rw [orbitEmbeddingEquiv_basepoint]
  rfl

omit [FiniteDimensional k L] [IsGalois k L] in
/-- Equivariance determines an orbit function from its value at the original point. -/
theorem orbitEvaluation_injective (i : I) :
    Function.Injective (orbitEvaluation k L i) := by
  intro f g h
  apply Subtype.ext
  funext j
  obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp j.property
  have hj : j = σ • orbitBasepoint k L i := Subtype.ext hσ.symm
  have hbase : f.1 (orbitBasepoint k L i) = g.1 (orbitBasepoint k L i) :=
    congrArg (fun x : stabilizerField k L i => (x : L)) h
  rw [hj, f.2, g.2, hbase]

@[simp] theorem orbitCoordinates_evaluation (i : I) (f : orbitCoordinateAlgebra k L i) :
    orbitCoordinates k L i (orbitEvaluation k L i f) = f := by
  apply orbitEvaluation_injective k L i
  exact orbitEvaluation_coordinates k L i _

/-- Evaluation identifies semilinear orbit coordinates with the stabilizer fixed field. -/
def orbitEvaluationEquiv (i : I) :
    orbitCoordinateAlgebra k L i ≃ₐ[k] stabilizerField k L i :=
  { orbitEvaluation k L i with
    invFun := orbitCoordinates k L i
    left_inv := orbitCoordinates_evaluation k L i
    right_inv := orbitEvaluation_coordinates k L i }

@[simp] theorem orbitEvaluationEquiv_apply (i : I) (f : orbitCoordinateAlgebra k L i) :
    orbitEvaluationEquiv k L i f = orbitEvaluation k L i f := rfl

/-- The inverse equivalence evaluates an element through each orbit embedding. -/
@[simp] theorem orbitEvaluationEquiv_symm_apply (i : I) (x : stabilizerField k L i)
    (j : MulAction.orbit (L ≃ₐ[k] L) i) :
    ((orbitEvaluationEquiv k L i).symm x).1 j = orbitEmbeddingEquiv k L i j x := rfl

end Langlands.Algebra.FiniteGaloisOrbits
