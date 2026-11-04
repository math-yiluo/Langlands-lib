import Langlands.GroupScheme.MatrixRepresentation.TensorFixedStabilizer

/-! # Cancelling inverse line characters in a tensor representation

Standard basis vectors `e_j`, `e_s` on which a subgroup acts through inverse units give a
subgroup-fixed tensor `e_(j,s)`; conversely, any point fixing `e_(j,s)` preserves the line of
`e_j`. The dual of a representation that is diagonal at a point acts on each basis vector through
the inverse unit. All statements hold on arbitrary scheme tests, with no reducedness assumption.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

section Coordinates

variable {A : Type*} [CommRing A] {n m : Type} [DecidableEq n] [DecidableEq m]

/-- The pure tensor of two standard basis vectors is the standard basis vector of the pair. -/
theorem single_mul_single (j : n) (s : m) :
    (fun ij : n × m => (Pi.single j (1 : A) : n → A) ij.1 * (Pi.single s (1 : A) : m → A) ij.2) =
      (Pi.single (j, s) (1 : A) : n × m → A) := by
  funext ⟨r, t⟩
  simp only [Pi.single_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

end Coordinates

section SchemeRepresentations

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

omit [Fintype n] in
/-- The image of a standard basis vector in the global sections of a test scheme is again the
standard basis vector. -/
theorem scalarMap_single (T : Over (Spec R)) (j : n) :
    (fun r => scalarMap T ((Pi.single j 1 : n → R) r)) = (Pi.single j 1 : n → Γ(T.left, ⊤)) := by
  funext r
  simp only [Pi.single_apply]
  split_ifs <;> simp

/-- The tensor action on a standard basis vector of the pair is the pure tensor of the two
transformed standard basis vectors. -/
theorem tensor_pointMatrix_mulVec_single
    (ρ : MatrixRepresentation G n) (τ : MatrixRepresentation G m)
    (T : Over (Spec R)) (x : T ⟶ G.X) (j : n) (s : m) :
    ((ρ.tensor τ).pointMatrix T x : Matrix (n × m) (n × m) Γ(T.left, ⊤)) *ᵥ
        Pi.single (j, s) 1 =
      fun ij => ((ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ Pi.single j 1) ij.1 *
        ((τ.pointMatrix T x : Matrix m m Γ(T.left, ⊤)) *ᵥ Pi.single s 1) ij.2 := by
  rw [← single_mul_single, tensor_pointMatrix]
  exact GeneralLinear.kroneckerHom_mulVec n m _ _ _ _

/-- Cancellation of inverse line characters: if every point of `H` scales `e_j` under `ρ` by a
unit `a` and `e_s` under `τ` by `a⁻¹`, then the tensor `e_(j,s)` is fixed by `H`. -/
theorem isFixedVector_tensor_single
    (ρ : MatrixRepresentation G n) (τ : MatrixRepresentation G m) (i : H ⟶ G)
    (j : n) (s : m)
    (h : ∀ (T : Over (Spec R)) (x : T ⟶ H.X), ∃ a : Γ(T.left, ⊤)ˣ,
      (ρ.pointMatrix T (x ≫ i.hom.hom) : Matrix n n Γ(T.left, ⊤)) *ᵥ Pi.single j 1 =
          (a : Γ(T.left, ⊤)) • (Pi.single j 1 : n → Γ(T.left, ⊤)) ∧
        (τ.pointMatrix T (x ≫ i.hom.hom) : Matrix m m Γ(T.left, ⊤)) *ᵥ Pi.single s 1 =
          ((a⁻¹ : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) • (Pi.single s 1 : m → Γ(T.left, ⊤))) :
    ((ρ.tensor τ).restrict i).IsFixedVector (Pi.single (j, s) 1) := by
  intro T x
  obtain ⟨a, ha, hb⟩ := h T x
  rw [scalarMap_single, pointMatrix_restrict, tensor_pointMatrix_mulVec_single, ha, hb,
    ← single_mul_single]
  funext ij
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_mul_mul_comm, Units.mul_inv, one_mul]

/-- A point fixing the tensor `e_(j,s)` preserves the line of `e_j`, with a unit scalar. -/
theorem exists_unit_of_tensor_fixes_single
    (ρ : MatrixRepresentation G n) (τ : MatrixRepresentation G m) (j : n) (s : m)
    (T : Over (Spec R)) (x : T ⟶ G.X)
    (hx : ((ρ.tensor τ).pointMatrix T x : Matrix (n × m) (n × m) Γ(T.left, ⊤)) *ᵥ
        (fun ij => scalarMap T ((Pi.single (j, s) 1 : n × m → R) ij)) =
      fun ij => scalarMap T ((Pi.single (j, s) 1 : n × m → R) ij)) :
    ∃ a : Γ(T.left, ⊤)ˣ,
      (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ Pi.single j 1 =
        (a : Γ(T.left, ⊤)) • (Pi.single j 1 : n → Γ(T.left, ⊤)) := by
  rw [scalarMap_single, tensor_pointMatrix_mulVec_single, ← single_mul_single] at hx
  exact exists_unit_smul_of_pureTensor_eq _ _ _ _ j s (by simp) (by simp) hx

/-- If every point preserving the line of `e_j` lies in the subgroup, then so does every point
fixing the tensor `e_(j,s)`: the stabilizer hypothesis of `FixedSubrepresentation.range_kernel_eq`
for the tensor representation and the vector `e_(j,s)`. -/
theorem mem_range_of_tensor_fixes_single
    (ρ : MatrixRepresentation G n) (τ : MatrixRepresentation G m) (i : H ⟶ G)
    (j : n) (s : m)
    (hline : ∀ (T : Over (Spec R)) (x : T ⟶ G.X),
      (∃ a : Γ(T.left, ⊤)ˣ,
        (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ Pi.single j 1 =
          (a : Γ(T.left, ⊤)) • (Pi.single j 1 : n → Γ(T.left, ⊤))) →
        x ∈ (SubgroupFunctor.range i).carrier T)
    (T : Over (Spec R)) (x : T ⟶ G.X)
    (hx : ((ρ.tensor τ).pointMatrix T x : Matrix (n × m) (n × m) Γ(T.left, ⊤)) *ᵥ
        (fun ij => scalarMap T ((Pi.single (j, s) 1 : n × m → R) ij)) =
      fun ij => scalarMap T ((Pi.single (j, s) 1 : n × m → R) ij)) :
    x ∈ (SubgroupFunctor.range i).carrier T :=
  hline T x (exists_unit_of_tensor_fixes_single ρ τ j s T x hx)

/-- At a point where `σ` is the diagonal matrix of units `a t`, the dual representation scales
`e_s` by `(a s)⁻¹`, by the inverse-transpose formula for the dual. -/
theorem dual_pointMatrix_mulVec_single_of_diagonal
    (σ : MatrixRepresentation G m) (T : Over (Spec R)) (x : T ⟶ G.X)
    (a : m → Γ(T.left, ⊤)ˣ)
    (hx : (σ.pointMatrix T x : Matrix m m Γ(T.left, ⊤)) =
      Matrix.diagonal fun t => (a t : Γ(T.left, ⊤)))
    (s : m) :
    (σ.dual.pointMatrix T x : Matrix m m Γ(T.left, ⊤)) *ᵥ Pi.single s 1 =
      (((a s)⁻¹ : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) • (Pi.single s 1 : m → Γ(T.left, ⊤)) := by
  have hinv : (Matrix.diagonal fun t => (a t : Γ(T.left, ⊤)))⁻¹ =
      Matrix.diagonal fun t => (((a t)⁻¹ : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    simp only [Units.inv_mul]
    exact Matrix.diagonal_one
  rw [dual_pointMatrix, GeneralLinear.matrixContragredient_coe, Matrix.coe_units_inv, hx, hinv,
    Matrix.diagonal_transpose]
  funext r
  rw [Matrix.mulVec_diagonal]
  by_cases hr : r = s
  · subst hr
    simp
  · simp [hr]

end SchemeRepresentations

end Langlands.GroupScheme.MatrixRepresentation
