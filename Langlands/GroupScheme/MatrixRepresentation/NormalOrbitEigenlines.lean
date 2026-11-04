import Langlands.GroupScheme.MatrixRepresentation.OrbitCoordinates
import Langlands.GroupScheme.Chevalley.ActualLineStabilizer

/-! # Eigenlines of a normal subgroup in rational orbit coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The representation acts by a unit scalar on the given vector on every test.
No nonzero condition on the vector is included. -/
def HasUnitScalarAction (ρ : MatrixRepresentation G n) (v : n → k) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
    ∃ a : Γ(T.left, ⊤)ˣ,
      (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ
          (fun r => scalarMap T (v r)) =
        (a : Γ(T.left, ⊤)) • (fun r => scalarMap T (v r))

/-- Normality preserves the subgroup-eigenline property under translation by a
point of the ambient group, on every test scheme. -/
theorem normal_unitEigenvector_translate
    (ρ : MatrixRepresentation G n) (i : H ⟶ G)
    (hN : (SubgroupFunctor.range i).IsNormal) (j : n)
    (hline : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
      x ∈ (SubgroupFunctor.range i).carrier T →
        ∃ a : Γ(T.left, ⊤)ˣ,
          (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ Pi.single j 1 =
            (a : Γ(T.left, ⊤)) • (Pi.single j (1 : Γ(T.left, ⊤)) : n → Γ(T.left, ⊤)))
    (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (h : T ⟶ H.X) :
    ∃ a : Γ(T.left, ⊤)ˣ,
      (ρ.pointMatrix T (h ≫ i.hom.hom) : Matrix n n Γ(T.left, ⊤)) *ᵥ
          ((ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) *ᵥ Pi.single j 1) =
        (a : Γ(T.left, ⊤)) •
          ((ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) *ᵥ Pi.single j 1) := by
  have hconj := hN T g⁻¹ (h ≫ i.hom.hom) (by trivial)
    (SubgroupFunctor.mem_range.mpr ⟨h, rfl⟩)
  obtain ⟨a, ha⟩ := hline T _ hconj
  rw [map_mul, map_mul, map_inv, inv_inv] at ha
  set U := ρ.pointMatrix T g
  set M := ρ.pointMatrix T (h ≫ i.hom.hom)
  have he : (M : Matrix n n Γ(T.left, ⊤)) *ᵥ
      ((U : Matrix n n Γ(T.left, ⊤)) *ᵥ Pi.single j 1) =
    (U : Matrix n n Γ(T.left, ⊤)) *ᵥ
      (((U⁻¹ * M * U : GL n Γ(T.left, ⊤)) : Matrix n n Γ(T.left, ⊤)) *ᵥ
        Pi.single j 1) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  refine ⟨a, ?_⟩
  rw [he, ha, Matrix.mulVec_smul]

/-- A rational orbit vector spans a subgroup eigenline after any scalar extension. -/
theorem normal_rationalOrbit_column_eigenvector
    (ρ : MatrixRepresentation G n) (i : H ⟶ G)
    (hN : (SubgroupFunctor.range i).IsNormal) (j : n)
    (hline : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
      x ∈ (SubgroupFunctor.range i).carrier T →
        ∃ a : Γ(T.left, ⊤)ˣ,
          (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ Pi.single j 1 =
            (a : Γ(T.left, ⊤)) • (Pi.single j (1 : Γ(T.left, ⊤)) : n → Γ(T.left, ⊤)))
    {v : n → k}
    (hv : ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      v = (ρ.rationalMatrix g : Matrix n n k) *ᵥ Pi.single j 1)
    : (ρ.restrict i).HasUnitScalarAction v := by
  intro T h
  rw [pointMatrix_restrict]
  obtain ⟨g, rfl⟩ := hv
  have he : (fun r => scalarMap T
      (((ρ.rationalMatrix g : Matrix n n k) *ᵥ Pi.single j 1) r)) =
    (ρ.pointMatrix T (CartesianMonoidalCategory.toUnit T ≫ g) :
      Matrix n n Γ(T.left, ⊤)) *ᵥ Pi.single j 1 := by
    rw [pointMatrix_constant]
    simp only [Matrix.mulVec_single_one]
    rfl
  rw [he]
  exact normal_unitEigenvector_translate ρ i hN j hline T _ h

/-- If the split inclusion columns are eigenvectors, the induced matrix is
exactly diagonal with those eigenvalues. -/
theorem restrictCoordinates_eq_diagonal_of_column_eigenvectors
    (ρ : MatrixRepresentation G n) (B : Matrix n m k) (C : Matrix m n k)
    (hCB : C * B = 1) (hstable : ρ.IsStableCoordinates B C)
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X)
    (a : m → Γ(T.left, ⊤)ˣ)
    (ha : ∀ s, (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ
      (fun r => scalarMap T (B r s)) =
        (a s : Γ(T.left, ⊤)) • (fun r => scalarMap T (B r s))) :
    ((restrictCoordinates ρ B C hCB hstable).pointMatrix T x :
      Matrix m m Γ(T.left, ⊤)) = Matrix.diagonal (fun s => (a s : Γ(T.left, ⊤))) := by
  rw [restrictCoordinates_pointMatrix]
  change C.map (scalarMap T) * (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *
    B.map (scalarMap T) = _
  apply Matrix.ext_of_mulVec_single
  intro s
  have hCB' : C.map (scalarMap T) * B.map (scalarMap T) = 1 := by
    rw [← Matrix.map_mul, hCB, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  change C.map (scalarMap T) *ᵥ
    ((ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ
      (fun r => scalarMap T (B r s))) = _
  rw [ha s, Matrix.mulVec_smul]
  have hvec : C.map (scalarMap T) *ᵥ (fun r => scalarMap T (B r s)) =
      Pi.single s 1 := by
    have he := congrArg (fun M : Matrix m m Γ(T.left, ⊤) => M *ᵥ Pi.single s 1) hCB'
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.one_mulVec] at he
    exact he
  rw [hvec]
  funext t
  by_cases ht : t = s
  · subst t
    simp
  · simp [ht]

end Langlands.GroupScheme.MatrixRepresentation
