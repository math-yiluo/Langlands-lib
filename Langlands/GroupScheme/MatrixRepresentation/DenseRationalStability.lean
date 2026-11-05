import Langlands.AlgebraicGeometry.PointTopology.DenseRationalFamily
import Langlands.GroupScheme.MatrixRepresentation.RationalStableCoordinates
import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Invariant subspaces detected by a dense rational-point family -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k] {I : Type v}
  {J : GroupScheme (Spec (CommRingCat.of k))} [IsReduced J.X.left]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m]

/-- A dense family of base points detects invariant split coordinates on a reduced group. -/
theorem isStableCoordinates_of_denseBasePoints (ρ : MatrixRepresentation J n)
    (B : Matrix n m k) (C : Matrix m n k)
    (p : I → Langlands.AlgebraicGeometry.PointTopology.RationalPoint k J.X)
    (hp : Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPointFamily p)
    (h : ∀ i,
      ρ.coordinateStabilityDefect B C _ (p i) = 0) :
    ρ.IsStableCoordinates B C := by
  have hsep : IsSeparated (coefficientSpace n (CommRingCat.of k)).hom := by
    dsimp [coefficientSpace]
    infer_instance
  have huniv : ρ.coordinateStabilityDefect B C J.X (𝟙 _) = 0 := by
    ext r s
    let f : J.X ⟶ coefficientSpace n (CommRingCat.of k) :=
      coefficientPoint J.X (fun r => ρ.coordinateStabilityDefect B C J.X (𝟙 _) r s)
    let z : J.X ⟶ coefficientSpace n (CommRingCat.of k) :=
      coefficientPoint J.X 0
    have he : f = z := by
      apply Langlands.AlgebraicGeometry.PointTopology.hom_ext_of_denseRationalPointFamily p hp
      intro i
      apply coefficientCoordinates_injective
      simp only [f, z, coefficientCoordinates_comp,
        coefficientCoordinates_coefficientPoint]
      funext r
      have hx := congrArg (fun M => M r s)
        (ρ.coordinateStabilityDefect_naturality B C (p i) (𝟙 J.X))
      simp only [Category.comp_id, h i, Matrix.zero_apply, Matrix.map_apply] at hx
      exact hx.symm.trans (map_zero _).symm
    have hec := congrArg (fun q => coefficientCoordinates q r) he
    simpa only [f, z, coefficientCoordinates_coefficientPoint, Pi.zero_apply,
      Matrix.zero_apply] using hec
  intro T x
  apply sub_eq_zero.mp
  change ρ.coordinateStabilityDefect B C T x = 0
  have hx := ρ.coordinateStabilityDefect_naturality B C x (𝟙 J.X)
  simpa only [Category.comp_id, huniv, Matrix.map_zero _ (map_zero _)] using hx

/-- Dense-family detection expressed by matrices over the ground field. -/
theorem isStableCoordinates_of_denseRationalMatrix (ρ : MatrixRepresentation J n)
    (B : Matrix n m k) (C : Matrix m n k)
    (p : I → Langlands.AlgebraicGeometry.PointTopology.RationalPoint k J.X)
    (hp : Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPointFamily p)
    (h : ∀ i,
      (ρ.rationalMatrix (p i) : Matrix n n k) * B =
        B * (C * (ρ.rationalMatrix (p i) : Matrix n n k) * B)) :
    ρ.IsStableCoordinates B C := by
  apply isStableCoordinates_of_denseBasePoints ρ B C p hp
  intro i
  let e := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  apply Matrix.map_injective e.injective
  change (ρ.coordinateStabilityDefect B C _ (p i)).map e.toRingHom =
    (0 : Matrix n m Γ(Spec (CommRingCat.of k), ⊤)).map e.toRingHom
  have hB : (B.map (scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).map
      e.toRingHom = B := by
    ext r s
    exact e.apply_symm_apply _
  have hC : (C.map (scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).map
      e.toRingHom = C := by
    ext r s
    exact e.apply_symm_apply _
  have hM : ((ρ.pointMatrix (Over.mk (𝟙 (Spec (CommRingCat.of k))))) (p i)).val.map
      e.toRingHom = (ρ.rationalMatrix (p i) : Matrix n n k) := rfl
  simpa only [coordinateStabilityDefect, Matrix.map_sub _ (map_sub _),
    Matrix.map_mul (f := e.toRingHom), hB, hC, hM,
    Matrix.map_zero _ (map_zero _)] using sub_eq_zero.mpr (h i)


/-- An actual representation is irreducible if its nonzero coordinate space has
no nontrivial proper subspace stable on all affine tests. -/
def IsIrreducible (ρ : MatrixRepresentation J n) : Prop :=
  Nontrivial (n → k) ∧
    ∀ V : Submodule k (n → k), ρ.IsStableSubspace V → V = ⊥ ∨ V = ⊤

/-- Stability under the specified rational-point matrices implies stability on
every affine test, including nonreduced test algebras. -/
theorem isStableSubspace_of_denseRationalFamily (ρ : MatrixRepresentation J n)
    (p : I → Langlands.AlgebraicGeometry.PointTopology.RationalPoint k J.X)
    (hp : Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPointFamily p)
    (V : Submodule k (n → k))
    (h : ∀ i v, v ∈ V → (ρ.rationalMatrix (p i) : Matrix n n k) *ᵥ v ∈ V) :
    ρ.IsStableSubspace V := by
  classical
  obtain ⟨d, B, C, hCB, hcols, hproj⟩ := exists_subspace_split_coordinates V
  have hstable : ρ.IsStableCoordinates B C := by
    apply isStableCoordinates_of_denseRationalMatrix ρ B C p hp
    intro i
    have hmat : (B * C) * ((ρ.rationalMatrix (p i) : Matrix n n k) * B) =
        (ρ.rationalMatrix (p i) : Matrix n n k) * B := by
      ext r s
      exact congrFun (hproj _ (h i _ (hcols s))) r
    simpa only [Matrix.mul_assoc] using hmat.symm
  have hrange : LinearMap.range B.mulVecLin = V := by
    apply le_antisymm
    · rintro v ⟨w, rfl⟩
      have he : B *ᵥ w = ∑ j, w j • (fun i => B i j) := by
        ext i
        simp [Matrix.mulVec, dotProduct, mul_comm]
      change B *ᵥ w ∈ V
      rw [he]
      exact Submodule.sum_mem _ (fun j _ => V.smul_mem _ (hcols j))
    · intro v hv
      refine ⟨C *ᵥ v, ?_⟩
      exact (Matrix.mulVec_mulVec v B C).trans (hproj v hv)
  rw [← hrange]
  exact (intertwines_restrictCoordinates ρ B C hCB hstable).isStableSubspace_range

/-- The natural linear representation on actual rational points. -/
def rationalAction (ρ : MatrixRepresentation J n) :
    Representation k
      (Langlands.AlgebraicGeometry.PointTopology.RationalPoint k J.X) (n → k) :=
  Matrix.toLinAlgEquiv'.toAlgHom.toMonoidHom.comp
    ((Units.coeHom _).comp ρ.rationalMatrix)

@[simp]
theorem rationalAction_apply (ρ : MatrixRepresentation J n)
    (g : Langlands.AlgebraicGeometry.PointTopology.RationalPoint k J.X) (x : n → k) :
    ρ.rationalAction g x = (ρ.rationalMatrix g : Matrix n n k) *ᵥ x := rfl

/-- An all-test irreducible representation remains irreducible on any dense
monoid family of actual rational points. -/
theorem irreducible_rationalAction_comp [Monoid I]
    (ρ : MatrixRepresentation J n) (hρ : ρ.IsIrreducible)
    (α : I →* Langlands.AlgebraicGeometry.PointTopology.RationalPoint k J.X)
    (hα : Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPointFamily α) :
    Representation.IsIrreducible (ρ.rationalAction.comp α) := by
  let := hρ.1
  refine { exists_pair_ne := ?_, eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, ?_⟩
    intro h
    have hh : (⊥ : Submodule k (n → k)) = ⊤ :=
      congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top hh
  · intro W
    have hW : ρ.IsStableSubspace W.toSubmodule := by
      apply isStableSubspace_of_denseRationalFamily ρ α hα
      intro i v hv
      exact W.apply_mem_toSubmodule i hv
    rcases hρ.2 W.toSubmodule hW with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)

end Langlands.GroupScheme.MatrixRepresentation
