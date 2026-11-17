import Langlands.GroupScheme.Reductive.InvariantPowerLift
import Langlands.GroupScheme.Reductive.AffineInducedRegular
import Langlands.GroupScheme.HomogeneousCharacterCoordinates
import Langlands.GroupScheme.MatrixRepresentation.RationalStableCoordinates

/-! # Finite covariant families inside translation-stable spaces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.InvariantPowerLift

variable {k : Type u} [Field k]
  {J H : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- A coordinate inclusion transforms a finite section family by its transpose. -/
def coordinateFamily (B : Matrix n m k) (f : n → Γ(J.X.left, ⊤)) :
    m → Γ(J.X.left, ⊤) :=
  (B.map (scalarMap J.X))ᵀ *ᵥ f

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem appTop_coordinateFamily (B : Matrix n m k) (f : n → Γ(J.X.left, ⊤))
    (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ J.X) :
    (fun j => g.left.appTop (coordinateFamily B f j)) =
      (B.map (scalarMap T))ᵀ *ᵥ (fun j => g.left.appTop (f j)) := by
  ext j
  simp only [coordinateFamily, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Matrix.map_apply, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro r _
  exact congrArg (fun a => a * g.left.appTop (f r))
    (scalarMap_naturality g (B r j))

/-- An all-test coordinate intertwiner restricts a covariant section family. -/
theorem IsRightCovariantFamily.mapCoordinates
    {i : H ⟶ J} {ρ : MatrixRepresentation H n}
    {f : n → Γ(J.X.left, ⊤)} (hf : IsRightCovariantFamily i ρ f)
    (σ : MatrixRepresentation H m) (B : Matrix n m k)
    (hB : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X),
      (ρ.pointMatrix T h : Matrix n n Γ(T.left, ⊤)) * B.map (scalarMap T) =
        B.map (scalarMap T) *
          (σ.pointMatrix T h : Matrix m m Γ(T.left, ⊤))) :
    IsRightCovariantFamily i σ (coordinateFamily B f) := by
  intro T g h
  rw [appTop_coordinateFamily, hf T g h, appTop_coordinateFamily,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hB,
    Matrix.transpose_mul]

/-- Split invariant coordinates restrict a covariant section family on all tests. -/
theorem IsRightCovariantFamily.restrictCoordinates
    {i : H ⟶ J} {ρ : MatrixRepresentation H n}
    {f : n → Γ(J.X.left, ⊤)} (hf : IsRightCovariantFamily i ρ f)
    (B : Matrix n m k) (C : Matrix m n k) (hCB : C * B = 1)
    (hstable : ρ.IsStableCoordinates B C) :
    IsRightCovariantFamily i (ρ.restrictCoordinates B C hCB hstable)
      (coordinateFamily B f) :=
  hf.mapCoordinates _ B (MatrixRepresentation.restrictCoordinates_intertwines
    ρ B C hCB hstable)

section Regular

open AffineCoordinates AffineLinearEmbedding Chevalley MatrixRepresentation

variable [IsAffine J.X.left]
  (i : H ⟶ J) (V : Submodule k (algebra J)) {d : ℕ} (b : Basis (Fin d) k V)
  (hV : letI := (bialgebra (corepresentation J)).toCoalgebra
    ∀ (ψ : Module.Dual k (algebra J)) (w : algebra J),
      w ∈ V → rightAct ψ w ∈ V)

/-- An actual finite regular basis supplies the required covariance law. -/
theorem isRightCovariantFamily_regularBasis :
    IsRightCovariantFamily i ((affineRegularRepresentation J V b hV).restrict i)
      (fun j => globalAlgHom J (b j : algebra J)) := by
  intro T g h
  ext j
  rw [← pointAlgebraHom_apply_eq, affineRegularRepresentation_mul_basis J V b hV]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    pointMatrix_restrict, ← pointAlgebraHom_apply_eq]
  apply Finset.sum_congr rfl
  intro r _
  exact mul_comm _ _

end Regular

end Langlands.GroupScheme.InvariantPowerLift
