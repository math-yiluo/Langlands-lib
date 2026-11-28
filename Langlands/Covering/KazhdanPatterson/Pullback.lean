import Langlands.Group.GL.Basic
import Langlands.GroupTheory.CentralCocycle

/-! # Determinant pullback and twisting for Kazhdan–Patterson cocycles -/

namespace Langlands.KazhdanPatterson

attribute [local instance] trivialCoefficientAction

universe u v

variable {R : Type u} [CommRing R] {r : ℕ}

private def inverseDeterminantBlock : GeneralLinear r R →* Matrix (Fin 1) (Fin 1) R :=
  (Matrix.scalar (Fin 1)).toMonoidHom.comp
    ((Units.coeHom R).comp (invMonoidHom.comp GeneralLinear.determinant))

private def determinantBlock (g : GeneralLinear r R) :
    Matrix (Fin r ⊕ Fin 1) (Fin r ⊕ Fin 1) R :=
  Matrix.fromBlocks g.val 0 0 (inverseDeterminantBlock g)

private theorem determinantBlock_det (g : GeneralLinear r R) :
    (determinantBlock g).det = 1 := by
  rw [determinantBlock, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fin_one]
  change (GeneralLinear.determinant g).val *
    Matrix.scalar (Fin 1) ((GeneralLinear.determinant g)⁻¹).val 0 0 = 1
  rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
  exact (GeneralLinear.determinant g).val_inv

/-- The bottom-right determinant embedding used in Banks–Levy–Sepanski, §3. -/
def determinantEmbedding : GeneralLinear r R →* Matrix.SpecialLinearGroup (Fin (r + 1)) R where
  toFun g := ⟨(determinantBlock g).reindex finSumFinEquiv finSumFinEquiv, by
    rw [Matrix.det_reindex_self, determinantBlock_det]⟩
  map_one' := by
    apply Subtype.ext
    change Matrix.reindexRingEquiv R finSumFinEquiv (determinantBlock (1 : GeneralLinear r R)) = 1
    rw [determinantBlock, Units.val_one, map_one, Matrix.fromBlocks_one, map_one]
  map_mul' g h := by
    apply Subtype.ext
    let e := Matrix.reindexRingEquiv R (finSumFinEquiv : Fin r ⊕ Fin 1 ≃ Fin (r + 1))
    change e (determinantBlock (g * h)) = e (determinantBlock g) * e (determinantBlock h)
    rw [← map_mul]
    congr 1
    simp only [determinantBlock, Units.val_mul, map_mul, Matrix.fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

@[simp]
theorem determinantEmbedding_castSucc (g : GeneralLinear r R) (i j : Fin r) :
    determinantEmbedding g i.castSucc j.castSucc = g i j := by
  change (determinantBlock g).reindex finSumFinEquiv finSumFinEquiv _ _ = _
  simp [Matrix.reindex_apply, determinantBlock]

@[simp]
theorem determinantEmbedding_last (g : GeneralLinear r R) :
    determinantEmbedding g (Fin.last r) (Fin.last r) = ((GeneralLinear.determinant g)⁻¹).val := by
  change (determinantBlock g).reindex finSumFinEquiv finSumFinEquiv _ _ = _
  simp [Matrix.reindex_apply, determinantBlock, inverseDeterminantBlock, Matrix.scalar_apply]

theorem determinantEmbedding_injective :
    Function.Injective (determinantEmbedding (R := R) (r := r)) := by
  intro g h he
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simpa only [determinantEmbedding_castSucc] using
    congrArg (fun s : Matrix.SpecialLinearGroup (Fin (r + 1)) R => s i.castSucc j.castSucc) he

variable {A : Type v} [CommGroup A]

/-- The `e`-th power of a bilinear symbol evaluated on the two determinants. -/
def determinantTwist (b : Rˣ →* Rˣ →* A) (e : ℤ) : CentralTwoCocycle (GeneralLinear r R) A :=
  ((CentralTwoCocycle.ofBilinear b).pullback GeneralLinear.determinant).map (zpowGroupHom e)

@[simp]
theorem determinantTwist_apply (b : Rˣ →* Rˣ →* A) (e : ℤ) (g h : GeneralLinear r R) :
    determinantTwist b e (g, h) = b (GeneralLinear.determinant g) (GeneralLinear.determinant h) ^ e :=
  rfl

/-- Pull back an SL cocycle and multiply it by the determinant twist of exponent `e`. -/
def twistedPullbackCocycle (σ : CentralTwoCocycle (Matrix.SpecialLinearGroup (Fin (r + 1)) R) A)
    (b : Rˣ →* Rˣ →* A) (e : ℤ) : CentralTwoCocycle (GeneralLinear r R) A :=
  (σ.pullback determinantEmbedding).pointwiseMul (determinantTwist b e)

/-- The Banks–Levy–Sepanski determinant correction for an SL cocycle with symbol `b`. -/
def blsPullbackCocycle (σ : CentralTwoCocycle (Matrix.SpecialLinearGroup (Fin (r + 1)) R) A)
    (b : Rˣ →* Rˣ →* A) : CentralTwoCocycle (GeneralLinear r R) A :=
  twistedPullbackCocycle σ b (-1)

/-- In Kazhdan–Patterson coordinates the direct pullback is twisted by exponent `c + 1`. -/
def kpPullbackCocycle (σ : CentralTwoCocycle (Matrix.SpecialLinearGroup (Fin (r + 1)) R) A)
    (H : Rˣ →* Rˣ →* A) (c : ℤ) : CentralTwoCocycle (GeneralLinear r R) A :=
  twistedPullbackCocycle σ H (c + 1)

/-- The determinant normalization uses the inverse of `H` as the BLS symbol. -/
theorem kpPullbackCocycle_apply
    (σ : CentralTwoCocycle (Matrix.SpecialLinearGroup (Fin (r + 1)) R) A)
    (H : Rˣ →* Rˣ →* A) (c : ℤ) (g h : GeneralLinear r R) :
    kpPullbackCocycle σ H c (g, h) = blsPullbackCocycle σ H⁻¹ (g, h) * determinantTwist H c (g, h) := by
  simp [kpPullbackCocycle, blsPullbackCocycle, twistedPullbackCocycle, zpow_add,
    mul_assoc, mul_comm, mul_left_comm]

end Langlands.KazhdanPatterson
