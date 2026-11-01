import Langlands.Representation.RankinSelberg.TwoBlockDominantRectangleCoordinates
import Langlands.Representation.RankinSelberg.TwoBlockDominantBlockAlgebra
import Langlands.Group.GL.RankMaps
import Langlands.Representation.RankinSelberg.QuotientIntegrals
import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientData

/-! # Actual five-block matrices for JPSS Section 4.10 -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open GeneralLinear TwoBlockLowerUnipotentQuotient

universe uF

/-- Ordered five-block indices, retaining the separating singleton. -/
abbrev Coordinates (a j k b : ℕ) := Fin a ⊕ (Middle j k ⊕ Fin b)

/-- Collapse the three middle pieces in their displayed order. -/
def middleCoordinates (j k : ℕ) : Middle j k ≃ Fin (j+k+1) :=
  ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv).trans
    (finCongr (by omega))

/-- Collapse the ordered five blocks into standard finite coordinates. -/
def orderedCoordinates (a j k b : ℕ) :
    Coordinates a j k b ≃ Fin (a+((j+k+1)+b)) :=
  (Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumCongr (middleCoordinates j k) (Equiv.refl _)).trans finSumFinEquiv)).trans
      finSumFinEquiv

/-- Natural position in the displayed five-block order `(a,k,1,j,b)`. -/
def position {a j k b : ℕ} : Coordinates a j k b → ℕ
  | .inl i => i.val
  | .inr (.inl (.inl i)) => a+i.val
  | .inr (.inl (.inr (.inl i))) => a+k+i.val
  | .inr (.inl (.inr (.inr i))) => a+k+1+i.val
  | .inr (.inr i) => a+(j+k+1)+i.val

@[simp] theorem orderedCoordinates_val {a j k b : ℕ} (i : Coordinates a j k b) :
    (orderedCoordinates a j k b i).val = position i := by
  rcases i with i | ((i | (i | i)) | i) <;>
    simp [orderedCoordinates, middleCoordinates, position, Nat.add_assoc]

variable {K : Type uF} [Field K]
variable {t r j k : ℕ} {m : Fin 2 → ℕ}

/-- The total of the five displayed block sizes is the actual test rank. -/
theorem totalRank (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1)) :
    (m 0+1)+((j+k+1)+(m 1+1)) = r+1 := by
  have := TwoBlockJacquet.blockRanks_add h
  omega

/-- The rank transport from ordered blocks to the actual group coordinates. -/
def coordinates (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1)) :
    Coordinates (m 0+1) j k (m 1+1) ≃ Fin (r+1) :=
  (orderedCoordinates _ _ _ _).trans (finCongr (totalRank h hr))

@[simp] theorem coordinates_val (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1))
    (i : Coordinates (m 0+1) j k (m 1+1)) :
    (coordinates h hr i).val = position i := by
  simp [coordinates]

/-- The actual unit with rectangle blocks `x,y` and otherwise identity blocks. -/
def rectangleUnipotent (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1))
    (x : Matrix (Fin (m 0+1)) (Fin k) K)
    (y : Matrix (Fin j) (Fin (m 1+1)) K) : GeneralLinear (r+1) K :=
  reindex (coordinates h hr) (BlockAlgebra.upper (padX j x) (padY k y) (padX_mul_padY x y))

/-- All entries, including every zero off the two displayed rectangles. -/
theorem rectangleUnipotent_entry (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1))
    (x : Matrix (Fin (m 0+1)) (Fin k) K)
    (y : Matrix (Fin j) (Fin (m 1+1)) K)
    (i l : Coordinates (m 0+1) j k (m 1+1)) :
    rectangleUnipotent h hr x y (coordinates h hr i) (coordinates h hr l) =
      BlockAlgebra.three 1 (padX j x) 0 0 1 (padY k y) 0 0 1 i l := by
  change BlockAlgebra.three 1 (padX j x) 0 0 1 (padY k y) 0 0 1
    ((coordinates h hr).symm (coordinates h hr i))
    ((coordinates h hr).symm (coordinates h hr l)) = _
  simp

/-- Complete five-by-five entry table of the source rectangle matrix. -/
def rectangleEntries {a b j k : ℕ}
    (x : Matrix (Fin a) (Fin k) K) (y : Matrix (Fin j) (Fin b) K) :
    Coordinates a j k b → Coordinates a j k b → K
  | .inl i, .inl l => if i=l then 1 else 0
  | .inl i, .inr (.inl (.inl l)) => x i l
  | .inr (.inl (.inl i)), .inr (.inl (.inl l)) => if i=l then 1 else 0
  | .inr (.inl (.inr (.inl i))), .inr (.inl (.inr (.inl l))) => if i=l then 1 else 0
  | .inr (.inl (.inr (.inr i))), .inr (.inl (.inr (.inr l))) => if i=l then 1 else 0
  | .inr (.inl (.inr (.inr i))), .inr (.inr l) => y i l
  | .inr (.inr i), .inr (.inr l) => if i=l then 1 else 0
  | _, _ => 0

/-- All twenty-five blocks in the five-block order. -/
theorem rectangleUnipotent_five_entry (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1))
    (x : Matrix (Fin (m 0+1)) (Fin k) K)
    (y : Matrix (Fin j) (Fin (m 1+1)) K)
    (i l : Coordinates (m 0+1) j k (m 1+1)) :
    rectangleUnipotent h hr x y (coordinates h hr i) (coordinates h hr l) =
      rectangleEntries x y i l := by
  rw [rectangleUnipotent_entry]
  rcases i with i | ((i | (i | i)) | i) <;>
    rcases l with l | ((l | (l | l)) | l) <;>
      simp [rectangleEntries, BlockAlgebra.three, padX, padY, Matrix.one_apply]

/-- Negating both rectangles gives the actual inverse. -/
theorem rectangleUnipotent_inv (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1))
    (x : Matrix (Fin (m 0+1)) (Fin k) K)
    (y : Matrix (Fin j) (Fin (m 1+1)) K) :
    (rectangleUnipotent h hr x y)⁻¹ = rectangleUnipotent h hr (-x) (-y) := by
  rw [rectangleUnipotent, ← map_inv]
  congr 1
  apply Units.ext
  simp only [BlockAlgebra.upper_inv_val, BlockAlgebra.upper_val]
  have hx : -padX j x = padX j (-x) := by
    ext i l
    rcases l with l | (l | l) <;> simp [padX]
  have hy : -padY k y = padY k (-y) := by
    ext i l
    rcases i with i | (i | i) <;> simp [padY]
  rw [hx, hy]

/-- The actual unsigned block-Weyl matrix `diag(w_a,w_(c+b))`. -/
def blockWeyl (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1)) :
    GeneralLinear (r+1) K :=
  reindex (finCongr (totalRank h hr))
    (blockSum (weylLong (m 0+1) K, weylLong ((j+k+1)+(m 1+1)) K))

@[simp] theorem blockWeyl_mul_self (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1)) :
    blockWeyl (K := K) h hr * blockWeyl h hr = 1 := by
  unfold blockWeyl
  rw [← map_mul, ← map_mul]
  have hp : (weylLong (m 0+1) K, weylLong ((j+k+1)+(m 1+1)) K) *
      (weylLong (m 0+1) K, weylLong ((j+k+1)+(m 1+1)) K) = 1 := by
    ext <;> simp
  rw [hp, map_one, map_one]

/-- The actual rank inclusion `diag(g,I_c)` with the specified target rank. -/
def append (hr : r=t+(j+k+1)) : GeneralLinear (t+1) K →* GeneralLinear (r+1) K :=
  (reindex (finCongr (congrArg (·+1) hr.symm))).toMonoidHom.comp
    (appendIdentity t (j+k+1))

/-- The inclusion has exactly the entries of `diag(g,I_c)`. -/
theorem append_entry (hr : r=t+(j+k+1)) (g : GeneralLinear (t+1) K) (i l : Fin (r+1)) :
    append hr g i l =
      if hi : i.val < t+1 then
        if hl : l.val < t+1 then g ⟨i.val,hi⟩ ⟨l.val,hl⟩ else 0
      else if i=l then 1 else 0 := by
  change appendIdentity t (j+k+1) g
    ((finCongr (congrArg (·+1) hr.symm)).symm i)
    ((finCongr (congrArg (·+1) hr.symm)).symm l) = _
  rw [appendIdentity_entry]
  simp

/-- The actual matrix displayed in JPSS 4.10(2), printed page 419. -/
def matrix (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1))
    (g : GeneralLinear (t+1) K)
    (x : Matrix (Fin (m 0+1)) (Fin k) K)
    (y : Matrix (Fin j) (Fin (m 1+1)) K) : GeneralLinear (r+1) K :=
  weylLong (r+1) K * rectangleUnipotent h hr x y * blockWeyl h hr * append hr g

/-- Evaluation in the actual general linear group, with no abstract matrix parameter. -/
theorem matrix_eq (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1))
    (g : GeneralLinear (t+1) K)
    (x : Matrix (Fin (m 0+1)) (Fin k) K)
    (y : Matrix (Fin j) (Fin (m 1+1)) K) :
    matrix h hr g x y =
      weylLong (r+1) K * rectangleUnipotent h hr x y *
        reindex (finCongr (totalRank h hr))
          (blockSum (weylLong (m 0+1) K, weylLong ((j+k+1)+(m 1+1)) K)) *
        append hr g := rfl

/-- The actual right multiplier `diag(I_(t+1),w_c)` in 4.10(3). -/
def rightWeyl (hr : r=t+(j+k+1)) : GeneralLinear (r+1) K :=
  reindex (finCongr (by omega : (t+1)+(j+k+1)=r+1))
    (blockSum (1, weylLong (j+k+1) K))

/-- The reversed five-block matrix, reversing the complete dependent family. -/
def reversedMatrix (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1))
    (g : GeneralLinear (t+1) K)
    (x : Matrix (Fin (m 1+1)) (Fin j) K)
    (y : Matrix (Fin k) (Fin (m 0+1)) K) : GeneralLinear (r+1) K :=
  matrix (reverse_sum h) (by omega : r=t+(k+j+1)) g x y * rightWeyl hr

/-- Evaluation of the source's reversed `(b,j,1,k,a)` construction and right translation. -/
theorem reversedMatrix_eq (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1))
    (g : GeneralLinear (t+1) K)
    (x : Matrix (Fin (m 1+1)) (Fin j) K)
    (y : Matrix (Fin k) (Fin (m 0+1)) K) :
    reversedMatrix h hr g x y =
      matrix (m := fun i => m i.rev) (reverse_sum h)
        (by omega : r=t+(k+j+1)) g x y * rightWeyl hr := rfl

/-- The actual reversed lower-left block `w_b Z w_a`, evaluated entrywise. -/
def crossMultiplier (h : ∑ i, (m i+1) = t+1) (u : lowerBlockUnipotent h K) :
    Matrix (Fin (m 1+1)) (Fin (m 0+1)) K :=
  (TwoBlockLowerFirstBlockQuotient.entryBlock h K u.val 1 0).submatrix Fin.rev Fin.rev

@[simp] theorem crossMultiplier_apply (h : ∑ i, (m i+1) = t+1)
    (u : lowerBlockUnipotent h K) (i : Fin (m 1+1)) (l : Fin (m 0+1)) :
    crossMultiplier h u i l =
      u.val ((succBlockShape m h).index 1 i.rev) ((succBlockShape m h).index 0 l.rev) := rfl

/-- The entry definition is exactly the rectangular unsigned Weyl conjugation. -/
theorem crossMultiplier_eq (h : ∑ i, (m i+1) = t+1) (u : lowerBlockUnipotent h K) :
    crossMultiplier h u = (weylLong (m 1+1) K).val *
      TwoBlockLowerFirstBlockQuotient.entryBlock h K u.val 1 0 * (weylLong (m 0+1) K).val := by
  ext i l
  change _ = (((Fin.revPerm⁻¹).toPEquiv.toMatrix : Matrix (Fin (m 1+1)) (Fin (m 1+1)) K) *
    TwoBlockLowerFirstBlockQuotient.entryBlock h K u.val 1 0 *
      ((Fin.revPerm⁻¹).toPEquiv.toMatrix : Matrix (Fin (m 0+1)) (Fin (m 0+1)) K)) i l
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

/-- Actual residual matrix on standard test-group coordinates, before long-Weyl conjugation. -/
def residualMatrix (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1))
    (u : lowerBlockUnipotent h K)
    (x : Matrix (Fin (m 0+1)) (Fin k) K)
    (y : Matrix (Fin j) (Fin (m 1+1)) K) : GeneralLinear (r+1) K :=
  reindex (coordinates h hr)
    (BlockAlgebra.residual (leftMultiplier h u) (rightMultiplier h u) (crossMultiplier h u)
      (padX j x) (padY k y) (padX_mul_padY x y))

/-- Exact residual entry formula in the ordered `(a,c,b)` coordinates. -/
theorem residualMatrix_entry (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1))
    (u : lowerBlockUnipotent h K)
    (x : Matrix (Fin (m 0+1)) (Fin k) K)
    (y : Matrix (Fin j) (Fin (m 1+1)) K)
    (i l : Coordinates (m 0+1) j k (m 1+1)) :
    residualMatrix h hr u x y (coordinates h hr i) (coordinates h hr l) =
      BlockAlgebra.three (leftMultiplier h u).val 0 0
        (padY k y * crossMultiplier h u)
        (1-padY k y * crossMultiplier h u * (((leftMultiplier h u)⁻¹).val * padX j x)) 0
        (crossMultiplier h u) (-crossMultiplier h u * (((leftMultiplier h u)⁻¹).val * padX j x))
        (rightMultiplier h u).val i l := by
  change (BlockAlgebra.residual _ _ _ _ _ _).val
    ((coordinates h hr).symm (coordinates h hr i))
    ((coordinates h hr).symm (coordinates h hr l)) = _
  simp only [Equiv.symm_apply_apply, BlockAlgebra.residual_val]

end Langlands.RankinSelberg.TwoBlockDominantRectangular
