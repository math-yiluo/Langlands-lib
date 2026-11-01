import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientData
import Langlands.Representation.RankinSelberg.TwoBlockLowerUnipotentQuotientData
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Langlands.LocalField.Normalization.Continuity

/-!
# The lower mixed quotient and its two fiber averages

Derived data for JPSS (1983), Section 4.9, equations (2) and (8).
-/

noncomputable section

open MeasureTheory

namespace Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient

open GeneralLinear TwoBlockJacquet TwoBlockDeformation QuotientIntegration
open TwoBlockFirstBlockQuotient TwoBlockLowerUnipotentQuotient

universe uF uR

section Algebra

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable (R : Type uR) [CommRing R]

/-- The actual rectangular block, in the published block coordinates. -/
def entryBlock (g : GeneralLinear (t + 1) R) (i j : Fin 2) :
    Matrix (Fin (m i + 1)) (Fin (m j + 1)) R :=
  (g : Matrix (Fin (t + 1)) (Fin (t + 1)) R).submatrix
    ((succBlockShape m h).index i) ((succBlockShape m h).index j)

theorem entryBlock_mul (g g' : GeneralLinear (t + 1) R) (i j : Fin 2) :
    entryBlock h R (g * g') i j =
      entryBlock h R g i 0 * entryBlock h R g' 0 j +
        entryBlock h R g i 1 * entryBlock h R g' 1 j := by
  ext a b
  exact mul_apply_index h g g' _ _

theorem ext_entryBlock {g g' : GeneralLinear (t + 1) R}
    (h00 : entryBlock h R g 0 0 = entryBlock h R g' 0 0)
    (h01 : entryBlock h R g 0 1 = entryBlock h R g' 0 1)
    (h10 : entryBlock h R g 1 0 = entryBlock h R g' 1 0)
    (h11 : entryBlock h R g 1 1 = entryBlock h R g' 1 1) : g = g' :=
  ext_index h (congrFun₂ h00) (congrFun₂ h01) (congrFun₂ h10) (congrFun₂ h11)

@[simp]
theorem entryBlock_lowerRadical_zero_zero
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R) :
    entryBlock h R (lowerRadical h R Z) 0 0 = 1 := by
  ext a b
  exact lowerRadical_index_zero_zero h R Z a b

@[simp]
theorem entryBlock_lowerRadical_zero_one
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R) :
    entryBlock h R (lowerRadical h R Z) 0 1 = 0 := by
  ext a b
  exact lowerRadical_index_zero_one h R Z a b

@[simp]
theorem entryBlock_lowerRadical_one_zero
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R) :
    entryBlock h R (lowerRadical h R Z) 1 0 = Z := by
  ext a b
  exact lowerRadical_index_one_zero h R Z a b

@[simp]
theorem entryBlock_lowerRadical_one_one
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R) :
    entryBlock h R (lowerRadical h R Z) 1 1 = 1 := by
  ext a b
  exact lowerRadical_index_one_one h R Z a b

@[simp]
theorem entryBlock_levi_zero_zero (u : GeneralLinear (m 0 + 1) R)
    (w : GeneralLinear (m 1 + 1) R) :
    entryBlock h R ((succBlockShape m h).leviEmbedding R (blockPair R (u, w))) 0 0 =
      (u : Matrix _ _ R) := by
  ext a b
  simpa only [entryBlock, Matrix.submatrix_apply, blockPair_apply_zero] using
    (succBlockShape m h).leviEmbedding_apply_same R (blockPair R (u, w)) 0 a b

@[simp]
theorem entryBlock_levi_zero_one (u : GeneralLinear (m 0 + 1) R)
    (w : GeneralLinear (m 1 + 1) R) :
    entryBlock h R ((succBlockShape m h).leviEmbedding R (blockPair R (u, w))) 0 1 = 0 := by
  ext a b
  exact leviEmbedding_index_zero_one h _ a b

@[simp]
theorem entryBlock_levi_one_zero (u : GeneralLinear (m 0 + 1) R)
    (w : GeneralLinear (m 1 + 1) R) :
    entryBlock h R ((succBlockShape m h).leviEmbedding R (blockPair R (u, w))) 1 0 = 0 := by
  ext a b
  exact leviEmbedding_index_one_zero h _ a b

@[simp]
theorem entryBlock_levi_one_one (u : GeneralLinear (m 0 + 1) R)
    (w : GeneralLinear (m 1 + 1) R) :
    entryBlock h R ((succBlockShape m h).leviEmbedding R (blockPair R (u, w))) 1 1 =
      (w : Matrix _ _ R) := by
  ext a b
  simpa only [entryBlock, Matrix.submatrix_apply, blockPair_apply_one] using
    (succBlockShape m h).leviEmbedding_apply_same R (blockPair R (u, w)) 1 a b

/-- The lower triangular matrix with radical coordinate `Z` and diagonal blocks `u,w`.
Its lower-left block is `Z * u`. -/
def lowerProduct (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R)
    (u : GeneralLinear (m 0 + 1) R) (w : GeneralLinear (m 1 + 1) R) :
    GeneralLinear (t + 1) R :=
  lowerRadical h R Z * (succBlockShape m h).leviEmbedding R (blockPair R (u, w))

@[simp]
theorem entryBlock_lowerProduct_zero_zero
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R)
    (u : GeneralLinear (m 0 + 1) R) (w : GeneralLinear (m 1 + 1) R) :
    entryBlock h R (lowerProduct h R Z u w) 0 0 = (u : Matrix _ _ R) := by
  simp [lowerProduct, entryBlock_mul]

@[simp]
theorem entryBlock_lowerProduct_zero_one
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R)
    (u : GeneralLinear (m 0 + 1) R) (w : GeneralLinear (m 1 + 1) R) :
    entryBlock h R (lowerProduct h R Z u w) 0 1 = 0 := by
  simp [lowerProduct, entryBlock_mul]

@[simp]
theorem entryBlock_lowerProduct_one_zero
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R)
    (u : GeneralLinear (m 0 + 1) R) (w : GeneralLinear (m 1 + 1) R) :
    entryBlock h R (lowerProduct h R Z u w) 1 0 = Z * (u : Matrix _ _ R) := by
  simp [lowerProduct, entryBlock_mul]

@[simp]
theorem entryBlock_lowerProduct_one_one
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R)
    (u : GeneralLinear (m 0 + 1) R) (w : GeneralLinear (m 1 + 1) R) :
    entryBlock h R (lowerProduct h R Z u w) 1 1 = (w : Matrix _ _ R) := by
  simp [lowerProduct, entryBlock_mul]

@[simp]
theorem lowerRadical_zero : lowerRadical (m := m) h R 0 = 1 := by
  simpa [lowerRadical] using reverseMatrix_mul_blockRotation h R

theorem lowerRadical_add (Z Z' : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R) :
    lowerRadical h R (Z + Z') = lowerRadical h R Z * lowerRadical h R Z' := by
  apply ext_entryBlock h R <;> simp [entryBlock_mul]

theorem lowerProduct_mul
    (Z Z' : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R)
    (u u' : GeneralLinear (m 0 + 1) R) (w w' : GeneralLinear (m 1 + 1) R) :
    lowerProduct h R Z u w * lowerProduct h R Z' u' w' =
      lowerProduct h R (Z + w.val * Z' * (u⁻¹).val)
        (u * u') (w * w') := by
  apply ext_entryBlock h R
  · simp [entryBlock_mul]
  · simp [entryBlock_mul]
  · simp [entryBlock_mul, Matrix.add_mul, Matrix.mul_assoc]
  · simp [entryBlock_mul]

theorem lowerProduct_inv
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R)
    (u : GeneralLinear (m 0 + 1) R) (w : GeneralLinear (m 1 + 1) R) :
    (lowerProduct h R Z u w)⁻¹ =
      lowerProduct h R (-(w⁻¹ : GeneralLinear _ R).val * Z * u.val) u⁻¹ w⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [lowerProduct_mul]
  simp [← Matrix.mul_assoc, lowerProduct]
  change ((succBlockShape m h).leviEmbedding R) ((blockPair R) 1) = 1
  simp

theorem mem_oppositeParabolic_of_entryBlock (g : GeneralLinear (t + 1) R)
    (hg : entryBlock h R g 0 1 = 0) :
    g ∈ (succBlockShape m h).oppositeParabolic R := by
  rw [BlockShape.mem_oppositeParabolic_iff]
  intro i j a b hij
  fin_cases i <;> fin_cases j
  · exact absurd hij (lt_irrefl _)
  · exact congrFun₂ hg a b
  · exact absurd hij (show ¬ (1 : Fin 2) < 0 by decide)
  · exact absurd hij (lt_irrefl _)

theorem oppositeParabolic_factorization (g : (succBlockShape m h).oppositeParabolic R) :
    lowerProduct h R
      (entryBlock h R g.val 1 0 *
        (((succBlockShape m h).oppositeLeviProjection R g 0)⁻¹).val)
      ((succBlockShape m h).oppositeLeviProjection R g 0)
      ((succBlockShape m h).oppositeLeviProjection R g 1) = g.val := by
  have h01 : entryBlock h R g.val 0 1 = 0 := by
    ext a b
    exact ((succBlockShape m h).mem_oppositeParabolic_iff R g.val).mp g.property
      0 1 a b (show (0 : Fin 2) < 1 by decide)
  apply ext_entryBlock h R
  · simp only [entryBlock_lowerProduct_zero_zero]; rfl
  · simp only [entryBlock_lowerProduct_zero_one]; exact h01.symm
  · simp only [entryBlock_lowerProduct_one_zero, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]
  · simp only [entryBlock_lowerProduct_one_one]; rfl

theorem continuous_lowerRadical [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (lowerRadical (m := m) h R) :=
  (continuous_const.mul (continuous_upperRadical (reverse_sum h) R)).mul continuous_const

theorem continuous_entryBlock [TopologicalSpace R] (i j : Fin 2) :
    Continuous (fun g : GeneralLinear (t + 1) R => entryBlock h R g i j) := by
  apply continuous_matrix
  intro a b
  exact (GeneralLinear.entry (R := R) _ _).continuous

@[simp]
theorem lowerProduct_zero (u : GeneralLinear (m 0 + 1) R)
    (w : GeneralLinear (m 1 + 1) R) :
    lowerProduct h R 0 u w =
      (succBlockShape m h).leviEmbedding R (blockPair R (u, w)) := by
  simp [lowerProduct]

@[simp]
theorem lowerProduct_one : lowerProduct (m := m) h R 0 1 1 = 1 := by
  rw [lowerProduct_zero]
  change ((succBlockShape m h).leviEmbedding R) ((blockPair R) 1) = 1
  simp

@[simp]
theorem determinant_lowerRadical
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R) :
    GeneralLinear.determinant (lowerRadical h R Z) = 1 :=
  determinant_eq_one_of_mem_lowerBlockUnipotent h R (lowerRadical_mem h R Z)

theorem continuous_lowerProduct [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (fun x : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R ×
        (GeneralLinear (m 0 + 1) R × GeneralLinear (m 1 + 1) R) =>
      lowerProduct h R x.1 x.2.1 x.2.2) :=
  ((continuous_lowerRadical h R).comp continuous_fst).mul
    (((succBlockShape m h).leviEmbeddingContinuous R).continuous.comp
      ((continuous_blockPair R).comp continuous_snd))

end Algebra

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The actual lower mixed subgroup: `R(Z) diag(a0,n)` with `|det a0| = 1` and
`n` upper unipotent. The lower-left block is unrestricted. -/
def lowerMixedSubgroup : Subgroup (GeneralLinear (t + 1) F.Carrier) where
  carrier := {g | ∃ (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier),
    lowerProduct h F.Carrier Z x.1.val x.2.val = g}
  one_mem' := ⟨0, 1, lowerProduct_one h F.Carrier⟩
  mul_mem' := by
    rintro _ _ ⟨Z, x, rfl⟩ ⟨Z', x', rfl⟩
    exact ⟨Z + x.2.val.val * Z' * (x.1.val⁻¹).val, x * x',
      (lowerProduct_mul h F.Carrier Z Z' x.1.val x'.1.val x.2.val x'.2.val).symm⟩
  inv_mem' := by
    rintro _ ⟨Z, x, rfl⟩
    exact ⟨-(x.2.val⁻¹).val * Z * x.1.val.val, x⁻¹,
      (lowerProduct_inv h F.Carrier Z x.1.val x.2.val).symm⟩

theorem lowerProduct_mem
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier) :
    lowerProduct h F.Carrier Z x.1.val x.2.val ∈ lowerMixedSubgroup F h :=
  ⟨Z, x, rfl⟩

/-- Elimination into the actual lower radical and the published mixed embedding. -/
theorem lowerMixed_decomposition {g : GeneralLinear (t + 1) F.Carrier}
    (hg : g ∈ lowerMixedSubgroup F h) :
    ∃ (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
      (a0 : normOneSubgroup F (m 0 + 1)) (n : upperUnipotent (m 1 + 1) F.Carrier),
      lowerRadical h F.Carrier Z * mixedEmbedding F h (a0, n) = g := by
  rcases hg with ⟨Z, x, hx⟩
  exact ⟨Z, x.1, x.2, hx⟩

/-- Intrinsic block criterion, using actual entries and the normalized absolute value
of the first diagonal determinant. Invertibility is supplied by the opposite Levi projection. -/
theorem mem_lowerMixedSubgroup_iff (g : GeneralLinear (t + 1) F.Carrier) :
    g ∈ lowerMixedSubgroup F h ↔
      entryBlock h F.Carrier g 0 1 = 0 ∧
      F.canonicalTopologicalData.normalizedAbs (entryBlock h F.Carrier g 0 0).det = 1 ∧
      (∀ (a b : Fin (m 1 + 1)), b < a → entryBlock h F.Carrier g 1 1 a b = 0) ∧
      (∀ a : Fin (m 1 + 1), entryBlock h F.Carrier g 1 1 a a = 1) := by
  constructor
  · rintro ⟨Z, x, rfl⟩
    refine ⟨entryBlock_lowerProduct_zero_one h F.Carrier Z x.1.val x.2.val, ?_, ?_, ?_⟩
    · rw [entryBlock_lowerProduct_zero_zero]
      exact (mem_normOneSubgroup_iff_normalizedAbs F x.1.val).mp x.1.property
    · intro a b hab
      rw [entryBlock_lowerProduct_one_one]
      exact UpperUnipotent.entry_eq_zero x.2 hab
    · intro a
      rw [entryBlock_lowerProduct_one_one]
      exact UpperUnipotent.entry_diag x.2 a
  · rintro ⟨h01, hdet, hlow, hdiag⟩
    let gp : (succBlockShape m h).oppositeParabolic F.Carrier :=
      ⟨g, mem_oppositeParabolic_of_entryBlock h F.Carrier g h01⟩
    let L := (succBlockShape m h).oppositeLeviProjection F.Carrier gp
    have hL0 : L 0 ∈ normOneSubgroup F (m 0 + 1) :=
      (mem_normOneSubgroup_iff_normalizedAbs F (L 0)).mpr hdet
    have hL1 : L 1 ∈ upperUnipotent (m 1 + 1) F.Carrier := ⟨hlow, hdiag⟩
    exact ⟨entryBlock h F.Carrier g 1 0 * ((L 0)⁻¹).val,
      (⟨L 0, hL0⟩, ⟨L 1, hL1⟩), oppositeParabolic_factorization h F.Carrier gp⟩

theorem mixedSubgroup_le_lowerMixedSubgroup : mixedSubgroup F h ≤ lowerMixedSubgroup F h := by
  rintro _ ⟨x, rfl⟩
  exact ⟨0, x, lowerProduct_zero h F.Carrier x.1.val x.2.val⟩

theorem lowerBlockUnipotent_le_lowerMixedSubgroup :
    lowerBlockUnipotent h F.Carrier ≤ lowerMixedSubgroup F h := by
  intro g hg
  have hc := (mem_lowerBlockUnipotent_iff h F.Carrier g).mp hg
  apply (mem_lowerMixedSubgroup_iff F h g).mpr
  refine ⟨?_, ?_, hc.2.1 1, hc.2.2 1⟩
  · ext a b
    exact hc.1 a b
  · let n := diagonalBlocks h F.Carrier ⟨g, hg⟩ 0
    exact (mem_normOneSubgroup_iff_normalizedAbs F n.val).mp
      (determinantNorm_eq_one_of_mem_upperUnipotent F F.canonicalTopologicalData n.property)

theorem lowerMixedSubgroup_le_oppositeParabolic :
    lowerMixedSubgroup F h ≤ (succBlockShape m h).oppositeParabolic F.Carrier := by
  intro g hg
  exact mem_oppositeParabolic_of_entryBlock h F.Carrier g
    ((mem_lowerMixedSubgroup_iff F h g).mp hg).1

theorem lowerMixedSubgroup_le_normOneSubgroup :
    lowerMixedSubgroup F h ≤ normOneSubgroup F (t + 1) := by
  rintro _ ⟨Z, x, rfl⟩
  change F.canonicalTopologicalData.normalizedAbsUnits
    (GeneralLinear.determinant (lowerProduct h F.Carrier Z x.1.val x.2.val)) = 1
  change F.canonicalTopologicalData.normalizedAbsUnits
    (GeneralLinear.determinant (lowerRadical h F.Carrier Z * mixedEmbedding F h x)) = 1
  rw [map_mul, determinant_lowerRadical, one_mul, determinant_mixedEmbedding]
  exact x.1.property

/-- The first diagonal block is invertible, with its actual inverse extracted by the
opposite Levi projection; its determinant has absolute value one. -/
def lowerMixedDiagonal (g : lowerMixedSubgroup F h) :
    normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier :=
  (⟨(succBlockShape m h).oppositeLeviProjection F.Carrier
      ⟨g.val, lowerMixedSubgroup_le_oppositeParabolic F h g.property⟩ 0,
    (mem_normOneSubgroup_iff_normalizedAbs F _).mpr
      ((mem_lowerMixedSubgroup_iff F h g.val).mp g.property).2.1⟩,
   ⟨(succBlockShape m h).oppositeLeviProjection F.Carrier
      ⟨g.val, lowerMixedSubgroup_le_oppositeParabolic F h g.property⟩ 1,
    ⟨((mem_lowerMixedSubgroup_iff F h g.val).mp g.property).2.2.1,
      ((mem_lowerMixedSubgroup_iff F h g.val).mp g.property).2.2.2⟩⟩)

@[simp]
theorem lowerMixedDiagonal_fst_val (g : lowerMixedSubgroup F h) :
    (lowerMixedDiagonal F h g).1.val.val = entryBlock h F.Carrier g.val 0 0 := rfl

@[simp]
theorem lowerMixedDiagonal_snd_val (g : lowerMixedSubgroup F h) :
    (lowerMixedDiagonal F h g).2.val.val = entryBlock h F.Carrier g.val 1 1 := rfl

/-- Coordinates `(X * a0⁻¹, (a0,n))` of the actual block matrix `[[a0,0],[X,n]]`. -/
def lowerMixedCoordinates (g : lowerMixedSubgroup F h) :
    Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier ×
      (normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier) :=
  (entryBlock h F.Carrier g.val 1 0 * ((lowerMixedDiagonal F h g).1.val⁻¹).val,
    lowerMixedDiagonal F h g)

@[simp]
theorem lowerMixedDiagonal_lowerProduct
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier) :
    lowerMixedDiagonal F h ⟨lowerProduct h F.Carrier Z x.1.val x.2.val,
      lowerProduct_mem F h Z x⟩ = x := by
  refine Prod.ext (Subtype.ext (Matrix.GeneralLinearGroup.ext fun a b => ?_))
    (Subtype.ext (Matrix.GeneralLinearGroup.ext fun a b => ?_))
  · exact congrFun₂ (entryBlock_lowerProduct_zero_zero h F.Carrier Z x.1.val x.2.val) a b
  · exact congrFun₂ (entryBlock_lowerProduct_one_one h F.Carrier Z x.1.val x.2.val) a b

@[simp]
theorem lowerMixedCoordinates_lowerProduct
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (x : normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier) :
    lowerMixedCoordinates F h ⟨lowerProduct h F.Carrier Z x.1.val x.2.val,
      lowerProduct_mem F h Z x⟩ = (Z, x) := by
  simp [lowerMixedCoordinates, Matrix.mul_assoc]

/-- Reconstructing from the coordinates returns the original matrix. -/
theorem lowerProduct_lowerMixedCoordinates (g : lowerMixedSubgroup F h) :
    lowerProduct h F.Carrier (lowerMixedCoordinates F h g).1
      (lowerMixedCoordinates F h g).2.1.val (lowerMixedCoordinates F h g).2.2.val = g.val :=
  oppositeParabolic_factorization h F.Carrier
    ⟨g.val, lowerMixedSubgroup_le_oppositeParabolic F h g.property⟩

/-- The coordinate equivalence, before topology. Its domain is given the semidirect
multiplication stated below, rather than the product group multiplication. -/
def lowerMixedSubgroupEquiv :
    Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier ×
      (normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier) ≃
        lowerMixedSubgroup F h where
  toFun x := ⟨lowerProduct h F.Carrier x.1 x.2.1.val x.2.2.val, lowerProduct_mem F h x.1 x.2⟩
  invFun := lowerMixedCoordinates F h
  left_inv x := lowerMixedCoordinates_lowerProduct F h x.1 x.2
  right_inv g := Subtype.ext (lowerProduct_lowerMixedCoordinates F h g)

@[simp]
theorem lowerMixedSubgroupEquiv_apply_val
    (x : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier ×
      (normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier)) :
    (lowerMixedSubgroupEquiv F h x).val = lowerRadical h F.Carrier x.1 * mixedEmbedding F h x.2 :=
  rfl

/-- The coordinate equivalence is a homeomorphism in the canonical topology. -/
def lowerMixedSubgroupHomeomorph :
    letI := F.canonicalTopologicalData.topology
    Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier ×
      (normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier) ≃ₜ
        lowerMixedSubgroup F h := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hd : Continuous (lowerMixedDiagonal F h) := by
    have hp : Continuous (fun g : lowerMixedSubgroup F h =>
        (succBlockShape m h).oppositeLeviProjection F.Carrier
          ⟨g.val, lowerMixedSubgroup_le_oppositeParabolic F h g.property⟩) :=
      ((succBlockShape m h).oppositeLeviProjectionContinuous F.Carrier).continuous.comp
        (continuous_subtype_val.subtype_mk _)
    exact (((continuous_apply 0).comp hp).subtype_mk _).prodMk
      (((continuous_apply 1).comp hp).subtype_mk _)
  refine
    { toEquiv := lowerMixedSubgroupEquiv F h
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · exact ((continuous_lowerProduct h F.Carrier).comp
      (continuous_fst.prodMk
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
          (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))))).subtype_mk _
  · exact (((continuous_entryBlock h F.Carrier 1 0).comp continuous_subtype_val).matrix_mul
      (Units.continuous_val.comp
        ((continuous_subtype_val.comp (continuous_fst.comp hd)).inv))).prodMk hd

/-- Closedness follows from the actual upper-right block, first determinant and
upper-unipotent second block conditions. -/
theorem isClosed_lowerMixedSubgroup :
    letI := F.canonicalTopologicalData.topology
    IsClosed (lowerMixedSubgroup F h : Set (GeneralLinear (t + 1) F.Carrier)) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  have he : (lowerMixedSubgroup F h : Set (GeneralLinear (t + 1) F.Carrier)) =
      {g | entryBlock h F.Carrier g 0 1 = 0} ∩
      ({g | T.normalizedAbs (entryBlock h F.Carrier g 0 0).det = 1} ∩
      ((⋂ (a : Fin (m 1 + 1)) (b : Fin (m 1 + 1)) (_ : b < a),
        {g | entryBlock h F.Carrier g 1 1 a b = 0}) ∩
      (⋂ (a : Fin (m 1 + 1)), {g | entryBlock h F.Carrier g 1 1 a a = 1}))) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    exact mem_lowerMixedSubgroup_iff F h g
  have hentry : ∀ (a b : Fin (m 1 + 1)) (c : F.Carrier),
      IsClosed {g : GeneralLinear (t + 1) F.Carrier | entryBlock h F.Carrier g 1 1 a b = c} :=
    fun a b c => isClosed_eq (GeneralLinear.entry (R := F.Carrier) _ _).continuous continuous_const
  rw [he]
  exact (isClosed_eq (continuous_entryBlock h F.Carrier 0 1) continuous_const).inter
    ((isClosed_eq (T.continuous_normalizedAbs.comp
      (continuous_entryBlock h F.Carrier 0 0).matrix_det) continuous_const).inter
      ((isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ =>
        hentry a b 0).inter (isClosed_iInter fun a => hentry a a 1)))

/-- The inverse coordinate on the rectangle is exactly `X * a0⁻¹`. -/
theorem lowerMixedSubgroupEquiv_symm_apply_radical (g : lowerMixedSubgroup F h) :
    ((lowerMixedSubgroupEquiv F h).symm g).1 =
      entryBlock h F.Carrier g.val 1 0 * ((lowerMixedDiagonal F h g).1.val⁻¹).val := rfl

/-- The first inverse diagonal coordinate is the actual first entry block. -/
theorem lowerMixedSubgroupEquiv_symm_apply_fst (g : lowerMixedSubgroup F h) :
    ((lowerMixedSubgroupEquiv F h).symm g).2.1.val.val =
      entryBlock h F.Carrier g.val 0 0 := rfl

/-- The second inverse diagonal coordinate is the actual second entry block. -/
theorem lowerMixedSubgroupEquiv_symm_apply_snd (g : lowerMixedSubgroup F h) :
    ((lowerMixedSubgroupEquiv F h).symm g).2.2.val.val =
      entryBlock h F.Carrier g.val 1 1 := rfl

/-- Coordinate multiplication is semidirect: `Z + n Z2 a0⁻¹` on the rectangle. -/
theorem lowerMixedSubgroupEquiv_mul
    (x y : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier ×
      (normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier)) :
    lowerMixedSubgroupEquiv F h x * lowerMixedSubgroupEquiv F h y =
      lowerMixedSubgroupEquiv F h
        (x.1 + x.2.2.val.val * y.1 * (x.2.1.val⁻¹).val, x.2 * y.2) :=
  Subtype.ext (lowerProduct_mul h F.Carrier x.1 y.1 x.2.1.val y.2.1.val x.2.2.val y.2.2.val)

/-- Coordinate inversion is `(-n⁻¹ Z a0, a0⁻¹, n⁻¹)`. -/
theorem lowerMixedSubgroupEquiv_inv
    (x : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier ×
      (normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier)) :
    (lowerMixedSubgroupEquiv F h x)⁻¹ =
      lowerMixedSubgroupEquiv F h (-(x.2.2.val⁻¹).val * x.1 * x.2.1.val.val, x.2⁻¹) :=
  Subtype.ext (lowerProduct_inv h F.Carrier x.1 x.2.1.val x.2.2.val)

theorem isUnit_entryBlock_zero_zero (g : lowerMixedSubgroup F h) :
    IsUnit (entryBlock h F.Carrier g.val 0 0) :=
  (lowerMixedDiagonal F h g).1.val.isUnit

/-- The actual left quotient by the lower mixed subgroup. -/
abbrev LowerMixedQuotient := LeftQuotient (lowerMixedSubgroup F h)

/-- Projection from the published diagonal mixed quotient, by actual quotient descent. -/
def projectionFromMixed : MixedQuotient F h → LowerMixedQuotient F h :=
  descend _ (fun g => (Quotient.mk _ g : LowerMixedQuotient F h))
    (fun u g => TwoBlockUnipotentQuotient.mk_mul_of_mem _
      (mixedSubgroup_le_lowerMixedSubgroup F h u.property) g)

/-- Projection from the published lower unipotent quotient, by actual quotient descent. -/
def projectionFromLower : LowerQuotient h F.Carrier → LowerMixedQuotient F h :=
  descend _ (fun g => (Quotient.mk _ g : LowerMixedQuotient F h))
    (fun u g => TwoBlockUnipotentQuotient.mk_mul_of_mem _
      (lowerBlockUnipotent_le_lowerMixedSubgroup F h u.property) g)

@[simp]
theorem projectionFromMixed_mk (g : GeneralLinear (t + 1) F.Carrier) :
    projectionFromMixed F h (Quotient.mk _ g) = Quotient.mk _ g := rfl

@[simp]
theorem projectionFromLower_mk (g : GeneralLinear (t + 1) F.Carrier) :
    projectionFromLower F h (Quotient.mk _ g) = Quotient.mk _ g := rfl

theorem projectionFromMixed_surjective : Function.Surjective (projectionFromMixed F h) := by
  intro q
  induction q using Quotient.inductionOn with
  | h g => exact ⟨Quotient.mk _ g, rfl⟩

theorem projectionFromLower_surjective : Function.Surjective (projectionFromLower F h) := by
  intro q
  induction q using Quotient.inductionOn with
  | h g => exact ⟨Quotient.mk _ g, rfl⟩

theorem continuous_projectionFromMixed :
    letI := F.canonicalTopologicalData.topology
    Continuous (projectionFromMixed F h) := by
  let := F.canonicalTopologicalData.topology
  exact Continuous.quotient_lift continuous_quotient_mk' _

theorem continuous_projectionFromLower :
    letI := F.canonicalTopologicalData.topology
    Continuous (projectionFromLower F h) := by
  let := F.canonicalTopologicalData.topology
  exact Continuous.quotient_lift continuous_quotient_mk' _

theorem projectionFromMixed_rightTranslate :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    ∀ (g : GeneralLinear (t + 1) F.Carrier) (q : MixedQuotient F h),
      projectionFromMixed F h (rightTranslate _ g q) =
        rightTranslate _ g (projectionFromMixed F h q) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro g q
  induction q using Quotient.inductionOn with
  | h x => rfl

theorem projectionFromLower_rightTranslate :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    ∀ (g : GeneralLinear (t + 1) F.Carrier) (q : LowerQuotient h F.Carrier),
      projectionFromLower F h (rightTranslate _ g q) =
        rightTranslate _ g (projectionFromLower F h q) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro g q
  induction q using Quotient.inductionOn with
  | h x => rfl

/-- Closedness of the actual subgroup makes the lower mixed quotient Hausdorff. -/
theorem t2Space_lowerMixedQuotient :
    letI := F.canonicalTopologicalData.topology
    T2Space (LowerMixedQuotient F h) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  exact leftQuotient_t2Space _ (isClosed_lowerMixedSubgroup F h)

/-- The determinant order descends because the lower mixed subgroup lies in `GL^0`. -/
def determinantOrder : LowerMixedQuotient F h → ℤ :=
  descend _
    (fun g => F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier))
    (fun l g => by
      rw [map_mul, Units.val_mul,
        F.canonicalTopologicalData.ord_mul (GeneralLinear.determinant l.val).ne_zero
          (GeneralLinear.determinant g).ne_zero,
        ord_determinant_eq_zero F (lowerMixedSubgroup_le_normOneSubgroup F h l.property), zero_add])

@[simp]
theorem determinantOrder_mk (g : GeneralLinear (t + 1) F.Carrier) :
    determinantOrder F h (Quotient.mk _ g) =
      F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) := rfl

theorem continuous_determinantOrder :
    letI := F.canonicalTopologicalData.topology
    Continuous (determinantOrder F h) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  exact Continuous.quotient_lift
    ((continuous_ord_units T).comp (T.generalLinearDeterminant (t + 1)).continuous) _

/-- Integer determinant slices. The source's `Lminus \ G^0` is precisely slice zero. -/
def determinantSlice (k : ℤ) : Set (LowerMixedQuotient F h) :=
  {q | determinantOrder F h q = k}

theorem mem_determinantSlice {k : ℤ} {q : LowerMixedQuotient F h} :
    q ∈ determinantSlice F h k ↔ determinantOrder F h q = k := Iff.rfl

theorem mk_mem_determinantSlice {k : ℤ} {g : GeneralLinear (t + 1) F.Carrier} :
    (Quotient.mk _ g : LowerMixedQuotient F h) ∈ determinantSlice F h k ↔
      F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) = k := Iff.rfl

theorem isClopen_determinantSlice (k : ℤ) :
    letI := F.canonicalTopologicalData.topology
    IsClopen (determinantSlice F h k) := by
  let := F.canonicalTopologicalData.topology
  exact (isClopen_discrete ({k} : Set ℤ)).preimage (continuous_determinantOrder F h)

theorem measurableSet_determinantSlice (k : ℤ) :
    letI := F.canonicalTopologicalData.topology
    ∀ [MeasurableSpace (LowerMixedQuotient F h)] [BorelSpace (LowerMixedQuotient F h)],
      MeasurableSet (determinantSlice F h k) := by
  let := F.canonicalTopologicalData.topology
  intro _ _
  exact (isClopen_determinantSlice F h k).isOpen.measurableSet

theorem disjoint_determinantSlice {k l : ℤ} (hkl : k ≠ l) :
    Disjoint (determinantSlice F h k) (determinantSlice F h l) := by
  apply Set.disjoint_left.mpr
  intro q hqk hql
  exact hkl (hqk.symm.trans hql)

theorem pairwise_disjoint_determinantSlice :
    Pairwise (Function.onFun Disjoint (determinantSlice F h)) :=
  fun _ _ hkl => disjoint_determinantSlice F h hkl

@[simp]
theorem iUnion_determinantSlice : ⋃ k, determinantSlice F h k = Set.univ := by
  ext q
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨determinantOrder F h q, rfl⟩

/-- Both projections preserve the determinant order. -/
@[simp]
theorem determinantOrder_projectionFromMixed (q : MixedQuotient F h) :
    determinantOrder F h (projectionFromMixed F h q) =
      TwoBlockFirstBlockQuotient.determinantOrder F h q := by
  induction q using Quotient.inductionOn with
  | h g => rfl

@[simp]
theorem determinantOrder_projectionFromLower (q : LowerQuotient h F.Carrier) :
    determinantOrder F h (projectionFromLower F h q) =
      TwoBlockLowerUnipotentQuotient.determinantOrder F h q := by
  induction q using Quotient.inductionOn with
  | h g => exact (TwoBlockLowerUnipotentQuotient.determinantOrder_mk F h g).symm

theorem projectionFromMixed_preimage_determinantSlice (k : ℤ) :
    projectionFromMixed F h ⁻¹' determinantSlice F h k =
      TwoBlockFirstBlockQuotient.determinantSlice F h k := by
  ext q
  change determinantOrder F h (projectionFromMixed F h q) = k ↔
    TwoBlockFirstBlockQuotient.determinantOrder F h q = k
  rw [determinantOrder_projectionFromMixed]

theorem projectionFromLower_preimage_determinantSlice (k : ℤ) :
    projectionFromLower F h ⁻¹' determinantSlice F h k =
      TwoBlockLowerUnipotentQuotient.determinantSlice F h k := by
  ext q
  change determinantOrder F h (projectionFromLower F h q) = k ↔
    TwoBlockLowerUnipotentQuotient.determinantOrder F h q = k
  rw [determinantOrder_projectionFromLower]

/-- Right translation shifts the order by the order of its determinant. -/
theorem determinantOrder_rightTranslate :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    ∀ (g : GeneralLinear (t + 1) F.Carrier) (q : LowerMixedQuotient F h),
      determinantOrder F h (rightTranslate _ g q) =
        determinantOrder F h q +
          F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro g q
  induction q using Quotient.inductionOn with
  | h x =>
    rw [rightTranslate_mk, determinantOrder_mk, determinantOrder_mk, map_mul, Units.val_mul,
      F.canonicalTopologicalData.ord_mul (GeneralLinear.determinant x).ne_zero
        (GeneralLinear.determinant g).ne_zero]

theorem rightTranslate_mem_determinantSlice (k : ℤ) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    ∀ (g : GeneralLinear (t + 1) F.Carrier) (q : LowerMixedQuotient F h),
      rightTranslate _ g q ∈ determinantSlice F h k ↔
        q ∈ determinantSlice F h
          (k - F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier)) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro g q
  rw [mem_determinantSlice, mem_determinantSlice, determinantOrder_rightTranslate F h g q,
    eq_sub_iff_add_eq]

end Padic

/-! ### Commutation of the lower radical with block-diagonal matrices -/

section Commutation

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable (R : Type uR) [CommRing R]

/-- `R(W) diag(u, w) = diag(u, w) R(w⁻¹ W u)`. -/
theorem lowerRadical_mul_leviEmbedding_blockPair
    (W : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R)
    (u : GeneralLinear (m 0 + 1) R) (w : GeneralLinear (m 1 + 1) R) :
    lowerRadical h R W * (succBlockShape m h).leviEmbedding R (blockPair R (u, w)) =
      (succBlockShape m h).leviEmbedding R (blockPair R (u, w)) *
        lowerRadical h R ((w⁻¹ : GeneralLinear _ R).val * W * u.val) := by
  apply ext_entryBlock h R <;>
    simp only [entryBlock_mul, entryBlock_lowerRadical_zero_zero,
      entryBlock_lowerRadical_zero_one, entryBlock_lowerRadical_one_zero,
      entryBlock_lowerRadical_one_one, entryBlock_levi_zero_zero, entryBlock_levi_zero_one,
      entryBlock_levi_one_zero, entryBlock_levi_one_one, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, ← Matrix.mul_assoc, Units.mul_inv]

/-- `diag(u, w) R(W) = R(w W u⁻¹) diag(u, w)`. -/
theorem leviEmbedding_blockPair_mul_lowerRadical
    (u : GeneralLinear (m 0 + 1) R) (w : GeneralLinear (m 1 + 1) R)
    (W : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R) :
    (succBlockShape m h).leviEmbedding R (blockPair R (u, w)) * lowerRadical h R W =
      lowerRadical h R (w.val * W * (u⁻¹ : GeneralLinear _ R).val) *
        (succBlockShape m h).leviEmbedding R (blockPair R (u, w)) := by
  apply ext_entryBlock h R <;>
    simp only [entryBlock_mul, entryBlock_lowerRadical_zero_zero,
      entryBlock_lowerRadical_zero_one, entryBlock_lowerRadical_one_zero,
      entryBlock_lowerRadical_one_one, entryBlock_levi_zero_zero, entryBlock_levi_zero_one,
      entryBlock_levi_one_zero, entryBlock_levi_one_one, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, Matrix.mul_assoc, Units.inv_mul]

/-- `I(v) R(W) = R(W v⁻¹) I(v)` for the first-block embedding `I(v) = diag(v, 1)`. -/
theorem firstBlockEmbedding_mul_lowerRadical (v : GeneralLinear (m 0 + 1) R)
    (W : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R) :
    firstBlockEmbedding h R v * lowerRadical h R W =
      lowerRadical h R (W * (v⁻¹ : GeneralLinear _ R).val) * firstBlockEmbedding h R v := by
  rw [firstBlockEmbedding_apply, leviEmbedding_blockPair_mul_lowerRadical, Units.val_one,
    Matrix.one_mul]

/-- `diag(u, w)` lies in `H⁻` when both blocks are upper unipotent. -/
theorem leviEmbedding_blockPair_mem_lowerBlockUnipotent {u : GeneralLinear (m 0 + 1) R}
    {w : GeneralLinear (m 1 + 1) R} (hu : u ∈ upperUnipotent (m 0 + 1) R)
    (hw : w ∈ upperUnipotent (m 1 + 1) R) :
    (succBlockShape m h).leviEmbedding R (blockPair R (u, w)) ∈ lowerBlockUnipotent h R := by
  have hL : ∀ i : Fin 2, blockPair R (u, w) i ∈ upperUnipotent (m i + 1) R := by
    intro i
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · simpa using hu
    · simpa using hw
  refine (mem_lowerBlockUnipotent_iff h R _).mpr
    ⟨fun a b => leviEmbedding_index_zero_one h _ a b, fun i a b hab => ?_, fun i a => ?_⟩
  · rw [(succBlockShape m h).leviEmbedding_apply_same]
    exact UpperUnipotent.entry_eq_zero ⟨_, hL i⟩ hab
  · rw [(succBlockShape m h).leviEmbedding_apply_same]
    exact UpperUnipotent.entry_diag ⟨_, hL i⟩ a

/-- An upper-unipotent first block embeds into `H⁻`. -/
theorem firstBlockEmbedding_mem_lowerBlockUnipotent {u : GeneralLinear (m 0 + 1) R}
    (hu : u ∈ upperUnipotent (m 0 + 1) R) :
    firstBlockEmbedding h R u ∈ lowerBlockUnipotent h R :=
  leviEmbedding_blockPair_mem_lowerBlockUnipotent h R hu (upperUnipotent (m 1 + 1) R).one_mem

end Commutation

/-! ### Rectangular fibers into the mixed quotient -/

section RadicalFiber

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The rectangular fiber map `(Z, g) ↦ [R(Z) g]_M` into the published mixed quotient
`M \ G`, `M = diag(GL_a^0, N_b)`. -/
def radicalFiberPoint (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) : MixedQuotient F h :=
  Quotient.mk _ (lowerRadical h F.Carrier Z * g)

theorem radicalFiberPoint_def (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    radicalFiberPoint F h Z g = Quotient.mk _ (lowerRadical h F.Carrier Z * g) :=
  rfl

/-- The rectangular fiber map is jointly continuous in `(Z, g)`. -/
theorem continuous_radicalFiberPoint :
    letI := F.canonicalTopologicalData.topology
    Continuous (Function.uncurry (radicalFiberPoint F h)) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (t + 1)
  exact continuous_quotient_mk'.comp
    (((continuous_lowerRadical h F.Carrier).comp continuous_fst).mul continuous_snd)

/-- Right translation of the base point translates the fiber point. -/
theorem radicalFiberPoint_mul :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    ∀ (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
      (g g' : GeneralLinear (t + 1) F.Carrier),
      radicalFiberPoint F h Z (g * g') = rightTranslate _ g' (radicalFiberPoint F h Z g) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro Z g g'
  rw [radicalFiberPoint_def, radicalFiberPoint_def, rightTranslate_mk, mul_assoc]

/-- Since `det R(Z) = 1`, the fiber point has the determinant order of `g`. -/
@[simp]
theorem determinantOrder_radicalFiberPoint
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    TwoBlockFirstBlockQuotient.determinantOrder F h (radicalFiberPoint F h Z g) =
      F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) := by
  rw [radicalFiberPoint_def, TwoBlockFirstBlockQuotient.determinantOrder_mk, map_mul,
    determinant_lowerRadical, one_mul]

/-- The fiber point lies in the published slice `M \ G^k` exactly when `ord(det g) = k`. -/
theorem radicalFiberPoint_mem_determinantSlice_iff
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) (k : ℤ) :
    radicalFiberPoint F h Z g ∈ TwoBlockFirstBlockQuotient.determinantSlice F h k ↔
      F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) = k := by
  rw [TwoBlockFirstBlockQuotient.mem_determinantSlice, determinantOrder_radicalFiberPoint]

/-- The affine change of rectangular coordinates `Z ↦ n⁻¹ (Z + Z0) a0` attached to
`l = R(Z0) D(a0, n)`. -/
def radicalChange {a b : ℕ} (Z0 : Matrix (Fin b) (Fin a) F.Carrier) (a0 : normOneSubgroup F a)
    (n : upperUnipotent b F.Carrier) (Z : Matrix (Fin b) (Fin a) F.Carrier) :
    Matrix (Fin b) (Fin a) F.Carrier :=
  (n.val⁻¹).val * (Z + Z0) * a0.val.val

theorem radicalChange_apply {a b : ℕ} (Z0 : Matrix (Fin b) (Fin a) F.Carrier)
    (a0 : normOneSubgroup F a) (n : upperUnipotent b F.Carrier)
    (Z : Matrix (Fin b) (Fin a) F.Carrier) :
    radicalChange F Z0 a0 n Z = (n.val⁻¹).val * (Z + Z0) * a0.val.val :=
  rfl

/-- Representative change: for `l = R(Z0) D(a0, n)`,
`radicalFiberPoint Z (l g) = radicalFiberPoint (n⁻¹ (Z + Z0) a0) g`. -/
theorem radicalFiberPoint_lowerRadical_mixedEmbedding_mul
    (Z Z0 : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (a0 : normOneSubgroup F (m 0 + 1)) (n : upperUnipotent (m 1 + 1) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    radicalFiberPoint F h Z (lowerRadical h F.Carrier Z0 * mixedEmbedding F h (a0, n) * g) =
      radicalFiberPoint F h (radicalChange F Z0 a0 n Z) g := by
  rw [radicalFiberPoint_def, radicalFiberPoint_def, ← mul_assoc, ← mul_assoc,
    ← lowerRadical_add, mixedEmbedding_apply, lowerRadical_mul_leviEmbedding_blockPair,
    mul_assoc]
  exact TwoBlockUnipotentQuotient.mk_mul_of_mem _ (mixedEmbedding_mem F h (a0, n)) _

/-- The affine change is a homeomorphism of the rectangle. -/
def radicalChangeHomeomorph {a b : ℕ} (Z0 : Matrix (Fin b) (Fin a) F.Carrier)
    (a0 : normOneSubgroup F a) (n : upperUnipotent b F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    Matrix (Fin b) (Fin a) F.Carrier ≃ₜ Matrix (Fin b) (Fin a) F.Carrier := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact
    { toFun := radicalChange F Z0 a0 n
      invFun := fun W => n.val.val * W * (a0.val⁻¹).val - Z0
      left_inv := fun Z => by
        simp only [radicalChange, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, add_sub_cancel_right]
      right_inv := fun W => by
        simp only [radicalChange, sub_add_cancel, Matrix.mul_assoc, Units.inv_mul,
          Matrix.mul_one]
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      continuous_toFun :=
        (continuous_const.matrix_mul (continuous_id.add continuous_const)).matrix_mul
          continuous_const
      continuous_invFun :=
        ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).sub
          continuous_const }

@[simp]
theorem radicalChangeHomeomorph_apply {a b : ℕ} (Z0 : Matrix (Fin b) (Fin a) F.Carrier)
    (a0 : normOneSubgroup F a) (n : upperUnipotent b F.Carrier)
    (Z : Matrix (Fin b) (Fin a) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    radicalChangeHomeomorph F Z0 a0 n Z = radicalChange F Z0 a0 n Z :=
  rfl

/-- The affine change `Z ↦ n⁻¹ (Z + Z0) a0` preserves every Borel additive Haar measure on
the rectangle: its linear part has both determinant norms one
(`padicRectangularHaarScaling`), and the translation part preserves Haar measure. -/
theorem measurePreserving_radicalChange {a b : ℕ} :
    letI := F.canonicalTopologicalData.topology
    ∀ [MeasurableSpace (Matrix (Fin b) (Fin a) F.Carrier)]
      [BorelSpace (Matrix (Fin b) (Fin a) F.Carrier)]
      (μR : Measure (Matrix (Fin b) (Fin a) F.Carrier)) [μR.IsAddHaarMeasure]
      (Z0 : Matrix (Fin b) (Fin a) F.Carrier) (a0 : normOneSubgroup F a)
      (n : upperUnipotent b F.Carrier),
      MeasurePreserving (radicalChange F Z0 a0 n) μR μR := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μR _ Z0 a0 n
  have hlin : Continuous (fun X : Matrix (Fin b) (Fin a) F.Carrier =>
      (n.val⁻¹).val * X * a0.val.val) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have htr : Continuous (fun Z : Matrix (Fin b) (Fin a) F.Carrier => Z + Z0) :=
    continuous_id.add continuous_const
  have hn : T.determinantNorm b n.val = 1 :=
    determinantNorm_eq_one_of_mem_upperUnipotent F T n.property
  have ha : T.determinantNorm a a0.val = 1 := (mem_normOneSubgroup_iff F a0.val).mp a0.property
  have hscale := HarmonicAnalysis.padicRectangularHaarScaling F T b a μR n.val⁻¹ a0.val⁻¹
  simp only [inv_inv, map_inv, hn, ha, inv_one, Units.val_one, one_pow, div_one,
    one_smul] at hscale
  refine ⟨hlin.measurable.comp htr.measurable, ?_⟩
  change μR.map ((fun X : Matrix (Fin b) (Fin a) F.Carrier => (n.val⁻¹).val * X * a0.val.val) ∘
    (fun Z => Z + Z0)) = μR
  rw [← Measure.map_map hlin.measurable htr.measurable, map_add_right_eq_self μR Z0, hscale]

/-- Integrals over the rectangle are invariant under the affine change, with no
integrability hypothesis. -/
theorem integral_comp_radicalChange {a b : ℕ} :
    letI := F.canonicalTopologicalData.topology
    ∀ [MeasurableSpace (Matrix (Fin b) (Fin a) F.Carrier)]
      [BorelSpace (Matrix (Fin b) (Fin a) F.Carrier)]
      (μR : Measure (Matrix (Fin b) (Fin a) F.Carrier)) [μR.IsAddHaarMeasure]
      (Z0 : Matrix (Fin b) (Fin a) F.Carrier) (a0 : normOneSubgroup F a)
      (n : upperUnipotent b F.Carrier) (G : Matrix (Fin b) (Fin a) F.Carrier → ℂ),
      ∫ Z, G (radicalChange F Z0 a0 n Z) ∂μR = ∫ Z, G Z ∂μR := by
  let := F.canonicalTopologicalData.topology
  intro _ _ μR _ Z0 a0 n G
  exact (measurePreserving_radicalChange F μR Z0 a0 n).integral_comp
    (radicalChangeHomeomorph F Z0 a0 n).measurableEmbedding G

section Average

variable [MeasurableSpace (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)]

/-- The rectangular fiber integral `g ↦ ∫ f([R(Z) g]_M) dμR(Z)`, the ordinary total Bochner
integral against the supplied measure on the rectangle. -/
def radicalFiberIntegral (μR : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier))
    (f : MixedQuotient F h → ℂ) (g : GeneralLinear (t + 1) F.Carrier) : ℂ :=
  ∫ Z, f (radicalFiberPoint F h Z g) ∂μR

theorem radicalFiberIntegral_def
    (μR : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier))
    (f : MixedQuotient F h → ℂ) (g : GeneralLinear (t + 1) F.Carrier) :
    radicalFiberIntegral F h μR f g = ∫ Z, f (radicalFiberPoint F h Z g) ∂μR :=
  rfl

/-- Left invariance under `l = R(Z0) D(a0, n)`, for every Borel additive Haar measure and
every scalar function, without any integrability hypothesis. -/
theorem radicalFiberIntegral_lowerRadical_mixedEmbedding_mul :
    letI := F.canonicalTopologicalData.topology
    ∀ [BorelSpace (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)]
      (μR : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)) [μR.IsAddHaarMeasure]
      (f : MixedQuotient F h → ℂ) (Z0 : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
      (a0 : normOneSubgroup F (m 0 + 1)) (n : upperUnipotent (m 1 + 1) F.Carrier)
      (g : GeneralLinear (t + 1) F.Carrier),
      radicalFiberIntegral F h μR f
          (lowerRadical h F.Carrier Z0 * mixedEmbedding F h (a0, n) * g) =
        radicalFiberIntegral F h μR f g := by
  let := F.canonicalTopologicalData.topology
  intro _ μR _ f Z0 a0 n g
  simp only [radicalFiberIntegral_def, radicalFiberPoint_lowerRadical_mixedEmbedding_mul]
  exact integral_comp_radicalChange F μR Z0 a0 n (fun Z => f (radicalFiberPoint F h Z g))

/-- Left invariance under every element of the actual lower mixed subgroup. -/
theorem radicalFiberIntegral_lowerMixedSubgroup_mul :
    letI := F.canonicalTopologicalData.topology
    ∀ [BorelSpace (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)]
      (μR : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)) [μR.IsAddHaarMeasure]
      (f : MixedQuotient F h → ℂ) (l : lowerMixedSubgroup F h)
      (g : GeneralLinear (t + 1) F.Carrier),
      radicalFiberIntegral F h μR f (l.val * g) = radicalFiberIntegral F h μR f g := by
  let := F.canonicalTopologicalData.topology
  intro _ μR _ f l g
  obtain ⟨Z0, a0, n, hl⟩ := lowerMixed_decomposition F h l.property
  rw [← hl]
  exact radicalFiberIntegral_lowerRadical_mixedEmbedding_mul F h μR f Z0 a0 n g

/-- Right translation of the base point is right translation of the integrand. -/
theorem radicalFiberIntegral_mul :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    ∀ (μR : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier))
      (f : MixedQuotient F h → ℂ) (g g' : GeneralLinear (t + 1) F.Carrier),
      radicalFiberIntegral F h μR f (g * g') =
        radicalFiberIntegral F h μR (fun r => f (rightTranslate _ g' r)) g := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro μR f g g'
  simp only [radicalFiberIntegral_def, radicalFiberPoint_mul]

/-- The rectangular average on the actual quotient `Lminus \ G`: the actual descent of the
left-`Lminus`-invariant fiber integral. No coset representative is chosen. -/
def radicalAverage :
    letI := F.canonicalTopologicalData.topology
    ∀ [BorelSpace (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)]
      (μR : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)) [μR.IsAddHaarMeasure],
      (MixedQuotient F h → ℂ) → LowerMixedQuotient F h → ℂ := by
  letI := F.canonicalTopologicalData.topology
  intro _ μR _ f
  exact descend _ (radicalFiberIntegral F h μR f)
    (fun l g => radicalFiberIntegral_lowerMixedSubgroup_mul F h μR f l g)

/-- Representative evaluation of the rectangular average. -/
theorem radicalAverage_mk :
    letI := F.canonicalTopologicalData.topology
    ∀ [BorelSpace (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)]
      (μR : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)) [μR.IsAddHaarMeasure]
      (f : MixedQuotient F h → ℂ) (g : GeneralLinear (t + 1) F.Carrier),
      radicalAverage F h μR f (Quotient.mk _ g) = ∫ Z, f (radicalFiberPoint F h Z g) ∂μR := by
  let := F.canonicalTopologicalData.topology
  intro _ μR _ f g
  rfl

/-- Right translation on `Lminus \ G` corresponds to right translation of the function on
`M \ G`. -/
theorem radicalAverage_rightTranslate :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    ∀ [BorelSpace (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)]
      (μR : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)) [μR.IsAddHaarMeasure]
      (f : MixedQuotient F h → ℂ) (g : GeneralLinear (t + 1) F.Carrier)
      (q : LowerMixedQuotient F h),
      radicalAverage F h μR f (rightTranslate _ g q) =
        radicalAverage F h μR (fun r => f (rightTranslate _ g r)) q := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro _ μR _ f g q
  induction q using Quotient.inductionOn with
  | h x =>
    rw [rightTranslate_mk, radicalAverage_mk, radicalAverage_mk]
    exact radicalFiberIntegral_mul F h μR f x g

end Average

end RadicalFiber

/-! ### First-block fibers into the lower unipotent quotient -/

section FirstBlockFiber

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The first-block fiber map `([v], g) ↦ [I(v) g]_{H⁻}` from the small quotient
`N_a \ GL_a` to `H⁻ \ G`, by actual quotient descent: left multiplication of `v` by
`n ∈ N_a` multiplies `I(v) g` on the left by `I(n) ∈ H⁻`. -/
def firstBlockFiberPoint (q : LeftUnipotentQuotient (m 0) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) : LowerQuotient h F.Carrier :=
  descend _
    (fun v => (Quotient.mk _ (firstBlockEmbedding h F.Carrier v * g) : LowerQuotient h F.Carrier))
    (fun n v => by
      rw [map_mul, mul_assoc]
      exact TwoBlockUnipotentQuotient.mk_mul_of_mem _
        (firstBlockEmbedding_mem_lowerBlockUnipotent h F.Carrier n.property) _)
    q

/-- Representative formula: `firstBlockFiberPoint [v] g = [I(v) g]_{H⁻}`. -/
@[simp]
theorem firstBlockFiberPoint_mk (v : GeneralLinear (m 0 + 1) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    firstBlockFiberPoint F h (Quotient.mk _ v) g =
      Quotient.mk _ (firstBlockEmbedding h F.Carrier v * g) :=
  rfl

/-- The first-block fiber map is jointly continuous in `(q, g)`. -/
theorem continuous_firstBlockFiberPoint :
    letI := F.canonicalTopologicalData.topology
    Continuous (Function.uncurry (firstBlockFiberPoint F h)) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (m 0 + 1)
  let := T.generalLinearTopologicalGroup (t + 1)
  have hq : IsOpenQuotientMap (Prod.map (leftQuotientMap (upperUnipotent (m 0 + 1) F.Carrier))
      (id : GeneralLinear (t + 1) F.Carrier → GeneralLinear (t + 1) F.Carrier)) :=
    (leftQuotient_isOpenQuotientMap _).prodMap IsOpenQuotientMap.id
  rw [← hq.continuous_comp_iff]
  have he : Function.uncurry (firstBlockFiberPoint F h) ∘
      Prod.map (leftQuotientMap (upperUnipotent (m 0 + 1) F.Carrier)) id =
      fun x : GeneralLinear (m 0 + 1) F.Carrier × GeneralLinear (t + 1) F.Carrier =>
        (Quotient.mk _ (firstBlockEmbedding h F.Carrier x.1 * x.2) :
          LowerQuotient h F.Carrier) :=
    rfl
  rw [he]
  exact continuous_quotient_mk'.comp
    (((continuous_firstBlockEmbedding h F.Carrier).comp continuous_fst).mul continuous_snd)

/-- Right translation of the base point translates the fiber point. -/
theorem firstBlockFiberPoint_mul :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    ∀ (q : LeftUnipotentQuotient (m 0) F.Carrier) (g g' : GeneralLinear (t + 1) F.Carrier),
      firstBlockFiberPoint F h q (g * g') =
        rightTranslate _ g' (firstBlockFiberPoint F h q g) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro q g g'
  induction q using Quotient.inductionOn with
  | h v => rw [firstBlockFiberPoint_mk, firstBlockFiberPoint_mk, rightTranslate_mk, mul_assoc]

/-- The determinant order of the fiber point is the published small order of `q` plus
`ord(det g)`. -/
theorem determinantOrder_firstBlockFiberPoint (q : LeftUnipotentQuotient (m 0) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    TwoBlockLowerUnipotentQuotient.determinantOrder F h (firstBlockFiberPoint F h q g) =
      RankinSelberg.determinantOrder F.canonicalTopologicalData (m 0) q +
        F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) := by
  induction q using Quotient.inductionOn with
  | h v =>
    rw [firstBlockFiberPoint_mk, TwoBlockLowerUnipotentQuotient.determinantOrder_mk,
      RankinSelberg.determinantOrder_mk, map_mul, Units.val_mul,
      F.canonicalTopologicalData.ord_mul
        (GeneralLinear.determinant (firstBlockEmbedding h F.Carrier v)).ne_zero
        (GeneralLinear.determinant g).ne_zero,
      determinant_firstBlockEmbedding]

/-- `firstBlockFiberPoint q g` lies in the published slice `H⁻ \ G^k` exactly when
`ord(det q) + ord(det g) = k`. -/
theorem firstBlockFiberPoint_mem_determinantSlice_iff
    (q : LeftUnipotentQuotient (m 0) F.Carrier) (g : GeneralLinear (t + 1) F.Carrier) (k : ℤ) :
    firstBlockFiberPoint F h q g ∈ TwoBlockLowerUnipotentQuotient.determinantSlice F h k ↔
      RankinSelberg.determinantOrder F.canonicalTopologicalData (m 0) q +
        F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) = k := by
  rw [TwoBlockLowerUnipotentQuotient.mem_determinantSlice_iff_determinantOrder,
    determinantOrder_firstBlockFiberPoint]

/-- The block identity `I(v) R(Z0) D(a0, n) = R(Z0 v⁻¹) diag(1, n) I(v a0)`. -/
theorem firstBlockEmbedding_mul_lowerRadical_mul_mixedEmbedding
    (v : GeneralLinear (m 0 + 1) F.Carrier)
    (Z0 : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (a0 : normOneSubgroup F (m 0 + 1)) (n : upperUnipotent (m 1 + 1) F.Carrier) :
    firstBlockEmbedding h F.Carrier v * (lowerRadical h F.Carrier Z0 * mixedEmbedding F h (a0, n)) =
      lowerRadical h F.Carrier (Z0 * (v⁻¹ : GeneralLinear _ F.Carrier).val) *
          (succBlockShape m h).leviEmbedding F.Carrier (blockPair F.Carrier (1, n.val)) *
        firstBlockEmbedding h F.Carrier (v * a0.val) := by
  rw [← mul_assoc, firstBlockEmbedding_mul_lowerRadical, mul_assoc, mixedEmbedding_apply,
    firstBlockEmbedding_mul_leviEmbedding_blockPair, ← mul_assoc]

/-- The first two factors `R(Z0 v⁻¹) diag(1, n)` of the block identity lie in `H⁻`. -/
theorem lowerRadical_mul_leviEmbedding_one_mem
    (W : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (n : upperUnipotent (m 1 + 1) F.Carrier) :
    lowerRadical h F.Carrier W *
        (succBlockShape m h).leviEmbedding F.Carrier (blockPair F.Carrier (1, n.val)) ∈
      lowerBlockUnipotent h F.Carrier :=
  (lowerBlockUnipotent h F.Carrier).mul_mem (lowerRadical_mem h F.Carrier W)
    (leviEmbedding_blockPair_mem_lowerBlockUnipotent h F.Carrier
      (upperUnipotent (m 0 + 1) F.Carrier).one_mem n.property)

/-- Change of fiber: for `l = R(Z0) D(a0, n)`, left multiplication of the base point by `l`
is right translation of the small quotient by `a0`. -/
theorem firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (m 0 + 1)
    ∀ (q : LeftUnipotentQuotient (m 0) F.Carrier)
      (Z0 : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
      (a0 : normOneSubgroup F (m 0 + 1)) (n : upperUnipotent (m 1 + 1) F.Carrier)
      (g : GeneralLinear (t + 1) F.Carrier),
      firstBlockFiberPoint F h q (lowerRadical h F.Carrier Z0 * mixedEmbedding F h (a0, n) * g) =
        firstBlockFiberPoint F h (rightTranslate _ a0.val q) g := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (m 0 + 1)
  intro q Z0 a0 n g
  induction q using Quotient.inductionOn with
  | h v =>
    rw [rightTranslate_mk, firstBlockFiberPoint_mk, firstBlockFiberPoint_mk, ← mul_assoc,
      firstBlockEmbedding_mul_lowerRadical_mul_mixedEmbedding, mul_assoc]
    exact TwoBlockUnipotentQuotient.mk_mul_of_mem _
      (lowerRadical_mul_leviEmbedding_one_mem F h _ n) _

variable
  (μA : letI := F.canonicalTopologicalData.topology
    letI := borel (LeftUnipotentQuotient (m 0) F.Carrier)
    Measure (LeftUnipotentQuotient (m 0) F.Carrier))

/-- The inner slice integral of JPSS (4.9), (8): the total Bochner integral
`∫_{N_a \ GL_a^k} f(firstBlockFiberPoint q g) dμA(q)` over the published small slice, for
the supplied measure on the Borel structure of the small quotient. -/
def firstBlockFiberIntegral (k : ℤ) (f : LowerQuotient h F.Carrier → ℂ)
    (g : GeneralLinear (t + 1) F.Carrier) : ℂ :=
  letI := F.canonicalTopologicalData.topology
  letI := borel (LeftUnipotentQuotient (m 0) F.Carrier)
  ∫ q in RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k,
    f (firstBlockFiberPoint F h q g) ∂μA

theorem firstBlockFiberIntegral_def (k : ℤ) (f : LowerQuotient h F.Carrier → ℂ)
    (g : GeneralLinear (t + 1) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI := borel (LeftUnipotentQuotient (m 0) F.Carrier)
    firstBlockFiberIntegral F h μA k f g =
      ∫ q in RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k,
        f (firstBlockFiberPoint F h q g) ∂μA :=
  rfl

/-- Left invariance under `l = R(Z0) D(a0, n)`, without any integrability hypothesis: right
translation by `a0` preserves `μA` and, since `ord(det a0) = 0`, the small slice. -/
theorem firstBlockFiberIntegral_lowerRadical_mixedEmbedding_mul
    (hμA : NormOneRightInvariant F (m 0) μA) (k : ℤ) (f : LowerQuotient h F.Carrier → ℂ)
    (Z0 : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (a0 : normOneSubgroup F (m 0 + 1)) (n : upperUnipotent (m 1 + 1) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    firstBlockFiberIntegral F h μA k f
        (lowerRadical h F.Carrier Z0 * mixedEmbedding F h (a0, n) * g) =
      firstBlockFiberIntegral F h μA k f g := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (m 0 + 1)
  let := borel (LeftUnipotentQuotient (m 0) F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient (m 0) F.Carrier) := ⟨rfl⟩
  have hS : rightTranslate _ a0.val ⁻¹' RankinSelberg.determinantSlice T (m 0) k =
      RankinSelberg.determinantSlice T (m 0) k := by
    ext q
    rw [Set.mem_preimage, RankinSelberg.rightTranslate_mem_determinantSlice T (m 0) k a0.val q,
      ord_determinant_eq_zero F a0.property, sub_zero]
  rw [firstBlockFiberIntegral_def, firstBlockFiberIntegral_def]
  simp_rw [firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul F h _ Z0 a0 n g]
  have hI := (hμA a0).setIntegral_preimage_emb (rightTranslate _ a0.val).measurableEmbedding
    (fun q => f (firstBlockFiberPoint F h q g)) (RankinSelberg.determinantSlice T (m 0) k)
  rw [hS] at hI
  exact hI

/-- Left invariance under every element of the actual lower mixed subgroup. -/
theorem firstBlockFiberIntegral_lowerMixedSubgroup_mul
    (hμA : NormOneRightInvariant F (m 0) μA) (k : ℤ) (f : LowerQuotient h F.Carrier → ℂ)
    (l : lowerMixedSubgroup F h) (g : GeneralLinear (t + 1) F.Carrier) :
    firstBlockFiberIntegral F h μA k f (l.val * g) = firstBlockFiberIntegral F h μA k f g := by
  obtain ⟨Z0, a0, n, hl⟩ := lowerMixed_decomposition F h l.property
  rw [← hl]
  exact firstBlockFiberIntegral_lowerRadical_mixedEmbedding_mul F h μA hμA k f Z0 a0 n g

/-- Right translation of the base point is right translation of the integrand. -/
theorem firstBlockFiberIntegral_mul :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    ∀ (k : ℤ) (f : LowerQuotient h F.Carrier → ℂ) (g g' : GeneralLinear (t + 1) F.Carrier),
      firstBlockFiberIntegral F h μA k f (g * g') =
        firstBlockFiberIntegral F h μA k (fun r => f (rightTranslate _ g' r)) g := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro k f g g'
  simp only [firstBlockFiberIntegral_def, firstBlockFiberPoint_mul]

/-- The first-block slice average on the actual quotient `Lminus \ G`: the actual descent
of the left-`Lminus`-invariant inner slice integral. No coset representative is chosen. -/
def firstBlockAverage (hμA : NormOneRightInvariant F (m 0) μA) (k : ℤ)
    (f : LowerQuotient h F.Carrier → ℂ) : LowerMixedQuotient F h → ℂ :=
  descend _ (firstBlockFiberIntegral F h μA k f)
    (firstBlockFiberIntegral_lowerMixedSubgroup_mul F h μA hμA k f)

/-- Representative evaluation of the first-block slice average. -/
theorem firstBlockAverage_mk (hμA : NormOneRightInvariant F (m 0) μA) (k : ℤ)
    (f : LowerQuotient h F.Carrier → ℂ) (g : GeneralLinear (t + 1) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI := borel (LeftUnipotentQuotient (m 0) F.Carrier)
    firstBlockAverage F h μA hμA k f (Quotient.mk _ g) =
      ∫ q in RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k,
        f (firstBlockFiberPoint F h q g) ∂μA :=
  rfl

/-- Right translation on `Lminus \ G` corresponds to right translation of the function on
`H⁻ \ G`. -/
theorem firstBlockAverage_rightTranslate (hμA : NormOneRightInvariant F (m 0) μA) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    ∀ (k : ℤ) (f : LowerQuotient h F.Carrier → ℂ) (g : GeneralLinear (t + 1) F.Carrier)
      (q : LowerMixedQuotient F h),
      firstBlockAverage F h μA hμA k f (rightTranslate _ g q) =
        firstBlockAverage F h μA hμA k (fun r => f (rightTranslate _ g r)) q := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro k f g q
  induction q using Quotient.inductionOn with
  | h x =>
    rw [rightTranslate_mk]
    exact firstBlockFiberIntegral_mul F h μA k f x g

end FirstBlockFiber

end Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient
