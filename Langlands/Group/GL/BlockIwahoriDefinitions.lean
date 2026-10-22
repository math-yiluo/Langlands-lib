import Langlands.Group.GL.OppositeBlocks
import Langlands.Group.GL.NormalizedCharacter
import Mathlib.Topology.Algebra.OpenSubgroup

noncomputable section

open scoped NNReal

namespace Langlands.GeneralLinear.BlockShape

universe u

variable {n : ℕ} (B : GeneralLinear.BlockShape n) (R : Type u) [CommRing R]

/-- Blockwise scalar matrices in the actual product Levi. -/
def blockScalarLevi : (Fin B.length → Rˣ) →* B.Levi R where
  toFun a i := GeneralLinear.scalar (a i)
  map_one' := by funext i; exact map_one GeneralLinear.scalar
  map_mul' a b := by funext i; exact map_mul GeneralLinear.scalar (a i) (b i)

/-- The same scalars in the embedded common Levi subgroup. -/
def blockScalarInLevi : (Fin B.length → Rˣ) →* B.leviSubgroup R :=
  (B.leviEquiv R).toMonoidHom.comp (B.blockScalarLevi R)

/-- Actual block diagonal scalar matrices in the ambient general linear group. -/
def blockScalar : (Fin B.length → Rˣ) →* GeneralLinear n R :=
  (B.leviEmbedding R).comp (B.blockScalarLevi R)

@[simp] theorem blockScalarLevi_apply (a : Fin B.length → Rˣ) (i : Fin B.length) :
    B.blockScalarLevi R a i = GeneralLinear.scalar (a i) := rfl

@[simp] theorem blockScalarInLevi_val (a : Fin B.length → Rˣ) :
    (B.blockScalarInLevi R a).val = B.blockScalar R a := rfl

@[simp] theorem blockScalar_one : B.blockScalar R 1 = 1 := map_one _

@[simp] theorem blockScalar_mul (a b : Fin B.length → Rˣ) :
    B.blockScalar R (a * b) = B.blockScalar R a * B.blockScalar R b := map_mul _ _ _

@[simp] theorem blockScalar_inv (a : Fin B.length → Rˣ) :
    B.blockScalar R a⁻¹ = (B.blockScalar R a)⁻¹ := map_inv _ _

@[simp] theorem blockScalar_apply_same (a : Fin B.length → Rˣ)
    (i : Fin B.length) (r s : Fin (B.size i)) :
    B.blockScalar R a (B.index i r) (B.index i s) =
      if r = s then (a i : R) else 0 := by
  change B.leviEmbedding R (B.blockScalarLevi R a) _ _ = _
  rw [B.leviEmbedding_apply_same]
  rfl

theorem blockScalar_apply_ne (a : Fin B.length → Rˣ) {i j : Fin B.length}
    (r : Fin (B.size i)) (s : Fin (B.size j)) (hij : i ≠ j) :
    B.blockScalar R a (B.index i r) (B.index j s) = 0 :=
  B.leviEmbedding_apply_ne R _ r s hij

theorem blockScalar_mem_leviSubgroup (a : Fin B.length → Rˣ) :
    B.blockScalar R a ∈ B.leviSubgroup R := (B.blockScalarInLevi R a).property

/-- Block scalars commute with every element of the product Levi. -/
theorem blockScalarLevi_commute (a : Fin B.length → Rˣ) (m : B.Levi R) :
    B.blockScalarLevi R a * m = m * B.blockScalarLevi R a := by
  funext i
  exact Matrix.GeneralLinearGroup.scalar_commute (a i) (m i)

/-- Scalar conjugation preserves the actual upper radical. -/
theorem blockScalar_conj_mem_unipotentSubgroup (a : Fin B.length → Rˣ)
    {g : GeneralLinear n R} (hg : g ∈ B.unipotentSubgroup R) :
    B.blockScalar R a * g * (B.blockScalar R a)⁻¹ ∈ B.unipotentSubgroup R :=
  B.levi_conj_mem_unipotentSubgroup R (B.blockScalarLevi R a) hg

/-- Inverse scalar conjugation preserves the actual opposite radical. -/
theorem blockScalar_inv_conj_mem_oppositeUnipotentSubgroup (a : Fin B.length → Rˣ)
    {g : GeneralLinear n R} (hg : g ∈ B.oppositeUnipotentSubgroup R) :
    (B.blockScalar R a)⁻¹ * g * B.blockScalar R a ∈ B.oppositeUnipotentSubgroup R := by
  have h := B.levi_conj_mem_oppositeUnipotentSubgroup R (B.blockScalarLevi R a⁻¹) hg
  change B.blockScalar R a⁻¹ * g * (B.blockScalar R a⁻¹)⁻¹ ∈ _ at h
  simpa only [blockScalar_inv, inv_inv] using h

/-- Block scalars are the actual diagonal matrices in standard coordinates. -/
theorem coe_blockScalar (a : Fin B.length → Rˣ) :
    (B.blockScalar R a : Matrix (Fin n) (Fin n) R) =
      Matrix.diagonal (fun k => (a (B.indexEquiv.symm k).1 : R)) := by
  ext x y
  obtain ⟨⟨i, r⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, s⟩, rfl⟩ := B.indexEquiv.surjective y
  change B.blockScalar R a (B.index i r) (B.index j s) = _
  by_cases hij : i = j
  · subst j
    rw [B.blockScalar_apply_same]
    simp [Matrix.diagonal_apply, B.indexEquiv.injective.eq_iff]
  · rw [B.blockScalar_apply_ne R a r s hij]
    simp [B.indexEquiv.injective.eq_iff, hij]

/-- Left block-scalar multiplication multiplies each row by its block scalar. -/
theorem blockScalar_mul_apply (a : Fin B.length → Rˣ) (g : GeneralLinear n R)
    (i j : Fin B.length) (r : Fin (B.size i)) (s : Fin (B.size j)) :
    (B.blockScalar R a * g) (B.index i r) (B.index j s) =
      (a i : R) * g (B.index i r) (B.index j s) := by
  change ((B.blockScalar R a : Matrix (Fin n) (Fin n) R) *
    (g : Matrix (Fin n) (Fin n) R)) _ _ = _
  rw [B.coe_blockScalar, Matrix.diagonal_mul]
  rw [show B.indexEquiv.symm (B.index i r) = ⟨i, r⟩ from
    B.indexEquiv.symm_apply_apply ⟨i, r⟩]

/-- Right block-scalar multiplication multiplies each column by its block scalar. -/
theorem mul_blockScalar_apply (a : Fin B.length → Rˣ) (g : GeneralLinear n R)
    (i j : Fin B.length) (r : Fin (B.size i)) (s : Fin (B.size j)) :
    (g * B.blockScalar R a) (B.index i r) (B.index j s) =
      g (B.index i r) (B.index j s) * (a j : R) := by
  change ((g : Matrix (Fin n) (Fin n) R) *
    (B.blockScalar R a : Matrix (Fin n) (Fin n) R)) _ _ = _
  rw [B.coe_blockScalar, Matrix.mul_diagonal]
  rw [show B.indexEquiv.symm (B.index j s) = ⟨j, s⟩ from
    B.indexEquiv.symm_apply_apply ⟨j, s⟩]

/-- Conjugation on the actual `(i,j)` block has the ratio `a_i/a_j`. -/
theorem blockScalar_conj_apply (a : Fin B.length → Rˣ) (g : GeneralLinear n R)
    (i j : Fin B.length) (r : Fin (B.size i)) (s : Fin (B.size j)) :
    (B.blockScalar R a * g * (B.blockScalar R a)⁻¹) (B.index i r) (B.index j s) =
      ((a i * (a j)⁻¹ : Rˣ) : R) * g (B.index i r) (B.index j s) := by
  rw [← B.blockScalar_inv, B.mul_blockScalar_apply, B.blockScalar_mul_apply]
  simp only [Pi.inv_apply, Units.val_mul]
  ac_rfl

/-- Inverse conjugation has the reciprocal block ratio. -/
theorem blockScalar_inv_conj_apply (a : Fin B.length → Rˣ) (g : GeneralLinear n R)
    (i j : Fin B.length) (r : Fin (B.size i)) (s : Fin (B.size j)) :
    ((B.blockScalar R a)⁻¹ * g * B.blockScalar R a) (B.index i r) (B.index j s) =
      (((a i)⁻¹ * a j : Rˣ) : R) * g (B.index i r) (B.index j s) := by
  simpa only [blockScalar_inv, Pi.inv_apply, inv_inv] using
    B.blockScalar_conj_apply R a⁻¹ g i j r s


variable (K : Subgroup (GeneralLinear n R))

/-- The intersection of `K` with the opposite radical, in the ambient group. -/
def iwahoriLower : Subgroup (GeneralLinear n R) := K ⊓ B.oppositeUnipotentSubgroup R

/-- The intersection of `K` with the common embedded Levi. -/
def iwahoriLevi : Subgroup (GeneralLinear n R) := K ⊓ B.leviSubgroup R

/-- The intersection of `K` with the upper radical, in the ambient group. -/
def iwahoriUpper : Subgroup (GeneralLinear n R) := K ⊓ B.unipotentSubgroup R

@[simp] theorem mem_iwahoriLower (g : GeneralLinear n R) :
    g ∈ B.iwahoriLower R K ↔ g ∈ K ∧ g ∈ B.oppositeUnipotentSubgroup R := Iff.rfl

@[simp] theorem mem_iwahoriLevi (g : GeneralLinear n R) :
    g ∈ B.iwahoriLevi R K ↔ g ∈ K ∧ g ∈ B.leviSubgroup R := Iff.rfl

@[simp] theorem mem_iwahoriUpper (g : GeneralLinear n R) :
    g ∈ B.iwahoriUpper R K ↔ g ∈ K ∧ g ∈ B.unipotentSubgroup R := Iff.rfl

/-- Ordered multiplication of actual opposite, Levi and upper factors into `K`.
This is a map of sets; no direct-product group law is asserted. -/
def iwahoriProduct :
    B.iwahoriLower R K × B.iwahoriLevi R K × B.iwahoriUpper R K → K :=
  fun x => ⟨x.1.val * x.2.1.val * x.2.2.val,
    K.mul_mem (K.mul_mem x.1.property.1 x.2.1.property.1) x.2.2.property.1⟩

@[simp] theorem iwahoriProduct_val
    (x : B.iwahoriLower R K × B.iwahoriLevi R K × B.iwahoriUpper R K) :
    (B.iwahoriProduct R K x).val = x.1.val * x.2.1.val * x.2.2.val := rfl

@[simp] theorem iwahoriProduct_one : B.iwahoriProduct R K (1, 1, 1) = 1 := by
  apply Subtype.ext
  simp

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

/-- The actual root-ratio character in block-scalar coordinates. -/
def blockScalarRatio (i j : Fin B.length) : (Fin B.length → F.Carrierˣ) →* ℝ≥0ˣ where
  toFun a := T.normalizedAbsUnits (a i * (a j)⁻¹)
  map_one' := by simp
  map_mul' a b := by
    simp only [Pi.mul_apply, mul_inv_rev]
    rw [show a i * b i * ((b j)⁻¹ * (a j)⁻¹) =
      (a i * (a j)⁻¹) * (b i * (b j)⁻¹) by ac_rfl, map_mul]

@[simp] theorem blockScalarRatio_apply (a : Fin B.length → F.Carrierˣ)
    (i j : Fin B.length) :
    B.blockScalarRatio T i j a = T.normalizedAbsUnits (a i * (a j)⁻¹) := rfl

/-- Weak contraction of the upper radical: every forward block ratio is at most one. -/
def IsWeaklyContracting (a : Fin B.length → F.Carrierˣ) : Prop :=
  ∀ i j : Fin B.length, i < j → (((B.blockScalarRatio T i j a : ℝ≥0) : ℝ) ≤ 1)

/-- Strict contraction of the upper radical: every forward block ratio is below one. -/
def IsStrictlyContracting (a : Fin B.length → F.Carrierˣ) : Prop :=
  ∀ i j : Fin B.length, i < j → (((B.blockScalarRatio T i j a : ℝ≥0) : ℝ) < 1)

/-- The ratio inequalities alone; consumers separately impose `0 < ε` and `ε ≤ 1`. -/
def IsDeeplyContracting (ε : ℝ) (a : Fin B.length → F.Carrierˣ) : Prop :=
  ∀ i j : Fin B.length, i < j → (((B.blockScalarRatio T i j a : ℝ≥0) : ℝ) < ε)

@[simp] theorem isWeaklyContracting_one : B.IsWeaklyContracting T 1 := by
  intro i j _
  simp

/-- Central scalar tuples satisfy every weak inequality without a size bound. -/
theorem isWeaklyContracting_const (a : F.Carrierˣ) :
    B.IsWeaklyContracting T (fun _ => a) := by
  intro i j _
  simp

theorem IsStrictlyContracting.weak {a : Fin B.length → F.Carrierˣ}
    (ha : B.IsStrictlyContracting T a) : B.IsWeaklyContracting T a :=
  fun i j hij => (ha i j hij).le

theorem IsDeeplyContracting.strict {ε : ℝ} {a : Fin B.length → F.Carrierˣ}
    (ha : B.IsDeeplyContracting T ε a) (hε : ε ≤ 1) : B.IsStrictlyContracting T a :=
  fun i j hij => (ha i j hij).trans_le hε

theorem IsWeaklyContracting.mul {a b : Fin B.length → F.Carrierˣ}
    (ha : B.IsWeaklyContracting T a) (hb : B.IsWeaklyContracting T b) :
    B.IsWeaklyContracting T (a * b) := by
  intro i j hij
  rw [map_mul, Units.val_mul, NNReal.coe_mul]
  calc
    _ ≤ 1 * 1 := mul_le_mul (ha i j hij) (hb i j hij) (by positivity) zero_le_one
    _ = 1 := one_mul 1

/-- With at most one block there are no contracting inequalities, even at rank zero. -/
theorem isDeeplyContracting_of_length_le_one (hB : B.length ≤ 1)
    (ε : ℝ) (a : Fin B.length → F.Carrierˣ) : B.IsDeeplyContracting T ε a := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have hij' : i.val < j.val := hij
  omega

/-- A weak-chamber version of block Iwahori factorization for an actual open subgroup.
Compactness is deliberately a separate `IsCompact (K : Set _)` hypothesis. -/
def HasBlockIwahoriFactorization :
    letI := T.topology
    OpenSubgroup (GeneralLinear n F.Carrier) → Prop :=
  letI := T.topology
  fun K =>
    Function.Bijective (B.iwahoriProduct F.Carrier K.toSubgroup) ∧
    ∀ a : Fin B.length → F.Carrierˣ, B.IsWeaklyContracting T a →
      (∀ g ∈ B.iwahoriUpper F.Carrier K.toSubgroup,
        B.blockScalar F.Carrier a * g * (B.blockScalar F.Carrier a)⁻¹ ∈
          B.iwahoriUpper F.Carrier K.toSubgroup) ∧
      (∀ g ∈ B.iwahoriLower F.Carrier K.toSubgroup,
        (B.blockScalar F.Carrier a)⁻¹ * g * B.blockScalar F.Carrier a ∈
          B.iwahoriLower F.Carrier K.toSubgroup)

theorem HasBlockIwahoriFactorization.bijective :
    letI := T.topology
    ∀ {K : OpenSubgroup (GeneralLinear n F.Carrier)},
      B.HasBlockIwahoriFactorization T K →
        Function.Bijective (B.iwahoriProduct F.Carrier K.toSubgroup) := by
  let := T.topology
  intro K hK
  exact hK.1

theorem HasBlockIwahoriFactorization.upper_conj_mem :
    letI := T.topology
    ∀ {K : OpenSubgroup (GeneralLinear n F.Carrier)},
      B.HasBlockIwahoriFactorization T K →
      ∀ {a : Fin B.length → F.Carrierˣ}, B.IsWeaklyContracting T a →
      ∀ {g : GeneralLinear n F.Carrier}, g ∈ B.iwahoriUpper F.Carrier K.toSubgroup →
        B.blockScalar F.Carrier a * g * (B.blockScalar F.Carrier a)⁻¹ ∈
          B.iwahoriUpper F.Carrier K.toSubgroup := by
  let := T.topology
  intro K hK a ha g hg
  exact (hK.2 a ha).1 g hg

theorem HasBlockIwahoriFactorization.lower_inv_conj_mem :
    letI := T.topology
    ∀ {K : OpenSubgroup (GeneralLinear n F.Carrier)},
      B.HasBlockIwahoriFactorization T K →
      ∀ {a : Fin B.length → F.Carrierˣ}, B.IsWeaklyContracting T a →
      ∀ {g : GeneralLinear n F.Carrier}, g ∈ B.iwahoriLower F.Carrier K.toSubgroup →
        (B.blockScalar F.Carrier a)⁻¹ * g * B.blockScalar F.Carrier a ∈
          B.iwahoriLower F.Carrier K.toSubgroup := by
  let := T.topology
  intro K hK a ha g hg
  exact (hK.2 a ha).2 g hg

end Padic
end Langlands.GeneralLinear.BlockShape
