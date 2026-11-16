import Langlands.Automorphic.ConstantTerm
import Langlands.Group.GL.Maps
import Langlands.Global.RankinSelberg.UnequalAnalyticPoints

/-! # Cuspidality of the transpose-inverse dual

For a continuous rational-left-invariant function `f` on `GL_n(𝔸_K)`, the function
`g ↦ f(ᵗg⁻¹)` is again continuous and rational-left-invariant (`transposeDual`). Its constant
term along the `(a, b)` block parabolic is a constant term of `f` along the `(b, a)` block
parabolic, at a translated point (`constantTerm_transposeDual`). Hence `f` cuspidal implies the
dual cuspidal (`isCuspidal_transposeDual`).

The matrix identity behind this is `ᵗu(Y)⁻¹ = P u'(-ᵗY) P⁻¹`. Here `u(Y)` is the upper block
unipotent with blocks `(a, b)`, `u'` is the one with blocks `(b, a)`, and `P` is the rational
permutation matrix exchanging the two blocks (`inverseTranspose_blockUnipotent`). The change of
variables `X ↦ -ᵗX` carries the normalized Haar measure of the `a × b` matrices over `𝔸_K / K`
to that of the `b × a` matrices, by uniqueness of Haar probability measures. -/

noncomputable section
universe u
open MeasureTheory
open scoped NumberField
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.GeneralLinear ContinuousRationalFunctions

section Matrices

variable {R : Type*} [CommRing R] {a b n : ℕ}

/-- The consecutive block numbering `Fin a ⊕ Fin b ≃ Fin n` used by `blockUnipotent`. -/
abbrev blockEquiv (h : a + b = n) : Fin a ⊕ Fin b ≃ Fin n :=
  finSumFinEquiv.trans (finCongr h)

/-- The permutation of `Fin n` exchanging the blocks: it sends the `(b, a)` block index of `p`
to the `(a, b)` block index of `p.swap`. -/
def blockSwap (h : a + b = n) : Equiv.Perm (Fin n) :=
  ((blockEquiv ((Nat.add_comm b a).trans h)).symm.trans (Equiv.sumComm (Fin b) (Fin a))).trans
    (blockEquiv h)

theorem blockSwap_inv_apply (h : a + b = n) (p : Fin a ⊕ Fin b) :
    (blockSwap h)⁻¹ (blockEquiv h p) = blockEquiv ((Nat.add_comm b a).trans h) p.swap := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
  change blockEquiv h p = blockEquiv h (Equiv.sumComm (Fin b) (Fin a)
    ((blockEquiv ((Nat.add_comm b a).trans h)).symm
      (blockEquiv ((Nat.add_comm b a).trans h) p.swap)))
  rw [Equiv.symm_apply_apply, Equiv.sumComm_apply, Sum.swap_swap]

theorem blockUnipotent_apply_blockEquiv (h : a + b = n) (X : Matrix (Fin a) (Fin b) R)
    (p q : Fin a ⊕ Fin b) :
    (blockUnipotent h X : Matrix (Fin n) (Fin n) R) (blockEquiv h p) (blockEquiv h q) =
      Matrix.fromBlocks 1 X 0 1 p q := by
  rw [blockUnipotent_val, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

theorem blockUnipotent_inv (h : a + b = n) (X : Matrix (Fin a) (Fin b) R) :
    (blockUnipotent h X)⁻¹ = blockUnipotent h (-X) :=
  inv_eq_of_mul_eq_one_right (by rw [← blockUnipotent_add, add_neg_cancel, blockUnipotent_zero])

/-- **Transpose inverse of a block unipotent.** `ᵗu(Y)⁻¹ = P u'(-ᵗY) P⁻¹`, with `P` the
permutation matrix of `blockSwap`. -/
theorem inverseTranspose_blockUnipotent (h : a + b = n) (Y : Matrix (Fin a) (Fin b) R) :
    inverseTranspose n R (blockUnipotent h Y) =
      permutation n R (blockSwap h) * blockUnipotent ((Nat.add_comm b a).trans h) (-Y.transpose) *
        (permutation n R (blockSwap h))⁻¹ := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [permutation_conjugate_entry, inverseTranspose_entry, blockUnipotent_inv]
  obtain ⟨p, rfl⟩ := (blockEquiv h).surjective i
  obtain ⟨q, rfl⟩ := (blockEquiv h).surjective j
  rw [blockSwap_inv_apply, blockSwap_inv_apply, blockUnipotent_apply_blockEquiv,
    blockUnipotent_apply_blockEquiv]
  rcases p with p | p <;> rcases q with q | q
  · simp only [Sum.swap_inl, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]
    rw [Matrix.one_apply, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  · simp only [Sum.swap_inl, Sum.swap_inr, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
  · simp only [Sum.swap_inl, Sum.swap_inr, Matrix.fromBlocks_apply₁₂, Matrix.neg_apply,
      Matrix.transpose_apply]
  · simp only [Sum.swap_inr, Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₁₁]
    rw [Matrix.one_apply, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl

/-- Permutation matrices are compatible with ring homomorphisms. -/
theorem map_permutation {S : Type*} [CommRing S] (φ : R →+* S) (σ : Equiv.Perm (Fin n)) :
    Matrix.GeneralLinearGroup.map φ (permutation n R σ) = permutation n S σ := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Matrix.GeneralLinearGroup.map_apply, permutation_entry, permutation_entry]
  split_ifs <;> simp

end Matrices

variable {K : Type u} [Field K] [NumberField K] {n : ℕ}

theorem inverseTranspose_rational (γ : RationalGL K n) :
    inverseTranspose n (NumberField.AdeleRing (𝓞 K) K) (AdelicGL.rational K n γ) =
      AdelicGL.rational K n (inverseTranspose n K γ) :=
  RankinSelbergGlobal.UnequalAnalytic.inverseTranspose_map _ γ

theorem permutation_eq_rational (σ : Equiv.Perm (Fin n)) :
    permutation n (NumberField.AdeleRing (𝓞 K) K) σ = AdelicGL.rational K n (permutation n K σ) :=
  (map_permutation _ σ).symm

namespace ContinuousRationalFunctions

/-- The transpose-inverse dual `g ↦ f(ᵗg⁻¹)` of a continuous rational-left-invariant
function. -/
def transposeDual (f : ContinuousRationalFunctions K n) : ContinuousRationalFunctions K n :=
  ⟨⟨fun x => evaluate K n f (inverseTranspose n (NumberField.AdeleRing (𝓞 K) K) x), by
      intro γ x
      change evaluate K n f (inverseTranspose n _ (AdelicGL.rational K n γ * x)) =
        evaluate K n f (inverseTranspose n _ x)
      rw [map_mul, inverseTranspose_rational]
      exact evaluate_rational K n f _ _⟩,
    (continuous_evaluate K n f).comp (continuous_inverseTranspose n _)⟩

@[simp]
theorem evaluate_transposeDual (f : ContinuousRationalFunctions K n) (x : AdelicGL K n) :
    evaluate K n (transposeDual f) x = evaluate K n f (inverseTranspose n _ x) := rfl

end ContinuousRationalFunctions

section Measure

variable (K)

/-- The continuous additive equivalence `X ↦ -ᵗX` between the `a × b` and the `b × a`
matrices over `𝔸_K / K`. -/
def transposeNegEquiv (a b : ℕ) :
    Matrix (Fin a) (Fin b) (AdeleQuotient K) ≃ₜ+ Matrix (Fin b) (Fin a) (AdeleQuotient K) where
  toFun X := -X.transpose
  invFun Y := -Y.transpose
  left_inv X := by simp
  right_inv Y := by simp
  map_add' X Y := by rw [Matrix.transpose_add, neg_add]
  continuous_toFun := continuous_id.matrix_transpose.neg
  continuous_invFun := continuous_id.matrix_transpose.neg

theorem transposeNegEquiv_apply {a b : ℕ} (X : Matrix (Fin a) (Fin b) (AdeleQuotient K)) :
    transposeNegEquiv K a b X = -X.transpose := rfl

variable [CompactSpace (AdeleQuotient K)]

/-- `X ↦ -ᵗX` carries the normalized Haar measure to the normalized Haar measure. -/
theorem map_transposeNegEquiv_matrixQuotientHaar (a b : ℕ) :
    letI : MeasurableSpace (Matrix (Fin a) (Fin b) (AdeleQuotient K)) := borel _
    letI : MeasurableSpace (Matrix (Fin b) (Fin a) (AdeleQuotient K)) := borel _
    (matrixQuotientHaar K a b).map (transposeNegEquiv K a b) = matrixQuotientHaar K b a := by
  let : MeasurableSpace (Matrix (Fin a) (Fin b) (AdeleQuotient K)) := borel _
  have : BorelSpace (Matrix (Fin a) (Fin b) (AdeleQuotient K)) := ⟨rfl⟩
  let : MeasurableSpace (Matrix (Fin b) (Fin a) (AdeleQuotient K)) := borel _
  have : BorelSpace (Matrix (Fin b) (Fin a) (AdeleQuotient K)) := ⟨rfl⟩
  have := matrixQuotientHaar_isAddHaarMeasure K a b
  have := matrixQuotientHaar_isAddHaarMeasure K b a
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- Change of variables `X ↦ -ᵗX` in an integral over the matrices over `𝔸_K / K`. -/
theorem integral_transposeNegEquiv {a b : ℕ}
    (G : Matrix (Fin b) (Fin a) (AdeleQuotient K) → ℂ) :
    ∫ X, G (transposeNegEquiv K a b X) ∂(matrixQuotientHaar K a b) =
      ∫ Y, G Y ∂(matrixQuotientHaar K b a) := by
  let : MeasurableSpace (Matrix (Fin a) (Fin b) (AdeleQuotient K)) := borel _
  have : BorelSpace (Matrix (Fin a) (Fin b) (AdeleQuotient K)) := ⟨rfl⟩
  let : MeasurableSpace (Matrix (Fin b) (Fin a) (AdeleQuotient K)) := borel _
  have : BorelSpace (Matrix (Fin b) (Fin a) (AdeleQuotient K)) := ⟨rfl⟩
  rw [← map_transposeNegEquiv_matrixQuotientHaar K a b]
  exact (integral_map_equiv (transposeNegEquiv K a b).toHomeomorph.toMeasurableEquiv G).symm

end Measure

variable [CompactSpace (AdeleQuotient K)]

omit [CompactSpace (AdeleQuotient K)] in
theorem matrixQuotientMap_neg_transpose {a b : ℕ} (Y : Matrix (Fin a) (Fin b) (Adeles K)) :
    matrixQuotientMap (-Y.transpose) = transposeNegEquiv K a b (matrixQuotientMap Y) := by
  ext i j
  simp [matrixQuotientMap, transposeNegEquiv_apply, Matrix.map_apply, Matrix.transpose_apply,
    Matrix.neg_apply, map_neg]

/-- **The constant terms of the transpose-inverse dual.** The `(a, b)` constant term of
`g ↦ f(ᵗg⁻¹)` at `g` is the `(b, a)` constant term of `f` at `P⁻¹ ᵗg⁻¹`, where `P` is the
rational block-exchanging permutation matrix. -/
theorem constantTerm_transposeDual {a b : ℕ} (h : a + b = n)
    (f : ContinuousRationalFunctions K n) (g : AdelicGL K n) :
    constantTerm K n h (transposeDual f) g =
      constantTerm K n ((Nat.add_comm b a).trans h) f
        ((AdelicGL.rational K n (permutation n K (blockSwap h)))⁻¹ *
          inverseTranspose n (NumberField.AdeleRing (𝓞 K) K) g) := by
  unfold constantTerm
  rw [← integral_transposeNegEquiv K (a := a) (b := b) (constantTermIntegrand K n _ f _)]
  congr 1
  funext X
  set P := AdelicGL.rational K n (permutation n K (blockSwap h))
  rw [← matrixQuotientMap_matrixLift X, ← matrixQuotientMap_neg_transpose,
    constantTermIntegrand_mk, constantTermIntegrand_mk, evaluate_transposeDual, map_mul,
    inverseTranspose_blockUnipotent, permutation_eq_rational, mul_assoc, mul_assoc,
    evaluate_rational]

/-- **The transpose-inverse dual of a cuspidal function is cuspidal.** -/
theorem isCuspidal_transposeDual {f : ContinuousRationalFunctions K n} (hf : IsCuspidal K n f) :
    IsCuspidal K n (transposeDual f) := by
  intro a b h ha hb g
  rw [constantTerm_transposeDual]
  exact hf b a _ hb ha _

end Langlands.Automorphic
