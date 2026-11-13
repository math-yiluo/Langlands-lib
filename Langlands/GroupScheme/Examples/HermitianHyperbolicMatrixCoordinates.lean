import Langlands.GroupScheme.Examples.HermitianHyperbolicReduction

/-! # Matrix coordinates for a hyperbolic Hermitian splitting -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

variable {A : Type u} [CommRing A] {ι : Type v}

/-- The standard top, middle and bottom function coordinates as a product. -/
def indexProductCoordinates : (Index ι → A) ≃ₗ[A] A × ((ι → A) × A) where
  toFun z := (z (Sum.inl ()), (fun i => z (Sum.inr (Sum.inl i)), z (Sum.inr (Sum.inr ()))))
  invFun z := Sum.elim (fun _ => z.1) (Sum.elim z.2.1 (fun _ => z.2.2))
  left_inv z := by
    funext i
    rcases i with ⟨⟩ | i | ⟨⟩ <;> rfl
  right_inv z := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [Fintype ι] [DecidableEq ι] {c : RingInvolution A}

@[simp] theorem gram_mulVec_top (H : DiagonalForm c ι) (z : Index ι → A) (i : Unit) :
    (gram H).mulVec z (Sum.inl i) = z (Sum.inr (Sum.inr ())) := by
  cases i
  simp [Matrix.mulVec, dotProduct, gram, Matrix.fromBlocks, Fintype.sum_sum_type]

@[simp] theorem gram_mulVec_middle (H : DiagonalForm c ι) (z : Index ι → A) (i : ι) :
    (gram H).mulVec z (Sum.inr (Sum.inl i)) =
      -H.weight i * z (Sum.inr (Sum.inl i)) := by
  simp [Matrix.mulVec, dotProduct, gram, Matrix.fromBlocks, Fintype.sum_sum_type,
    Matrix.diagonal_apply]

@[simp] theorem gram_mulVec_bottom (H : DiagonalForm c ι) (z : Index ι → A) (i : Unit) :
    (gram H).mulVec z (Sum.inr (Sum.inr i)) = z (Sum.inl ()) := by
  cases i
  simp [Matrix.mulVec, dotProduct, gram, Matrix.fromBlocks, Fintype.sum_sum_type]

/-- The actual Gram matrix induces the hyperbolic cross-minus-middle pairing,
in the convention linear in the first vector. -/
theorem gram_mulVec_pairing (H : DiagonalForm c ι) (z w : Index ι → A) :
    dotProduct (fun i => c.bar (w i)) ((gram H).mulVec z) =
      z (Sum.inl ()) * c.bar (w (Sum.inr (Sum.inr ()))) -
        H.pairing (fun i => z (Sum.inr (Sum.inl i)))
          (fun i => w (Sum.inr (Sum.inl i))) +
        z (Sum.inr (Sum.inr ())) * c.bar (w (Sum.inl ())) := by
  simp only [dotProduct, Fintype.sum_sum_type, Fintype.sum_unique,
    gram_mulVec_top, gram_mulVec_middle, gram_mulVec_bottom, DiagonalForm.pairing]
  have hs : (∑ i, c.bar (w (Sum.inr (Sum.inl i))) *
      (-H.weight i * z (Sum.inr (Sum.inl i)))) =
      -(∑ i, H.weight i * z (Sum.inr (Sum.inl i)) *
        c.bar (w (Sum.inr (Sum.inl i)))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

/-- The actual invertible matrix of a linear coordinate equivalence. -/
def linearCoordinateMatrix (e : (Index ι → A) ≃ₗ[A] (Index ι → A)) :
    Matrix.GeneralLinearGroup (Index ι) A :=
  Units.map LinearMap.toMatrixAlgEquiv'.toMonoidHom
    (LinearMap.GeneralLinearGroup.ofLinearEquiv e)

@[simp] theorem linearCoordinateMatrix_apply
    (e : (Index ι → A) ≃ₗ[A] (Index ι → A)) (i j : Index ι) :
    (linearCoordinateMatrix e : Matrix (Index ι) (Index ι) A) i j =
      e (Pi.single j 1) i := rfl

@[simp] theorem linearCoordinateMatrix_mulVec
    (e : (Index ι → A) ≃ₗ[A] (Index ι → A)) (z : Index ι → A) :
    (linearCoordinateMatrix e : Matrix (Index ι) (Index ι) A).mulVec z = e z :=
  LinearMap.toMatrix'_mulVec e.toLinearMap z

/-- Equality of the actual full pairings yields the corresponding actual
invertible Gram congruence. -/
theorem gramCongruence_of_pairing_coordinates
    (J : Matrix (Index ι) (Index ι) A) (H : DiagonalForm c ι)
    (e : (Index ι → A) ≃ₗ[A] (Index ι → A))
    (he : ∀ z w, dotProduct (fun i => c.bar (w i)) (J.mulVec z) =
      dotProduct (fun i => c.bar (e w i)) ((gram H).mulVec (e z))) :
    conjugateTranspose c (linearCoordinateMatrix e : Matrix (Index ι) (Index ι) A) *
      gram H * (linearCoordinateMatrix e : Matrix (Index ι) (Index ι) A) = J := by
  ext i j
  calc
    _ = dotProduct (fun k => c.bar (e (Pi.single i 1) k))
        ((gram H).mulVec (e (Pi.single j 1))) := by
      simp only [Matrix.mul_apply, conjugateTranspose, Matrix.transpose_apply,
        Matrix.map_apply, linearCoordinateMatrix_apply, dotProduct, Matrix.mulVec,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = dotProduct (fun k => c.bar ((Pi.single i (1 : A) : Index ι → A) k))
        (J.mulVec (Pi.single j 1)) := (he (Pi.single j 1) (Pi.single i 1)).symm
    _ = J i j := by
      simp [dotProduct, Matrix.mulVec, Pi.single_apply]

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {V : Type w} [AddCommGroup V] [Module L V]
  (h : V →ₗ[L] V →ₛₗ[(fieldInvolution K L).bar.toRingHom] L)
  (hbar : ∀ x y, (fieldInvolution K L).bar (h x y) = h y x)

include hbar in
/-- A rank-one Hermitian space has actual function coordinates whose pairing
is given by the Library's hyperbolic-plus-diagonal Gram matrix. -/
theorem exists_rankOne_gram_coordinates [FiniteDimensional L V]
    (hn : h.Nondegenerate) {x : V} (hx : x ≠ 0) (hxx : h x x = 0)
    (hrank : ∀ W : Submodule L V,
      (∀ a b : W, h (a : V) (b : V) = 0) → Module.finrank L W ≤ 1)
    (m : ℕ) (hdim : Module.finrank L V = m + 2) :
    ∃ H : DiagonalForm (fieldInvolution K L) (Fin m), H.IsAnisotropic ∧
      ∃ e : V ≃ₗ[L] (Index (Fin m) → L), ∀ v w,
        h v w = dotProduct (fun i => (fieldInvolution K L).bar (e w i))
          ((gram H).mulVec (e v)) := by
  obtain ⟨H, hH, f, hf⟩ :=
    exists_rankOne_diagonal_coordinates hbar hn hx hxx hrank m hdim
  let e := f.trans indexProductCoordinates.symm
  refine ⟨H, hH, e, ?_⟩
  intro v w
  rw [gram_mulVec_pairing]
  exact hf v w

/-- A supplied matrix pairing of Witt index one is congruent, through an actual
invertible matrix, to a hyperbolic plane with negative anisotropic diagonal middle. -/
theorem exists_rankOne_gram_congruence {m : ℕ}
    (h : (Index (Fin m) → L) →ₗ[L]
      (Index (Fin m) → L) →ₛₗ[(fieldInvolution K L).bar.toRingHom] L)
    (hbar : ∀ x y, (fieldInvolution K L).bar (h x y) = h y x)
    (J : Matrix (Index (Fin m)) (Index (Fin m)) L)
    (hJ : ∀ z w, h z w =
      dotProduct (fun i => (fieldInvolution K L).bar (w i)) (J.mulVec z))
    (hn : h.Nondegenerate) {x : Index (Fin m) → L}
    (hx : x ≠ 0) (hxx : h x x = 0)
    (hrank : ∀ W : Submodule L (Index (Fin m) → L),
      (∀ a b : W, h (a : Index (Fin m) → L) (b : Index (Fin m) → L) = 0) →
        Module.finrank L W ≤ 1) :
    ∃ H : DiagonalForm (fieldInvolution K L) (Fin m), H.IsAnisotropic ∧
      ∃ P : Matrix.GeneralLinearGroup (Index (Fin m)) L,
        conjugateTranspose (fieldInvolution K L)
            (P : Matrix (Index (Fin m)) (Index (Fin m)) L) *
          gram H * (P : Matrix (Index (Fin m)) (Index (Fin m)) L) = J := by
  have hdim : Module.finrank L (Index (Fin m) → L) = m + 2 := by
    simp only [Module.finrank_fintype_fun_eq_card, Index, Fintype.card_sum,
      Fintype.card_unit, Fintype.card_fin]
    omega
  obtain ⟨H, hH, e, he⟩ :=
    exists_rankOne_gram_coordinates h hbar hn hx hxx hrank m hdim
  refine ⟨H, hH, linearCoordinateMatrix e, ?_⟩
  apply gramCongruence_of_pairing_coordinates
  intro z w
  exact (hJ z w).symm.trans (he z w)

end Langlands.GroupScheme.HermitianRoot
