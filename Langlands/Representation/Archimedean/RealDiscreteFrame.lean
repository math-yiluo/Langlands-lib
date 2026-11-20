import Langlands.Representation.Archimedean.RealDiscreteMinorCyclic
import Langlands.Representation.Archimedean.RealDiscreteScalarFunctional
import Langlands.Representation.Archimedean.RealDiscretePresentation

/-!
# Frame vectors and the scalar step

Let `T` be an `O(n)`-fixed vector of the module of `ps`, and let `qs` be the twist of `ps` by
the product of the bottom minors with rows `R_j` (`IsMinorShift`). For a complex matrix `U`
and column sets `D_j`, the frame vector `u_D` is the function
`g ↦ T(g) ∏_j det (g U)_{R_j, D_j}` in the module of `qs`. When `U` is invertible, the
`O(n)`-translates of a frame vector are combinations of frame vectors, and every product
`T · ∏_j Δ_{R_j, C_j}` is a combination of frame vectors.

The main theorem `hasScalarCommutant_of_frame` is an abstract scalar step. Suppose that `T`
generates its module under the Lie algebra, that `Φ` is a surjective `(𝔤, K)`-intertwiner from
the module of `qs` onto that of `ds`, and that for every `O(n)`-equivariant `L` the values
`(L u_D)(1)` are multiples `ε_D (L u_{D₀})(1)`. Then every endomorphism of the module of `ds`
commuting with `O(n)` and the Lie algebra is a scalar.
-/

noncomputable section

open Matrix Finset

open scoped Manifold ContDiff TensorProduct

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean Langlands.GeneralLinear

set_option autoImplicit false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealDiscreteFrame

open MatrixMinor RealTemperedCommutantReduction RealTiedMinorProduct RealDiscreteMinorCyclic
  RealDiscreteScalar

variable {n : ℕ}

/-! ## Cauchy–Binet over all column sets -/

theorem sum_minor_mul_minor {S : Type*} [CommRing S] (X Y : Matrix (Fin n) (Fin n) S)
    (A B : Finset (Fin n)) :
    ∑ C : Finset (Fin n), minor X A C * minor Y C B = minor (X * Y) A B := by
  by_cases hB : B.card = A.card
  · rw [minor_mul X Y rfl hB]
    symm
    refine Finset.sum_subset (subset_univ _) fun C _ hC => ?_
    have h : A.card ≠ C.card := fun h => hC (mem_powersetCard.mpr ⟨subset_univ _, h.symm⟩)
    rw [minor_of_card_ne h, zero_mul]
  · rw [minor_of_card_ne (Ne.symm hB)]
    refine Finset.sum_eq_zero fun C _ => ?_
    by_cases hC : A.card = C.card
    · have h : C.card ≠ B.card := fun h => hB (hC.trans h).symm
      rw [minor_of_card_ne h, mul_zero]
    · rw [minor_of_card_ne hC, zero_mul]

/-- Cauchy–Binet for a product of minors with several row and column sets. -/
theorem prod_minor_mul {S : Type*} [CommRing S] {N : ℕ} (X Y : Matrix (Fin n) (Fin n) S)
    (A B : Fin N → Finset (Fin n)) :
    ∏ j, minor (X * Y) (A j) (B j) =
      ∑ C : Fin N → Finset (Fin n), ∏ j, (minor X (A j) (C j) * minor Y (C j) (B j)) := by
  rw [← Fintype.prod_sum (fun j (C : Finset (Fin n)) => minor X (A j) C * minor Y C (B j))]
  exact Finset.prod_congr rfl fun j _ => (sum_minor_mul_minor X Y (A j) (B j)).symm

/-- Swapping two adjacent columns `p`, `p + 1` of `X` moves the column set of a minor by the
swap, when the column set does not contain both. -/
theorem swap_lt_swap {p q : Fin n} (hpq : (q : ℕ) = p + 1) {D : Finset (Fin n)}
    (hD : ¬ (p ∈ D ∧ q ∈ D)) {x y : Fin n} (hx : x ∈ D) (hy : y ∈ D) (hxy : x < y) :
    Equiv.swap p q x < Equiv.swap p q y := by
  have hne : ¬ (x = p ∧ y = q) := fun h => hD ⟨h.1 ▸ hx, h.2 ▸ hy⟩
  rw [Fin.lt_def] at hxy ⊢
  by_cases hxp : x = p
  · have hyq : y ≠ q := fun h => hne ⟨hxp, h⟩
    have hyp : y ≠ p := fun h => by rw [Fin.ext_iff] at hxp h; omega
    rw [hxp, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hyp hyq]
    have h1 : (y : ℕ) ≠ q := fun h => hyq (Fin.ext h)
    rw [Fin.ext_iff] at hxp
    omega
  · by_cases hxq : x = q
    · have hyp : y ≠ p := fun h => by rw [Fin.ext_iff] at hxq h; omega
      have hyq : y ≠ q := fun h => by rw [Fin.ext_iff] at hxq h; omega
      rw [hxq, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hyp hyq]
      rw [Fin.ext_iff] at hxq
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hxp hxq]
      by_cases hyp : y = p
      · rw [hyp, Equiv.swap_apply_left]
        rw [Fin.ext_iff] at hyp
        omega
      · by_cases hyq : y = q
        · rw [hyq, Equiv.swap_apply_right]
          have h1 : (x : ℕ) ≠ p := fun h => hxp (Fin.ext h)
          rw [Fin.ext_iff] at hyq
          omega
        · rw [Equiv.swap_apply_of_ne_of_ne hyp hyq]
          exact hxy

theorem minor_submatrix_swap {S : Type*} [CommRing S] (X : Matrix (Fin n) (Fin n) S)
    (A D : Finset (Fin n)) {p q : Fin n} (hpq : (q : ℕ) = p + 1) (hD : ¬ (p ∈ D ∧ q ∈ D)) :
    minor (X.submatrix id (Equiv.swap p q)) A D =
      minor X A (D.map (Equiv.swap p q).toEmbedding) := by
  have hc' : (D.map (Equiv.swap p q).toEmbedding).card = D.card := card_map _
  by_cases hc : A.card = D.card
  · rw [minor_eq rfl hc.symm, minor_eq rfl (hc'.trans hc.symm)]
    have he : ∀ i, Equiv.swap p q (D.orderEmbOfFin hc.symm i) =
        (D.map (Equiv.swap p q).toEmbedding).orderEmbOfFin (hc'.trans hc.symm) i := by
      intro i
      have h := Finset.orderEmbOfFin_unique (s := D.map (Equiv.swap p q).toEmbedding)
        (hc'.trans hc.symm) (f := fun i => Equiv.swap p q (D.orderEmbOfFin hc.symm i))
        (fun i => mem_map_of_mem _ (orderEmbOfFin_mem _ _ _))
        (fun i j hij => swap_lt_swap hpq hD (orderEmbOfFin_mem _ _ _) (orderEmbOfFin_mem _ _ _)
          ((D.orderEmbOfFin hc.symm).strictMono hij))
      exact congrFun h i
    congr 1
    ext i j
    simp only [Matrix.submatrix_apply, id]
    rw [he]
  · rw [minor_of_card_ne hc, minor_of_card_ne (by rwa [hc'])]

/-! ## Complex matrices of group elements -/

/-- The complex matrix of `g ∈ GL_n(ℝ)`. -/
def cmat (g : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (g : Matrix (Fin n) (Fin n) ℝ).map Complex.ofRealHom

/-- The complex matrix of `k ∈ O(n)`. -/
def kmat (k : Matrix.unitaryGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (k : Matrix (Fin n) (Fin n) ℝ).map Complex.ofRealHom

theorem cmat_mul_toUnits (g : Langlands.GeneralLinear n ℝ) (k : Matrix.unitaryGroup (Fin n) ℝ) :
    cmat (g * Unitary.toUnits k) = cmat g * kmat k := by
  unfold cmat kmat
  rw [Units.val_mul, Matrix.map_mul]
  rfl

theorem minorG_eq (A B : Finset (Fin n)) (g : Langlands.GeneralLinear n ℝ) :
    minorG A B g = minor (cmat g) A B := by
  unfold minorG cmat
  rw [minor_map]
  rfl

theorem apply_mul_toUnits {ds : List RealBlock} {T : KF n ds}
    (hT : ∀ k, realStandardRep n ds k T = T) (g : Langlands.GeneralLinear n ℝ)
    (k : Matrix.unitaryGroup (Fin n) ℝ) :
    (T : Langlands.GeneralLinear n ℝ → ℂ) (g * Unitary.toUnits k) =
      (T : Langlands.GeneralLinear n ℝ → ℂ) g := by
  have h : ((realStandardRep n ds k T : KF n ds) : Langlands.GeneralLinear n ℝ → ℂ) g =
      (T : Langlands.GeneralLinear n ℝ → ℂ) g := by rw [hT k]
  rw [realStandardRep_apply_coe] at h
  exact h

/-! ## Frame vectors -/

variable {ps qs : List RealBlock} {N : ℕ} {R : Fin N → Finset (Fin n)}

/-- The frame vector `g ↦ T(g) ∏_j det (g U)_{R_j, D_j}`, written as a combination of the
products `T · ∏_j Δ_{R_j, D'_j}`. -/
def frameVec (hsh : IsMinorShift n ps qs R) (T : KF n ps) (U : Matrix (Fin n) (Fin n) ℂ)
    (D : Fin N → Finset (Fin n)) : KF n qs :=
  ∑ D' : Fin N → Finset (Fin n), (∏ j, minor U (D' j) (D j)) • mulProd hsh D' T

theorem frameVec_apply (hsh : IsMinorShift n ps qs R) (T : KF n ps)
    (U : Matrix (Fin n) (Fin n) ℂ) (D : Fin N → Finset (Fin n)) (g : Langlands.GeneralLinear n ℝ) :
    ((frameVec hsh T U D : KF n qs) : Langlands.GeneralLinear n ℝ → ℂ) g =
      (T : Langlands.GeneralLinear n ℝ → ℂ) g * ∏ j, minor (cmat g * U) (R j) (D j) := by
  rw [prod_minor_mul, Finset.mul_sum]
  unfold frameVec
  rw [Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [Submodule.coe_smul, Pi.smul_apply, mulProd_coe, prodG_apply, smul_eq_mul,
    Finset.prod_mul_distrib]
  simp only [minorG_eq]
  ring

theorem rep_frameVec_apply (hsh : IsMinorShift n ps qs R) {T : KF n ps}
    (hT : ∀ k, realStandardRep n ps k T = T) (U : Matrix (Fin n) (Fin n) ℂ)
    (D : Fin N → Finset (Fin n)) (k : Matrix.unitaryGroup (Fin n) ℝ)
    (g : Langlands.GeneralLinear n ℝ) :
    ((realStandardRep n qs k (frameVec hsh T U D) : KF n qs) :
        Langlands.GeneralLinear n ℝ → ℂ) g =
      (T : Langlands.GeneralLinear n ℝ → ℂ) g * ∏ j, minor (cmat g * kmat k * U) (R j) (D j) := by
  rw [realStandardRep_apply_coe]
  change ((frameVec hsh T U D : KF n qs) : Langlands.GeneralLinear n ℝ → ℂ)
    (g * Unitary.toUnits k) = _
  rw [frameVec_apply, apply_mul_toUnits hT, cmat_mul_toUnits]

/-- The `O(n)`-translates of a frame vector are combinations of frame vectors. -/
theorem rep_frameVec (hsh : IsMinorShift n ps qs R) {T : KF n ps}
    (hT : ∀ k, realStandardRep n ps k T = T) {U V : Matrix (Fin n) (Fin n) ℂ} (hUV : U * V = 1)
    (D : Fin N → Finset (Fin n)) (k : Matrix.unitaryGroup (Fin n) ℝ) :
    realStandardRep n qs k (frameVec hsh T U D) =
      ∑ D' : Fin N → Finset (Fin n),
        (∏ j, minor (V * kmat k * U) (D' j) (D j)) • frameVec hsh T U D' := by
  apply Subtype.ext
  funext g
  have e : cmat g * kmat k * U = cmat g * U * (V * kmat k * U) := by
    rw [← Matrix.mul_assoc (cmat g * U), ← Matrix.mul_assoc (cmat g * U),
      Matrix.mul_assoc (cmat g) U V, hUV, Matrix.mul_one]
  rw [rep_frameVec_apply hsh hT, Submodule.coe_sum, Finset.sum_apply, e, prod_minor_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, frameVec_apply, Finset.prod_mul_distrib]
  ring

/-- Every product `T · ∏_j Δ_{R_j, D_j}` is a combination of frame vectors. -/
theorem mulProd_eq_sum_frameVec (hsh : IsMinorShift n ps qs R) (T : KF n ps)
    {U V : Matrix (Fin n) (Fin n) ℂ} (hUV : U * V = 1) (D : Fin N → Finset (Fin n)) :
    mulProd hsh D T =
      ∑ D' : Fin N → Finset (Fin n), (∏ j, minor V (D' j) (D j)) • frameVec hsh T U D' := by
  apply Subtype.ext
  funext g
  have e : cmat g = cmat g * U * V := by rw [Matrix.mul_assoc, hUV, Matrix.mul_one]
  rw [mulProd_coe, prodG_apply, Submodule.coe_sum, Finset.sum_apply]
  simp only [minorG_eq]
  rw [e, prod_minor_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, frameVec_apply, Finset.prod_mul_distrib]
  ring

/-- If `k U = U diag(μ)`, the frame vectors are eigenvectors of `k`. -/
theorem rep_frameVec_diagonal (hsh : IsMinorShift n ps qs R) {T : KF n ps}
    (hT : ∀ k, realStandardRep n ps k T = T) {U : Matrix (Fin n) (Fin n) ℂ}
    {k : Matrix.unitaryGroup (Fin n) ℝ} {μ : Fin n → ℂ}
    (hk : kmat k * U = U * Matrix.diagonal μ) (D : Fin N → Finset (Fin n)) :
    realStandardRep n qs k (frameVec hsh T U D) =
      (∏ j, ∏ i ∈ D j, μ i) • frameVec hsh T U D := by
  apply Subtype.ext
  funext g
  rw [rep_frameVec_apply hsh hT, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, frameVec_apply,
    Matrix.mul_assoc, hk, ← Matrix.mul_assoc]
  simp only [minor_mul_diagonal]
  rw [Finset.prod_mul_distrib]
  ring

/-- If `k U` is `U` with columns permuted by `σ`, and the permutation moves the column sets
`D_j` to `D'_j` in every minor, then `k` maps the frame vector of `D` to that of `D'`. -/
theorem rep_frameVec_perm (hsh : IsMinorShift n ps qs R) {T : KF n ps}
    (hT : ∀ k, realStandardRep n ps k T = T) {U : Matrix (Fin n) (Fin n) ℂ}
    {k : Matrix.unitaryGroup (Fin n) ℝ} {σ : Equiv.Perm (Fin n)}
    (hk : kmat k * U = U.submatrix id σ) {D D' : Fin N → Finset (Fin n)}
    (hD : ∀ j (X : Matrix (Fin n) (Fin n) ℂ),
      minor (X.submatrix id σ) (R j) (D j) = minor X (R j) (D' j)) :
    realStandardRep n qs k (frameVec hsh T U D) = frameVec hsh T U D' := by
  apply Subtype.ext
  funext g
  have e : cmat g * kmat k * U = (cmat g * U).submatrix id σ := by
    rw [Matrix.mul_assoc, hk]
    ext i j
    simp [Matrix.mul_apply, Matrix.submatrix_apply]
  rw [rep_frameVec_apply hsh hT, frameVec_apply, e]
  simp only [hD]

/-! ## Relations between the values of frame vectors -/

/-- **Rotation vanishing.** If the rotations `r_p(θ)` act on `U` by `U ↦ U diag(e^{i c_l θ})`
and the total weight `w = Σ_j Σ_{l ∈ D_j} c_l` satisfies `|w| ≤ |m|` for an induction block of
weight `m` of `ds` at position `p`, then `(L u_D)(1) = 0` for every `O(n)`-equivariant `L`. -/
theorem ev_frameVec_eq_zero_of_rotation {ds : List RealBlock} (hn : realRank ds = n)
    (hsh : IsMinorShift n ps qs R) {T : KF n ps} (hT : ∀ k, realStandardRep n ps k T = T)
    {U : Matrix (Fin n) (Fin n) ℂ} {p : ℕ} {c : Fin n → ℤ}
    (hrot : ∀ θ : ℝ, kmat (rot n p θ) * U =
      U * Matrix.diagonal fun l => Complex.exp ((c l : ℂ) * (θ : ℂ) * Complex.I))
    {d : ComplexCharacterData} (hd : realInducedBlockAt ds p = some d)
    {L : KF n qs →ₗ[ℂ] KF n ds} (hL : IsKEquivariant L) (D : Fin N → Finset (Fin n))
    (hle : |∑ j, ∑ l ∈ D j, c l| ≤ |d.weight|) : ev (L (frameVec hsh T U D)) = 0 := by
  refine ev_eq_zero_of_rotation hn hL hd _ (∑ j, ∑ l ∈ D j, c l) (fun θ => ?_) hle
  rw [rep_frameVec_diagonal hsh hT (hrot θ)]
  congr 1
  simp only [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]

/-- **Sign relation.** If a diagonal sign matrix `s` acts on `U` by `U ↦ U diag(μ)`, then
`(∏_j ∏_{l ∈ D_j} μ_l) (L u_D)(1)` is the character of `ds` at the signs of `s` times
`(L u_D)(1)`. -/
theorem ev_frameVec_sign {ds : List RealBlock} (hsh : IsMinorShift n ps qs R) {T : KF n ps}
    (hT : ∀ k, realStandardRep n ps k T = T) {U : Matrix (Fin n) (Fin n) ℂ}
    {L : KF n qs →ₗ[ℂ] KF n ds} (hL : IsKEquivariant L) (a : Fin n → ℝˣ)
    {s : Matrix.unitaryGroup (Fin n) ℝ}
    (hs : Unitary.toUnits s = (Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℝ))
    {μ : Fin n → ℂ} (hk : kmat s * U = U * Matrix.diagonal μ) (D : Fin N → Finset (Fin n)) :
    (∏ j, ∏ l ∈ D j, μ l) * ev (L (frameVec hsh T U D)) =
      principalSeriesCharacter ℝ n (realPositionCharacter ds) a * ev (L (frameVec hsh T U D)) := by
  rw [← ev_rep_sign hL a s hs, rep_frameVec_diagonal hsh hT hk, map_smul]
  rfl

/-- **Flip relation.** If a diagonal sign matrix `s` maps the frame vector of `D` to that of
`D'`, then `(L u_{D'})(1)` is the character of `ds` at the signs of `s` times `(L u_D)(1)`. -/
theorem ev_frameVec_flip {ds : List RealBlock} (hsh : IsMinorShift n ps qs R) {T : KF n ps}
    (hT : ∀ k, realStandardRep n ps k T = T) {U : Matrix (Fin n) (Fin n) ℂ}
    {L : KF n qs →ₗ[ℂ] KF n ds} (hL : IsKEquivariant L) (a : Fin n → ℝˣ)
    {s : Matrix.unitaryGroup (Fin n) ℝ}
    (hs : Unitary.toUnits s = (Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℝ))
    {σ : Equiv.Perm (Fin n)} (hk : kmat s * U = U.submatrix id σ) {D D' : Fin N → Finset (Fin n)}
    (hD : ∀ j (X : Matrix (Fin n) (Fin n) ℂ),
      minor (X.submatrix id σ) (R j) (D j) = minor X (R j) (D' j)) :
    ev (L (frameVec hsh T U D')) =
      principalSeriesCharacter ℝ n (realPositionCharacter ds) a * ev (L (frameVec hsh T U D)) := by
  rw [← ev_rep_sign hL a s hs, rep_frameVec_perm hsh hT hk hD]

/-! ## The scalar step -/

/-- **Scalar step through frame vectors.** Let `T` be an `O(n)`-fixed vector of the module of
`ps` that generates it under the Lie algebra, let `U V = 1`, and let `Φ` be a surjective
`(𝔤, K)`-intertwiner from the module of `qs` onto that of `ds`. If for every
`O(n)`-equivariant `L` the values `(L u_D)(1)` are `ε_D (L u_{D₀})(1)`, then `ds` has a scalar
commutant. -/
theorem hasScalarCommutant_of_frame {ds : List RealBlock} (hsh : IsMinorShift n ps qs R)
    {T : KF n ps} (hT : ∀ k, realStandardRep n ps k T = T)
    (hcyc : ∀ W' : Submodule ℂ (KF n ps), T ∈ W' →
      (∀ Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ, ∀ w ∈ W', realStandardLie n ps Z w ∈ W') → W' = ⊤)
    {U V : Matrix (Fin n) (Fin n) ℂ} (hUV : U * V = 1)
    {Φ : KF n qs →ₗ[ℂ] KF n ds} (hΦs : Function.Surjective Φ)
    (hΦ : RealDiscretePresentation.IsGKMap n qs ds Φ)
    (ε : (Fin N → Finset (Fin n)) → ℂ) (D₀ : Fin N → Finset (Fin n))
    (hrel : ∀ L : KF n qs →ₗ[ℂ] KF n ds, IsKEquivariant L →
      ∀ D, ev (L (frameVec hsh T U D)) = ε D * ev (L (frameVec hsh T U D₀))) :
    HasScalarCommutant n ds := by
  unfold RealDiscretePresentation.IsGKMap at hΦ
  rw [InductionStages.isRealStandardIntertwiner_iff] at hΦ
  have hΦK : IsKEquivariant Φ := fun k u => hΦ.1 ⟨Unitary.toUnits k, k.2⟩ u
  have hΦL : ∀ (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) (v : KF n qs),
      Φ (realStandardLie n qs Z v) = realStandardLie n ds Z (Φ v) := by
    intro Z v
    induction Z with
    | tmul z X =>
      have h1 : ∀ es : List RealBlock, realStandardLie n es (z ⊗ₜ X) =
          z • realStandardLie n es (1 ⊗ₜ X) := fun es => by
        rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1, h1, LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
      exact congrArg (z • ·) (hΦ.2 X v)
    | add Z₁ Z₂ h₁ h₂ =>
      rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, h₁, h₂]
  intro E hEK hEL
  obtain ⟨a, ha⟩ := exists_smul_family Φ hΦK (frameVec hsh T U) ε D₀ hrel E hEK
  have hfv : ∀ D, E (Φ (frameVec hsh T U D)) = a • Φ (frameVec hsh T U D) := fun D =>
    ha _ (fun k D' => ∏ j, minor (V * kmat k * U) (D' j) (D j))
      (fun k => rep_frameVec hsh hT hUV D k)
  have hmp : ∀ D, E (Φ (mulProd hsh D T)) = a • Φ (mulProd hsh D T) := by
    intro D
    rw [mulProd_eq_sum_frameVec hsh T hUV D, map_sum, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun D' _ => ?_
    rw [map_smul, map_smul, hfv, smul_comm]
  -- the eigenspace of `E` for `a`
  let W : Submodule ℂ (KF n ds) :=
    LinearMap.ker ((E - a • LinearMap.id : Module.End ℂ (KF n ds)))
  have hmemW : ∀ v, v ∈ W ↔ E v = a • v := by
    intro v
    simp only [W, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
  have hWL : ∀ Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ, ∀ v ∈ W, realStandardLie n ds Z v ∈ W := by
    intro Z v hv
    rw [hmemW] at hv ⊢
    rw [hEL, hv, map_smul]
  let W' : Submodule ℂ (KF n qs) := W.comap Φ
  have hW'L : ∀ Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ, ∀ v ∈ W',
      realStandardLie n qs Z v ∈ W' := by
    intro Z v hv
    change Φ (realStandardLie n qs Z v) ∈ W
    rw [hΦL]
    exact hWL Z _ hv
  have htop : W' = ⊤ := eq_top_of_cyclic hsh T hcyc W' hW'L fun D => (hmemW _).mpr (hmp D)
  refine ⟨a, fun v => ?_⟩
  obtain ⟨u, rfl⟩ := hΦs v
  have hu : u ∈ W' := htop ▸ Submodule.mem_top
  exact (hmemW _).mp hu

end RealDiscreteFrame

end Langlands.Archimedean
