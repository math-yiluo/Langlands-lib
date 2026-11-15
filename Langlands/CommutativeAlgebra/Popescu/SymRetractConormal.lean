import Langlands.CommutativeAlgebra.Popescu.SymRetractJacobian

/-! # The new relations generate the conormal module after inverting `u` -/

namespace Langlands.CommutativeAlgebra.Popescu.SymRetract

open MvPolynomial

variable {R : Type*} [CommRing R] {n m : ℕ}
  (I : Ideal (MvPolynomial (Fin n) R)) (F : Fin m → MvPolynomial (Fin n) R)
  (P : Matrix (Fin n) (Fin m) (MvPolynomial (Fin n) R)) (u : MvPolynomial (Fin n) R)
  (Θ : Fin m → Fin m → Fin m → MvPolynomial (Fin n) R)

/-- `(u − E) Z̃ E = 0` over `C`. -/
theorem uC_sub_EC_mul (hFI : ∀ k, F k ∈ I) (hE1 : ∀ k, u * F k - ∑ l, Et F P k l * F l ∈ I ^ 2)
    (hΘ : ∀ k j, Et F P k j * u - ∑ l, Et F P k l * Et F P l j = ∑ p, Θ k j p * F p) :
    (uC I F u • (1 : Matrix (Fin m) (Fin m) (SymAlg I F)) - EC I F P) * ZC I F Θ * EC I F P = 0 := by
  have h1 : ZC I F Θ * EC I F P = EC I F P * YC I F P u * PC I F P :=
    calc ZC I F Θ * EC I F P = ZC I F Θ * (DC I F * PC I F P) := by rw [EC_eq I F P]
      _ = ZC I F Θ * DC I F * PC I F P := (Matrix.mul_assoc _ _ _).symm
      _ = EC I F P * YC I F P u * PC I F P := by rw [ZC_mul_DC I F P u Θ hFI hE1 hΘ]
  rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.sub_mul,
    EC_sq I F P u hFI hE1, Matrix.smul_mul, Matrix.one_mul, sub_self, Matrix.zero_mul,
    Matrix.zero_mul]

/-- The ring `R[x, y]/J²`. -/
def SymAlg2 : Type _ := MvPolynomial (Fin (n + m)) R ⧸ symIdeal I F ^ 2

noncomputable instance : CommRing (SymAlg2 I F) :=
  inferInstanceAs (CommRing (MvPolynomial (Fin (n + m)) R ⧸ symIdeal I F ^ 2))

/-- The quotient map onto `R[x, y]/J²`. -/
noncomputable def q2 : MvPolynomial (Fin (n + m)) R →+* SymAlg2 I F := Ideal.Quotient.mk _

/-- The projection `R[x, y]/J² → R[x, y]/J`. -/
noncomputable def φ21 : SymAlg2 I F →+* SymAlg I F :=
  Ideal.Quotient.factor (Ideal.pow_le_self two_ne_zero)

theorem φ21_q2 (x : MvPolynomial (Fin (n + m)) R) : φ21 I F (q2 I F x) = qC I F x := rfl

/-- The image of `J` in `R[x, y]/J²`. -/
noncomputable def Jbar : Ideal (SymAlg2 I F) := (symIdeal I F).map (q2 I F)

theorem q2_mem_Jbar {x : MvPolynomial (Fin (n + m)) R} (hx : x ∈ symIdeal I F) :
    q2 I F x ∈ Jbar I F :=
  Ideal.mem_map_of_mem _ hx

theorem mem_Jbar_of_φ21 {e : SymAlg2 I F} (he : φ21 I F e = 0) : e ∈ Jbar I F := by
  have : e ∈ RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_self two_ne_zero :
      symIdeal I F ^ 2 ≤ symIdeal I F)) := he
  rwa [Ideal.Quotient.factor_ker] at this

theorem Jbar_mul {x y : SymAlg2 I F} (hx : x ∈ Jbar I F) (hy : y ∈ Jbar I F) : x * y = 0 := by
  have h : x * y ∈ Jbar I F * Jbar I F := Ideal.mul_mem_mul hx hy
  have h2 : Jbar I F * Jbar I F = ⊥ := by
    rw [Jbar, ← Ideal.map_mul, ← pow_two]
    exact Ideal.map_quotient_self _
  rwa [h2, Ideal.mem_bot] at h

theorem q2_eq_zero_of_mem_sq {x : MvPolynomial (Fin (n + m)) R} (hx : x ∈ symIdeal I F ^ 2) :
    q2 I F x = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr hx

section Vectors

open Matrix

/-- The image of `u` in `R[x, y]/J²`. -/
noncomputable abbrev U2 : SymAlg2 I F := q2 I F (ιx u)

/-- `E` over `R[x, y]/J²`. -/
noncomputable def E2 : Matrix (Fin m) (Fin m) (SymAlg2 I F) :=
  Matrix.of fun k l => q2 I F (ιx (Et F P k l))

/-- `Z̃` over `R[x, y]/J²`. -/
noncomputable def Z2 : Matrix (Fin m) (Fin m) (SymAlg2 I F) :=
  Matrix.of fun k p => q2 I F (Zt Θ k p)

/-- The classes of the `f_k`. -/
noncomputable def fv : Fin m → SymAlg2 I F := fun k => q2 I F (ιx (F k))

/-- The classes of the `𝒢_k`. -/
noncomputable def gv : Fin m → SymAlg2 I F := fun k => q2 I F (Gk F P u k)

/-- The classes of the `H_k`. -/
noncomputable def hv : Fin m → SymAlg2 I F := fun k => q2 I F (Hk F P u Θ k)

theorem E2_map : (E2 I F P).map (φ21 I F) = EC I F P := by
  ext k l; rfl

theorem Z2_map : (Z2 I F Θ).map (φ21 I F) = ZC I F Θ := by
  ext k l; rfl

theorem fv_mem (hFI : ∀ k, F k ∈ I) (k : Fin m) : fv I F k ∈ Jbar I F :=
  q2_mem_Jbar I F (ιx_mem_symIdeal I F (hFI k))

theorem mulVec_eq_zero_of_map {M : Matrix (Fin m) (Fin m) (SymAlg2 I F)}
    (hM : M.map (φ21 I F) = 0) {w : Fin m → SymAlg2 I F} (hw : ∀ l, w l ∈ Jbar I F) :
    M *ᵥ w = 0 := by
  funext k
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  refine Finset.sum_eq_zero fun l _ => Jbar_mul I F (mem_Jbar_of_φ21 I F ?_) (hw l)
  have := congrFun (congrFun hM k) l
  simpa using this

theorem E2_mulVec_fv (hE1 : ∀ k, u * F k - ∑ l, Et F P k l * F l ∈ I ^ 2) :
    E2 I F P *ᵥ fv I F = U2 I F u • fv I F := by
  funext k
  have h := q2_eq_zero_of_mem_sq I F (ιx_mem_symIdeal_sq (m := m) I F (hE1 k))
  simp only [map_sub, map_mul, map_sum] at h
  simp only [Matrix.mulVec, dotProduct, E2, fv, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  exact (sub_eq_zero.mp h).symm

theorem E2_mulVec_gv
    (hΘ : ∀ k j, Et F P k j * u - ∑ l, Et F P k l * Et F P l j = ∑ p, Θ k j p * F p) :
    E2 I F P *ᵥ gv I F P u = Z2 I F Θ *ᵥ fv I F := by
  funext k
  have h := congrArg (q2 I F) (Et_Gk F P u Θ hΘ k)
  simp only [map_sum, map_mul] at h
  simpa [Matrix.mulVec, dotProduct, E2, Z2, gv, fv] using h

theorem hv_eq : hv I F P u Θ =
    U2 I F u ^ 3 • fv I F + U2 I F u ^ 2 • gv I F P u - (E2 I F P * Z2 I F Θ) *ᵥ fv I F := by
  funext k
  simp only [hv, Hk, map_add, map_sub, map_mul, map_pow, map_sum, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.mul_apply, E2, Z2, fv, gv,
    Matrix.of_apply, U2]

/-- `u⁵ f ≡ u E H` modulo `J²`. -/
theorem U2_smul_E2_mulVec_hv (hFI : ∀ k, F k ∈ I)
    (hE1 : ∀ k, u * F k - ∑ l, Et F P k l * F l ∈ I ^ 2)
    (hΘ : ∀ k j, Et F P k j * u - ∑ l, Et F P k l * Et F P l j = ∑ p, Θ k j p * F p) :
    U2 I F u • (E2 I F P *ᵥ hv I F P u Θ) = U2 I F u ^ 5 • fv I F := by
  set U := U2 I F u
  set w := Z2 I F Θ *ᵥ fv I F
  have hw : ∀ l, w l ∈ Jbar I F := fun l => by
    simp only [w, Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun p _ => Ideal.mul_mem_left _ _ (fv_mem I F hFI p)
  -- `E² w = u E w`
  have hb : (E2 I F P * E2 I F P) *ᵥ w = U • (E2 I F P *ᵥ w) := by
    have hzero : (E2 I F P * E2 I F P - U • E2 I F P) *ᵥ w = 0 := by
      apply mulVec_eq_zero_of_map I F _ hw
      rw [Matrix.map_sub _ (map_sub (φ21 I F)), Matrix.map_mul,
        Matrix.map_smul' _ _ _ (map_mul (φ21 I F)), E2_map, EC_sq I F P u hFI hE1]
      exact sub_self _
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, sub_eq_zero] at hzero
    exact hzero
  -- `(u − E) Z̃ E f = 0`
  have hd : U ^ 2 • w - U • (E2 I F P *ᵥ w) = 0 := by
    have hzero : ((U • (1 : Matrix (Fin m) (Fin m) (SymAlg2 I F)) - E2 I F P) * Z2 I F Θ *
        E2 I F P) *ᵥ fv I F = 0 := by
      apply mulVec_eq_zero_of_map I F _ (fv_mem I F hFI)
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub (φ21 I F)),
        Matrix.map_smul' _ _ _ (map_mul (φ21 I F)), Matrix.map_one _ (map_zero _) (map_one _),
        E2_map, Z2_map]
      exact uC_sub_EC_mul I F P u Θ hFI hE1 hΘ
    rw [← Matrix.mulVec_mulVec, E2_mulVec_fv I F P u hE1, Matrix.mulVec_smul,
      ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      at hzero
    rw [← hzero]
    module
  rw [hv_eq, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    E2_mulVec_fv I F P u hE1, E2_mulVec_gv I F P u Θ hΘ, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, ← Matrix.mulVec_mulVec (fv I F) (E2 I F P * E2 I F P) (Z2 I F Θ),
    show Z2 I F Θ *ᵥ fv I F = w from rfl, hb]
  have : U • (U ^ 3 • U • fv I F + U ^ 2 • w - U • (E2 I F P *ᵥ w)) =
      U ^ 5 • fv I F + U • (U ^ 2 • w - U • (E2 I F P *ᵥ w)) := by module
  rw [this, hd, smul_zero, add_zero]

end Vectors

section Membership

variable (hFI : ∀ k, F k ∈ I) (hIF : I ≤ Ideal.span (Set.range F))
  (hE1 : ∀ k, u * F k - ∑ l, Et F P k l * F l ∈ I ^ 2)
  (hΘ : ∀ k j, Et F P k j * u - ∑ l, Et F P k l * Et F P l j = ∑ p, Θ k j p * F p)

/-- The ideal `(H) + J²`. -/
noncomputable abbrev Mid : Ideal (MvPolynomial (Fin (n + m)) R) :=
  Ideal.span (Set.range (Hk F P u Θ)) ⊔ symIdeal I F ^ 2

include hFI hE1 hΘ in
theorem u5_F_mem (k : Fin m) : ιx u ^ 5 * ιx (F k) ∈ Mid I F P u Θ := by
  have h := congrFun (U2_smul_E2_mulVec_hv I F P u Θ hFI hE1 hΘ) k
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, E2, hv, fv, U2,
    Matrix.of_apply] at h
  have hdiff : ιx u ^ 5 * ιx (F k) - ιx u * ∑ l, ιx (Et F P k l) * Hk F P u Θ l ∈
      symIdeal I F ^ 2 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q2 I F _ = 0
    simp only [map_sub, map_mul, map_pow, map_sum, h, sub_self]
  have hH : ιx u * ∑ l, ιx (Et F P k l) * Hk F P u Θ l ∈ Ideal.span (Set.range (Hk F P u Θ)) :=
    Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun l _ =>
      Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩))
  rw [← sub_add_cancel (ιx u ^ 5 * ιx (F k)) (ιx u * ∑ l, ιx (Et F P k l) * Hk F P u Θ l)]
  exact Ideal.add_mem _ (Ideal.mem_sup_right hdiff) (Ideal.mem_sup_left hH)

include hFI hIF hE1 hΘ in
theorem u5_mem_of_mem {p : MvPolynomial (Fin n) R} (hp : p ∈ I) :
    ιx u ^ 5 * ιx p ∈ Mid I F P u Θ := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hIF hp)
  simp only [map_sum, map_mul, Finset.mul_sum]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [mul_left_comm]
  exact Ideal.mul_mem_left _ _ (u5_F_mem I F P u Θ hFI hE1 hΘ k)

include hFI hE1 hΘ in
theorem u7_Gk_mem (q : Fin m) : ιx u ^ 7 * Gk F P u q ∈ Mid I F P u Θ := by
  have h : ιx u ^ 7 * Gk F P u q = ιx u ^ 5 * Hk F P u Θ q -
      ιx u ^ 3 * (ιx u ^ 5 * ιx (F q)) +
      ∑ p, (∑ l, ιx (Et F P q l) * Zt Θ l p) * (ιx u ^ 5 * ιx (F p)) := by
    have hs : ιx u ^ 5 * ∑ p, (∑ l, ιx (Et F P q l) * Zt Θ l p) * ιx (F p) =
        ∑ p, (∑ l, ιx (Et F P q l) * Zt Θ l p) * (ιx u ^ 5 * ιx (F p)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    simp only [Hk]
    rw [mul_sub, mul_add, hs]
    ring
  rw [h]
  refine Ideal.add_mem _ (Ideal.sub_mem _ ?_ ?_) (Ideal.sum_mem _ fun p _ => ?_)
  · exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_left (Ideal.subset_span ⟨q, rfl⟩))
  · exact Ideal.mul_mem_left _ _ (u5_F_mem I F P u Θ hFI hE1 hΘ q)
  · exact Ideal.mul_mem_left _ _ (u5_F_mem I F P u Θ hFI hE1 hΘ p)

include hFI in
theorem kappa_Et_mem {κ : Fin m → MvPolynomial (Fin n) R} (hκ : ∑ j, κ j * F j ∈ I ^ 2)
    (l : Fin m) : ∑ q, κ q * Et F P q l ∈ I := by
  have hD : ∀ i, ∑ q, κ q * pderiv i (F q) ∈ I := fun i => by
    have h := pderiv_mem_of_mem_sq I i hκ
    simp only [map_sum, Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib] at h
    have h2 : ∑ q, F q * pderiv i (κ q) ∈ I := I.sum_mem fun q _ => I.mul_mem_right _ (hFI q)
    have := I.sub_mem h h2
    rwa [add_sub_cancel_right] at this
  have : ∑ q, κ q * Et F P q l = ∑ i, (∑ q, κ q * pderiv i (F q)) * P i l := by
    simp only [Et, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q _ => by ring
  rw [this]
  exact I.sum_mem fun i _ => I.mul_mem_right _ (hD i)

theorem u_symGen (κ : Fin m → MvPolynomial (Fin n) R) :
    ιx u * symGen κ = ∑ q, ιx (κ q) * Gk F P u q +
      symGen (fun j => ∑ q, κ q * Et F P q j) := by
  set S := ∑ j, (∑ q, ιx (m := m) (κ q) * ιx (Et F P q j)) * yv j
  have a : ∑ q, ιx (m := m) (κ q) * (ιx u * yv q) = ιx u * symGen κ := by
    rw [symGen, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  have b : ∑ q, ιx (m := m) (κ q) * ∑ j, ιx (Et F P q j) * yv j = S := by
    simp only [S, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => by ring
  have h1 : ∑ q, ιx (κ q) * Gk F P u q = ιx u * symGen κ - S := by
    calc ∑ q, ιx (κ q) * Gk F P u q
        = ∑ q, (ιx (m := m) (κ q) * (ιx u * yv q) -
            ιx (m := m) (κ q) * ∑ j, ιx (Et F P q j) * yv j) :=
          Finset.sum_congr rfl fun q _ => by rw [Gk_eq, mul_sub]
      _ = ιx u * symGen κ - S := by rw [Finset.sum_sub_distrib, a, b]
  have h2 : symGen (m := m) (fun j => ∑ q, κ q * Et F P q j) = S := by
    simp only [symGen, S, map_sum, map_mul]
  rw [h1, h2, sub_add_cancel]

include hFI hIF hE1 hΘ in
theorem u8_symGen_mem {κ : Fin m → MvPolynomial (Fin n) R} (hκ : ∑ j, κ j * F j ∈ I ^ 2) :
    ιx u ^ 8 * symGen κ ∈ Mid I F P u Θ := by
  have h : ιx u ^ 8 * symGen κ = ∑ q, ιx (κ q) * (ιx u ^ 7 * Gk F P u q) +
      ∑ j, (ιx u ^ 2 * yv j) * (ιx u ^ 5 * ιx (∑ q, κ q * Et F P q j)) := by
    have e1 : ιx u ^ 7 * ∑ q, ιx (κ q) * Gk F P u q =
        ∑ q, ιx (κ q) * (ιx u ^ 7 * Gk F P u q) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    have e2 : ιx u ^ 7 * symGen (m := m) (fun j => ∑ q, κ q * Et F P q j) =
        ∑ j, (ιx u ^ 2 * yv j) * (ιx u ^ 5 * ιx (∑ q, κ q * Et F P q j)) := by
      rw [symGen, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [show ιx u ^ 8 * symGen κ = ιx u ^ 7 * (ιx u * symGen κ) by ring, u_symGen, mul_add,
      e1, e2]
  rw [h]
  refine Ideal.add_mem _ (Ideal.sum_mem _ fun q _ => ?_) (Ideal.sum_mem _ fun j _ => ?_)
  · exact Ideal.mul_mem_left _ _ (u7_Gk_mem I F P u Θ hFI hE1 hΘ q)
  · exact Ideal.mul_mem_left _ _
      (u5_mem_of_mem I F P u Θ hFI hIF hE1 hΘ (kappa_Et_mem I F P hFI hκ j))

include hFI hIF hE1 hΘ in
/-- `u⁸ J ⊆ (H) + J²`. -/
theorem u8_mem {G : MvPolynomial (Fin (n + m)) R} (hG : G ∈ symIdeal I F) :
    ιx u ^ 8 * G ∈ Mid I F P u Θ := by
  have hle : symIdeal I F ≤ (Mid I F P u Θ).colon {ιx u ^ 8} := by
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul, mul_comm,
        show ιx u ^ 8 * ιx p = ιx u ^ 3 * (ιx u ^ 5 * ιx p) by ring]
      exact Ideal.mul_mem_left _ _ (u5_mem_of_mem I F P u Θ hFI hIF hE1 hΘ hp)
    · rw [Ideal.span_le]
      rintro _ ⟨κ, hκ, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_colon_singleton, smul_eq_mul, mul_comm]
      exact u8_symGen_mem I F P u Θ hFI hIF hE1 hΘ hκ
  have := hle hG
  rwa [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] at this

end Membership

end Langlands.CommutativeAlgebra.Popescu.SymRetract
