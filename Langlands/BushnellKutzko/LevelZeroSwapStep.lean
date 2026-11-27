import Langlands.BushnellKutzko.LevelZeroTheta
import Langlands.BushnellKutzko.LevelZeroLift
import Langlands.BushnellKutzko.LevelZeroAveraging
import Langlands.BushnellKutzko.LevelZeroNormalForm

/-! # Injectivity of compression by a block transposition -/

open Matrix ValuativeRel Langlands.Jacquet

noncomputable section

namespace Langlands.BushnellKutzko.LevelZero

universe uF uV uW

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {e f : ℕ}

section Lifts

/-- The integral lift of the upper right `r × (f - r)` corner of a matrix over the residue
field, the other entries being zero. -/
def truncLift (r : ℕ) (Z : Matrix (Fin f) (Fin f) 𝓀[F]) : Matrix (Fin f) (Fin f) F :=
  fun a b => if a.val < r ∧ r ≤ b.val then lift (Z a b) else 0

theorem truncLift_le_one (r : ℕ) (Z : Matrix (Fin f) (Fin f) 𝓀[F]) (a b : Fin f) :
    valuation F (truncLift r Z a b) ≤ 1 := by
  unfold truncLift
  split_ifs
  · exact lift_le_one _
  · simp

theorem truncLift_mul (r : ℕ) (Z Z' : Matrix (Fin f) (Fin f) 𝓀[F]) :
    truncLift r Z * truncLift r Z' = 0 := by
  ext a c
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  unfold truncLift
  split_ifs with h1 h2 <;> first | (exfalso; omega) | simp

/-- The unipotent element `1 + truncLift r Z`. -/
def unipLift (r : ℕ) (Z : Matrix (Fin f) (Fin f) 𝓀[F]) : GL (Fin f) F :=
  unipU (truncLift r Z) (truncLift_mul r Z Z)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem isIntGL_one : IsIntGL (1 : GL (Fin f) F) := by
  constructor <;> intro a b <;> by_cases h : a = b <;> simp [h]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem IsIntGL.neg {A : GL (Fin f) F} (hA : IsIntGL A) : IsIntGL (-A) := by
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · simpa [Valuation.map_neg] using hA.1 a b
  · rw [inv_neg]
    simpa [Valuation.map_neg] using hA.2 a b

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem isIntGL_unipU {T : Matrix (Fin f) (Fin f) F} (hT : T * T = 0)
    (hTi : ∀ a b, valuation F (T a b) ≤ 1) : IsIntGL (unipU T hT) := by
  have h1 : ∀ a b, valuation F ((1 : Matrix (Fin f) (Fin f) F) a b) ≤ 1 := by
    intro a b; by_cases h : a = b <;> simp [h, Matrix.one_apply]
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · simpa using Valuation.map_add_le _ (h1 a b) (hTi a b)
  · change valuation F ((1 - T) a b) ≤ 1
    simpa using Valuation.map_sub_le _ (h1 a b) (hTi a b)

theorem isIntGL_unipLift (r : ℕ) (Z : Matrix (Fin f) (Fin f) 𝓀[F]) :
    IsIntGL (unipLift r Z) :=
  isIntGL_unipU _ (truncLift_le_one r Z)

/-- Residues of a product of integral matrices. -/
theorem res_mul_apply {A B : Matrix (Fin f) (Fin f) F}
    (hA : ∀ a b, valuation F (A a b) ≤ 1) (hB : ∀ a b, valuation F (B a b) ≤ 1) (a b : Fin f) :
    res ((A * B) a b) = ((A.map res) * (B.map res)) a b := by
  simp only [Matrix.mul_apply, Matrix.map_apply]
  rw [res_sum _ _ fun c _ => by rw [map_mul]; exact mul_le_one' (hA a c) (hB c b)]
  exact Finset.sum_congr rfl fun c _ => res_mul (hA a c) (hB c b)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mul_le_one_apply {A B : Matrix (Fin f) (Fin f) F}
    (hA : ∀ a b, valuation F (A a b) ≤ 1) (hB : ∀ a b, valuation F (B a b) ≤ 1) (a b : Fin f) :
    valuation F ((A * B) a b) ≤ 1 := by
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_le _ fun c _ => by rw [map_mul]; exact mul_le_one' (hA a c) (hB c b)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem erMat_le_one (r : ℕ) (a b : Fin f) : valuation F (erMat F r a b) ≤ 1 := by
  rw [erMat_apply]; split_ifs <;> simp

theorem map_res_erMat (r : ℕ) : (erMat F (f := f) r).map res = erMat 𝓀[F] r := by
  ext a b
  simp only [Matrix.map_apply, erMat_apply]
  split_ifs <;> simp

end Lifts

section Step

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GL (Fin f × Fin e) F) V) (hπ : IsSmooth π)
  (K : OpenSubgroup (GL (Fin f × Fin e) F)) (hK : IsCompact (K : Set (GL (Fin f × Fin e) F)))

/-- Averaging over `K` commutes with translation by an element normalizing `K`. -/
theorem averageMap_apply_normalizing (m : GL (Fin f × Fin e) F)
    (hm : ∀ x, x ∈ K ↔ m⁻¹ * x * m ∈ K) (x : V) :
    Compact.averageMap π hπ K hK (π m x) = π m (Compact.averageMap π hπ K hK x) := by
  have hEq : conjOpenSubgroup m K = K := by
    ext y
    rw [mem_conjOpenSubgroup]
    exact (hm y).symm
  have hgen : ∀ (L : OpenSubgroup (GL (Fin f × Fin e) F))
      (hL : IsCompact (L : Set (GL (Fin f × Fin e) F))), L = K →
      Compact.averageMap π hπ L hL = Compact.averageMap π hπ K hK := by
    rintro L hL rfl; rfl
  rw [← averageMap_conj π hπ m K hK (isCompact_conjOpenSubgroup m K hK) x,
    hgen _ _ hEq]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_J1_iff_conj {m : GL (Fin f × Fin e) F} (hm : m ∈ J0 F e f) (x : GL (Fin f × Fin e) F) :
    x ∈ J1 F e f ↔ m⁻¹ * x * m ∈ J1 F e f := by
  constructor
  · intro hx
    simpa using conj_mem_J1 ((J0 F e f).inv_mem hm) hx
  · intro hx
    simpa [mul_assoc] using conj_mem_J1 hm hx

variable [Fintype 𝓀[F]]

/-- **Injectivity of compression by a block transposition.** Let `K = U^1(𝔄)` and let `g` be
a linear map into the `K`-fixed vectors, intertwining a family of operators `τ A D` with the
block diagonal elements `diag(A, D)` on the blocks `i`, `i + 1`. If the sums of `τ` over the
lifted unipotent radicals of the proper standard parabolic subgroups of `GL_f` vanish, then
compression by the transposition of the two blocks is zero on `g` only when `g` is zero. -/
theorem compressionMap_swap_comp_eq_zero {i j : Fin e} (hij : i.val + 1 = j.val) (hlt : i < j)
    (hKJ : K.toSubgroup = J1 F e f) {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (g : W →ₗ[ℂ] V) (hfix : ∀ w, g w ∈ fixedVectors π K.toSubgroup)
    (τ : GL (Fin f) F → GL (Fin f) F → Module.End ℂ W)
    (hτ : ∀ A D, IsIntGL A → IsIntGL D → ∀ w,
      g (τ A D w) = π (pairGL hlt.ne (diagU A D)) (g w))
    (hcusp : ∀ r, 0 < r → r < f →
      ∑ Z : Matrix (Fin f) (Fin f) 𝓀[F], τ (unipLift r Z) 1 = 0)
    (hzero : (compressionMap π hπ K hK (pairGL hlt.ne swapU)).comp g = 0) : g = 0 := by
  classical
  set S : GL (Fin f × Fin e) F := pairGL hlt.ne swapU with hS
  set avg := Compact.averageMap π hπ K hK with havg
  have hSS : S * S = 1 := by rw [hS, ← map_mul, swapU_mul_swapU, map_one]
  have hmemK : ∀ x, x ∈ J1 F e f → x ∈ K := fun x hx => by
    change x ∈ K.toSubgroup; rw [hKJ]; exact hx
  have hfixK : ∀ x ∈ fixedVectors π K.toSubgroup, ∀ k, k ∈ J1 F e f → π k x = x :=
    fun x hx k hk => hx ⟨k, hmemK k hk⟩
  -- the transversal
  let Q := Multiplicative (Matrix (Fin f) (Fin f) 𝓀[F])
  let tq : Q → GL (Fin f × Fin e) F := fun q =>
    pairGL hlt.ne (lowerU (liftM (Multiplicative.toAdd q)))
  have ht : ∀ q, tq q ∈ K := fun q => hmemK _ (lowerU_mem_J1 hlt (liftM_le_one _))
  let θ : K.toSubgroup →* Q :=
    (thetaHom hij).comp (MulEquiv.subgroupCongr hKJ).toMonoidHom
  have hθt : ∀ q, θ ⟨tq q, ht q⟩ = q := by
    intro q
    apply Multiplicative.toAdd.injective
    ext a b
    change res (pairEmb F hlt.ne (fromBlocks 1 0 (liftM (Multiplicative.toAdd q)) 1) (a, j) (b, i))
      = _
    rw [pairEmb_rl, Matrix.fromBlocks_apply₂₁, res_liftM]
  have hmean : ∀ x ∈ fixedVectors π K.toSubgroup,
      avg (π S x) = (Fintype.card Q : ℂ)⁻¹ • ∑ q, π (tq q) (π S x) := by
    intro x hx
    refine averageMap_eq_mean_of_hom π hπ K hK θ tq ht hθt (π S x) ?_
    intro h hθh
    let l : J1 F e f := MulEquiv.subgroupCongr hKJ h
    have hl : l ∈ (thetaHom hij).ker := hθh
    have hconj := swap_conj_mem_J1 hij hl
    have hx' : π (S * (h : GL (Fin f × Fin e) F) * S) x = x := hfixK x hx _ hconj
    calc π h (π S x) = π S (π (S * (h : GL (Fin f × Fin e) F) * S) x) := by
          rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
          congr 2
          rw [← mul_assoc, ← mul_assoc, hSS, one_mul]
      _ = π S x := by rw [hx']
  have hconjS : ∀ q, S * tq q * S = pairGL hlt.ne (upperU (liftM (Multiplicative.toAdd q))) := by
    intro q
    rw [hS, ← map_mul, ← map_mul, swapU_lowerU_swapU]
  have htwice : ∀ x ∈ fixedVectors π K.toSubgroup,
      avg (π S (avg (π S x))) = (Fintype.card Q : ℂ)⁻¹ •
        ∑ q, avg (π (pairGL hlt.ne (upperU (liftM (Multiplicative.toAdd q)))) x) := by
    intro x hx
    rw [hmean x hx, map_smul, map_smul, map_sum, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← hconjS q, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  -- the three kinds of residue matrices
  have hcase : ∀ w (X : Matrix (Fin f) (Fin f) 𝓀[F]),
      avg (π (pairGL hlt.ne (upperU (liftM X))) (g w)) = if X = 0 then g w else 0 := by
    intro w X
    split_ifs with hX0
    · -- the zero matrix
      subst hX0
      have hlt1 : ∀ a b, valuation F (liftM (0 : Matrix (Fin f) (Fin f) 𝓀[F]) a b) < 1 :=
        fun a b => (res_eq_zero_iff (liftM_le_one _ a b)).mp (by simp)
      rw [averageMap_apply_of_mem π hπ K hK (hmemK _ (upperU_mem_J1 hlt hlt1)),
        Compact.averageMap_id π hπ K hK _ (hfix w)]
    by_cases hXu : IsUnit X
    · -- an invertible matrix
      let Xg : GL (Fin f) F := liftGL hXu.unit
      have hXg : ((Xg : GL (Fin f) F) : Matrix (Fin f) (Fin f) F) = liftM X := by
        simp only [Xg, coe_liftGL, IsUnit.unit_spec]
      have hdecomp := upperU_eq_of_isUnit Xg
      rw [hXg] at hdecomp
      rw [hdecomp, map_mul, map_mul, map_mul]
      have hLJ : pairGL hlt.ne (lowerU ((Xg⁻¹ : GL (Fin f) F) : Matrix (Fin f) (Fin f) F)) ∈
          J1 F e f := lowerU_mem_J1 hlt (isIntGL_liftGL _).2
      have hL := hmemK _ hLJ
      rw [map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        Module.End.mul_apply, hfixK (g w) (hfix w) _ hLJ, averageMap_apply_of_mem π hπ K hK hL]
      have h1 := hτ (-Xg⁻¹) Xg (isIntGL_liftGL _).inv.neg (isIntGL_liftGL _) w
      rw [← h1]
      exact LinearMap.congr_fun hzero (τ (-Xg⁻¹) Xg w)
    · -- a nonzero singular matrix
      obtain ⟨r, hr0, hrf, P, Qm, hPQ⟩ := exists_erMat_form X hX0 hXu
      let Pg : GL (Fin f) F := liftGL P
      let Qg : GL (Fin f) F := liftGL Qm
      let E : Matrix (Fin f) (Fin f) F := erMat F r
      let X' : Matrix (Fin f) (Fin f) F := (Pg : Matrix (Fin f) (Fin f) F) * E * Qg
      have hPint := (isIntGL_liftGL P).1
      have hQint := (isIntGL_liftGL Qm).1
      have hX'int : ∀ a b, valuation F (X' a b) ≤ 1 :=
        mul_le_one_apply (mul_le_one_apply hPint (erMat_le_one r)) hQint
      have hres : ∀ a b, res (X' a b) = X a b := by
        intro a b
        rw [res_mul_apply (mul_le_one_apply hPint (erMat_le_one r)) hQint]
        have hm1 : ((Pg : Matrix (Fin f) (Fin f) F) * E).map res =
            (Pg : Matrix (Fin f) (Fin f) F).map res * E.map res := by
          ext c d; exact res_mul_apply hPint (erMat_le_one r) c d
        have hPm : (Pg : Matrix (Fin f) (Fin f) F).map res = P := by
          ext c d; exact res_liftGL P c d
        have hQm : (Qg : Matrix (Fin f) (Fin f) F).map res = Qm := by
          ext c d; exact res_liftGL Qm c d
        rw [hm1, hPm, hQm, map_res_erMat, hPQ]
      let δ : Matrix (Fin f) (Fin f) F := liftM X - X'
      have hδ : ∀ a b, valuation F (δ a b) < 1 := by
        intro a b
        exact (res_eq_res_iff (liftM_le_one _ a b) (hX'int a b)).mp (by rw [res_liftM, hres])
      have hsplit : upperU (liftM X) = upperU δ * upperU X' := by
        rw [upperU_mul]; congr 1; simp [δ]
      have hconj : upperU X' = diagU Pg Qg⁻¹ * upperU E * (diagU Pg Qg⁻¹)⁻¹ := by
        rw [diagU_upperU_conj, inv_inv]
      have hδK : pairGL hlt.ne (upperU δ) ∈ K := hmemK _ (upperU_mem_J1 hlt hδ)
      set Mp : GL (Fin f × Fin e) F := pairGL hlt.ne (diagU Pg Qg⁻¹) with hMp
      have hMpJ0 : Mp ∈ J0 F e f := diagU_mem_J0 hlt (isIntGL_liftGL P) (isIntGL_liftGL Qm).inv
      have hMpK : ∀ x, x ∈ K ↔ Mp⁻¹ * x * Mp ∈ K := by
        intro x
        change x ∈ K.toSubgroup ↔ Mp⁻¹ * x * Mp ∈ K.toSubgroup
        rw [hKJ]
        exact mem_J1_iff_conj hMpJ0 x
      have hMpinv : Mp⁻¹ = pairGL hlt.ne (diagU Pg⁻¹ Qg) := by
        rw [hMp, ← map_inv, diagU_inv, inv_inv]
      -- the core cuspidal computation
      have hcore : ∀ w', avg (π (pairGL hlt.ne (upperU E)) (g w')) = 0 := by
        intro w'
        have hterm : ∀ Z : Matrix (Fin f) (Fin f) 𝓀[F],
            avg (π (pairGL hlt.ne (upperU E)) (g w')) =
              avg (π (pairGL hlt.ne (upperU E)) (g (τ (unipLift r Z) 1 w'))) := by
          intro Z
          set T := truncLift r Z with hT
          have hZE : (-T) * E = 0 := by
            ext a c
            simp only [E, erMat, Matrix.mul_diagonal, Matrix.neg_apply, Matrix.zero_apply, hT,
              truncLift]
            split_ifs <;> first | (exfalso; omega) | simp
          have hET : -(E * (-T)) = T := by
            ext a c
            simp only [E, erMat, Matrix.diagonal_mul, Matrix.neg_apply, mul_neg, neg_neg, hT,
              truncLift]
            split_ifs <;> first | (exfalso; omega) | simp
          have hid := lowerU_mul_upperU hZE
          have hunip : unipU (-(E * -T)) (by
              rw [neg_mul_neg, mul_assoc, ← mul_assoc (-T), hZE]; simp) = unipLift r Z := by
            ext1
            rw [coe_unipU, unipLift, coe_unipU, hET]
          rw [hunip] at hid
          have hnJ : pairGL hlt.ne (lowerU (-T)) ∈ J1 F e f :=
            lowerU_mem_J1 hlt fun a b => by
              simpa [Valuation.map_neg] using truncLift_le_one r Z a b
          have hn := hmemK _ hnJ
          have hτZ := hτ (unipLift r Z) 1 (isIntGL_unipLift r Z) isIntGL_one w'
          calc avg (π (pairGL hlt.ne (upperU E)) (g w'))
              = avg (π (pairGL hlt.ne (lowerU (-T)))
                  (π (pairGL hlt.ne (upperU E)) (g w'))) :=
                (averageMap_apply_of_mem π hπ K hK hn _).symm
            _ = avg (π (pairGL hlt.ne (lowerU (-T) * upperU E)) (g w')) := by
                rw [map_mul, map_mul, Module.End.mul_apply]
            _ = avg (π (pairGL hlt.ne (upperU E))
                  (π (pairGL hlt.ne (diagU (unipLift r Z) 1))
                    (π (pairGL hlt.ne (lowerU (-T))) (g w')))) := by
                rw [hid, map_mul, map_mul, map_mul, map_mul, Module.End.mul_apply,
                  Module.End.mul_apply]
            _ = avg (π (pairGL hlt.ne (upperU E)) (g (τ (unipLift r Z) 1 w'))) := by
                rw [hfixK (g w') (hfix w') _ hnJ, hτZ]
        have hsum : (Fintype.card (Matrix (Fin f) (Fin f) 𝓀[F]) : ℂ) •
            avg (π (pairGL hlt.ne (upperU E)) (g w')) = 0 := by
          calc (Fintype.card (Matrix (Fin f) (Fin f) 𝓀[F]) : ℂ) •
                avg (π (pairGL hlt.ne (upperU E)) (g w'))
              = ∑ Z : Matrix (Fin f) (Fin f) 𝓀[F],
                  avg (π (pairGL hlt.ne (upperU E)) (g (τ (unipLift r Z) 1 w'))) := by
                rw [← Finset.sum_congr rfl fun Z _ => hterm Z, Finset.sum_const, Finset.card_univ,
                  Nat.cast_smul_eq_nsmul]
            _ = avg (π (pairGL hlt.ne (upperU E))
                  (g ((∑ Z : Matrix (Fin f) (Fin f) 𝓀[F], τ (unipLift r Z) 1) w'))) := by
                rw [LinearMap.sum_apply, map_sum, map_sum, map_sum]
            _ = 0 := by rw [hcusp r hr0 hrf]; simp
        exact (smul_eq_zero.mp hsum).resolve_left
          (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      rw [hsplit, map_mul, map_mul, Module.End.mul_apply,
        averageMap_apply_of_mem π hπ K hK hδK, hconj, map_mul, map_mul, map_mul, map_mul,
        Module.End.mul_apply, Module.End.mul_apply, ← hMp,
        averageMap_apply_normalizing π hπ K hK Mp hMpK, diagU_inv, inv_inv,
        ← hτ Pg⁻¹ Qg (isIntGL_liftGL P).inv (isIntGL_liftGL Qm), hcore, map_zero]
  -- conclusion
  ext w
  have hA : avg (π S (g w)) = 0 := LinearMap.congr_fun hzero w
  have h2 := htwice (g w) (hfix w)
  rw [hA, map_zero, map_zero] at h2
  simp only [hcase] at h2
  have hsum : ∑ q : Q, (if Multiplicative.toAdd q = 0 then g w else 0) = g w := by
    rw [Finset.sum_eq_single (1 : Q)]
    · simp
    · intro q _ hq
      simp only [ite_eq_right_iff]
      intro h
      exact absurd (Multiplicative.toAdd.injective (by simpa using h)) hq
    · simp
  rw [hsum] at h2
  have hcard : ((Fintype.card Q : ℂ))⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  simpa using ((smul_eq_zero.mp h2.symm).resolve_left hcard)

end Step

end Langlands.BushnellKutzko.LevelZero
