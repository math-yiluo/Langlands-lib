import Langlands.GroupScheme.IntegralModel.GreenbergWitt
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Greenberg rings attached to Witt-vector coordinate data

Let `k` be a perfect field of characteristic `p`, let `A` be a ring with a ring map
`ψ : W(k) → A`, and let `D` be cyclic Witt-vector coordinates of `A`
(`WittDecomposition`). For a `k`-algebra `T` the *Greenberg ring* is the quotient of
`A ⊗[ℤ] W(T)` by the common kernel of the coordinate functionals
`a ⊗ w ↦ (coord i a) · w ∈ W_{m i}(T)`. It is functorial in `T`, has natural coordinates
`∏ i W_{m i}(T)`, equals `A` at `T = k`, and carries a reduction map to `T` whose kernel,
and the kernel of every square-zero base change, is nilpotent.
-/

set_option maxSynthPendingDepth 2

noncomputable section

universe u

open WittVector TensorProduct

namespace Langlands.GroupScheme.IntegralModel.Greenberg

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝕎" => WittVector p

/-! ### Truncated Witt vectors and their canonical lifts -/

section Out

variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

theorem truncate_out (y : TruncatedWittVector p n R) : truncate n y.out = y :=
  TruncatedWittVector.ext fun i => by rw [coeff_truncate, TruncatedWittVector.coeff_out]

theorem coeff_truncMap (f : R →+* S) (y : TruncatedWittVector p n R) (i : Fin n) :
    (truncMap p n f y).coeff i = f (y.coeff i) := by
  obtain ⟨x, rfl⟩ := truncate_surjective p n R y
  rw [truncMap_truncate, coeff_truncate, map_coeff, coeff_truncate]

omit hp in
theorem coeff_out_of_le (y : TruncatedWittVector p n R) {i : ℕ} (hi : n ≤ i) :
    y.out.coeff i = 0 := by
  simp [TruncatedWittVector.out, not_lt.2 hi]

theorem map_out (f : R →+* S) (y : TruncatedWittVector p n R) :
    WittVector.map f y.out = (truncMap p n f y).out := by
  ext i
  rw [map_coeff]
  by_cases hi : i < n
  · obtain ⟨j, rfl⟩ : ∃ j : Fin n, (j : ℕ) = i := ⟨⟨i, hi⟩, rfl⟩
    rw [TruncatedWittVector.coeff_out, TruncatedWittVector.coeff_out, coeff_truncMap]
  · rw [coeff_out_of_le _ (not_lt.1 hi), coeff_out_of_le _ (not_lt.1 hi), map_zero]

theorem out_zero : (0 : TruncatedWittVector p n R).out = 0 := by
  ext i
  by_cases hi : i < n
  · obtain ⟨j, rfl⟩ : ∃ j : Fin n, (j : ℕ) = i := ⟨⟨i, hi⟩, rfl⟩
    rw [TruncatedWittVector.coeff_out, TruncatedWittVector.coeff_zero, zero_coeff]
  · rw [coeff_out_of_le _ (not_lt.1 hi), zero_coeff]

end Out

/-! ### Products of Witt vectors with nilpotent constant coefficients -/

section WittSquare

variable {T : Type*} [CommRing T]

theorem eq_teichmuller_add_verschiebung (x : 𝕎 T) :
    x = teichmuller p (x.coeff 0) + verschiebung (x.shift 1) := by
  ext n
  rw [coeff_add_of_disjoint n _ _ ?_]
  · rcases n with _ | n
    · rw [teichmuller_coeff_zero, verschiebung_coeff_zero, add_zero]
    · rw [teichmuller_coeff_pos p _ _ (Nat.succ_pos n), verschiebung_coeff_succ, shift_coeff,
        zero_add, add_comm]
  · intro n
    rcases n with _ | n
    · exact Or.inr (verschiebung_coeff_zero _)
    · exact Or.inl (teichmuller_coeff_pos p _ _ (Nat.succ_pos n))

theorem mul_eq_natCast_mul_of_charP [CharP T p] (x y : 𝕎 T)
    (hxy : x.coeff 0 * y.coeff 0 = 0) (hx : x.coeff 0 ^ p = 0) (hy : y.coeff 0 ^ p = 0) :
    ∃ z, x * y = p * z := by
  refine ⟨verschiebung (x.shift 1 * y.shift 1), ?_⟩
  have hF : ∀ a : T, a ^ p = 0 → WittVector.frobenius (teichmuller p a) = 0 := by
    intro a ha
    rw [frobenius_eq_map_frobenius, map_teichmuller, frobenius_def, ha, teichmuller_zero]
  have ex := eq_teichmuller_add_verschiebung x
  have ey := eq_teichmuller_add_verschiebung y
  set a := x.coeff 0
  set b := y.coeff 0
  set x' := x.shift 1
  set y' := y.shift 1
  calc x * y = (teichmuller p a + verschiebung x') * (teichmuller p b + verschiebung y') := by
        rw [← ex, ← ey]
    _ = teichmuller p (a * b) + verschiebung (y' * WittVector.frobenius (teichmuller p a)) +
          verschiebung (x' * WittVector.frobenius (teichmuller p b)) +
          verschiebung (x' * WittVector.frobenius (verschiebung y')) := by
        rw [map_mul, verschiebung_mul_frobenius, verschiebung_mul_frobenius,
          verschiebung_mul_frobenius]
        ring
    _ = p * verschiebung (x' * y') := by
        rw [hxy, teichmuller_zero, hF a hx, hF b hy, mul_zero, mul_zero, map_zero,
          frobenius_verschiebung,
          show x' * (y' * (p : 𝕎 T)) = p • (x' * y') by rw [nsmul_eq_mul]; ring,
          map_nsmul, nsmul_eq_mul]
        simp only [zero_add]

theorem mul_eq_natCast_mul {k : Type*} [Field k] [CharP k p] [Algebra k T] (x y : 𝕎 T)
    (hxy : x.coeff 0 * y.coeff 0 = 0) (hx : x.coeff 0 ^ p = 0) (hy : y.coeff 0 ^ p = 0) :
    ∃ z, x * y = p * z := by
  rcases subsingleton_or_nontrivial T with hT | hT
  · exact ⟨0, WittVector.ext fun n => Subsingleton.elim _ _⟩
  · have : CharP T p := charP_of_injective_algebraMap (algebraMap k T).injective p
    exact mul_eq_natCast_mul_of_charP x y hxy hx hy

end WittSquare

section Greenberg

variable {k : Type u} [Field k] [CharP k p] [PerfectRing k p]
  {A : Type u} [CommRing A] {ψ : WittVector p k →+* A} (D : WittDecomposition p ψ)

namespace WittDecomposition

omit [CharP k p] [PerfectRing k p] in
theorem eq_zero_of_coord {a : A} (h : ∀ i, D.coord i a = 0) : a = 0 := by
  rw [D.eq_sum a 0 fun i => by rw [Pi.zero_apply, map_zero, h]]
  simp

theorem psi_pow_mul_e (i : D.ι) : ψ ((p : 𝕎 k) ^ D.m i) * D.e i = 0 := by
  refine D.eq_zero_of_coord fun l => ?_
  rw [D.coord_mul]
  by_cases h : i = l
  · subst h
    rw [(mem_ker_truncate_iff_mem_span _ _).2 (Ideal.mem_span_singleton_self _), zero_mul]
  · rw [D.coord_e_ne l i h, mul_zero]

omit [CharP k p] [PerfectRing k p] in
theorem e_eq_zero_of_m_eq_zero {i : D.ι} (h : D.m i = 0) : D.e i = 0 := by
  refine D.eq_zero_of_coord fun l => ?_
  by_cases hil : i = l
  · subst hil
    exact TruncatedWittVector.ext fun j => absurd j.isLt (by omega)
  · exact D.coord_e_ne l i hil

omit [CharP k p] [PerfectRing k p] in
theorem mulLeft_semilinear (b : A) (l : D.ι) (c : 𝕎 k) (a : A) :
    ((D.coord l).comp (AddMonoidHom.mulLeft b)) (ψ c * a) =
      truncate (D.m l) c * ((D.coord l).comp (AddMonoidHom.mulLeft b)) a := by
  change D.coord l (b * (ψ c * a)) = _ * D.coord l (b * a)
  rw [mul_left_comm, D.coord_mul]

end WittDecomposition

variable (T : Type u) [CommRing T] [Algebra k T]

/-- The `W(T)`-linear extension of a `W(k)`-semilinear functional `μ : A → W_j(k)`. -/
def semiExt {j : ℕ} (μ : A →+ TruncatedWittVector p j k) :
    A ⊗[ℤ] 𝕎 T →+ TruncatedWittVector p j T :=
  liftAddHom
    (AddMonoidHom.mk' (fun a => AddMonoidHom.mk'
        (fun w => truncMap p j (algebraMap k T) (μ a) * truncate j w)
        (fun w w' => by rw [map_add, mul_add]))
      (fun a a' => AddMonoidHom.ext fun w => by
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, add_mul]))
    (fun n a w => by
      change truncMap p j (algebraMap k T) (μ (n • a)) * truncate j w =
        truncMap p j (algebraMap k T) (μ a) * truncate j (n • w)
      rw [map_zsmul, map_zsmul, map_zsmul, smul_mul_assoc, mul_smul_comm])

omit [CharP k p] [PerfectRing k p] in
@[simp] theorem semiExt_tmul {j : ℕ} (μ : A →+ TruncatedWittVector p j k) (a : A) (w : 𝕎 T) :
    semiExt T μ (a ⊗ₜ w) = truncMap p j (algebraMap k T) (μ a) * truncate j w :=
  rfl

/-- The coordinate functionals of `A ⊗[ℤ] W(T)`. -/
def coordMap : A ⊗[ℤ] 𝕎 T →+ ((i : D.ι) → TruncatedWittVector p (D.m i) T) :=
  AddMonoidHom.pi fun i => semiExt T (D.coord i)

omit [CharP k p] [PerfectRing k p] in
theorem coordMap_apply (x : A ⊗[ℤ] 𝕎 T) (i : D.ι) :
    coordMap D T x i = semiExt T (D.coord i) x :=
  rfl

/-- An additive map on `A ⊗[ℤ] W(T)` is *balanced* if it identifies `ψ(c) a ⊗ w` with
`a ⊗ c w` and kills `e i ⊗ w` whenever the first `m i` coefficients of `w` vanish. -/
structure Balanced {P : Type*} [AddCommGroup P] (Λ : A ⊗[ℤ] 𝕎 T →+ P) : Prop where
  smul : ∀ (c : 𝕎 k) (a : A) (w : 𝕎 T),
    Λ ((ψ c * a) ⊗ₜ w) = Λ (a ⊗ₜ (WittVector.map (algebraMap k T) c * w))
  vanish : ∀ (i : D.ι) (w : 𝕎 T), truncate (D.m i) w = 0 → Λ (D.e i ⊗ₜ w) = 0

namespace Balanced

variable {D T} {P : Type*} [AddCommGroup P] {Λ : A ⊗[ℤ] WittVector p T →+ P} (hΛ : Balanced D T Λ)
include hΛ
omit [CharP k p] [PerfectRing k p]

theorem congr_trunc (i : D.ι) {w w' : 𝕎 T} (h : truncate (D.m i) w = truncate (D.m i) w') :
    Λ (D.e i ⊗ₜ w) = Λ (D.e i ⊗ₜ w') := by
  rw [← sub_eq_zero, ← map_sub, ← tmul_sub]
  exact hΛ.vanish i _ (by rw [map_sub, h, sub_self])

/-- **Balanced maps factor through the coordinates.** -/
theorem eq_sum (x : A ⊗[ℤ] 𝕎 T) : Λ x = ∑ i, Λ (D.e i ⊗ₜ (coordMap D T x i).out) := by
  induction x using TensorProduct.inductionOn with
  | tmul a w =>
    have ha := D.eq_sum a (fun i => (D.coord i a).out) fun i => truncate_out _
    conv_lhs => rw [ha, sum_tmul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΛ.smul]
    apply hΛ.congr_trunc
    rw [truncate_out, coordMap_apply, semiExt_tmul, map_mul (truncate (D.m i)),
      ← truncMap_truncate, truncate_out]
  | add x y hx hy =>
    rw [map_add, hx, hy, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_add, ← tmul_add]
    apply hΛ.congr_trunc
    rw [map_add (truncate (D.m i)), truncate_out, truncate_out, truncate_out,
      map_add (coordMap D T), Pi.add_apply]

theorem eq_of_coordMap_eq {x y : A ⊗[ℤ] 𝕎 T} (h : coordMap D T x = coordMap D T y) :
    Λ x = Λ y := by
  rw [hΛ.eq_sum x, hΛ.eq_sum y, h]

theorem map_eq_zero {x : A ⊗[ℤ] 𝕎 T} (h : coordMap D T x = 0) : Λ x = 0 := by
  rw [hΛ.eq_of_coordMap_eq (y := 0) (by rw [h, map_zero]), map_zero]

end Balanced

theorem semiExt_balanced {j : ℕ} (μ : A →+ TruncatedWittVector p j k)
    (hμ : ∀ c a, μ (ψ c * a) = truncate j c * μ a) : Balanced D T (semiExt T μ) where
  smul c a w := by
    rw [semiExt_tmul, semiExt_tmul, hμ, map_mul (truncMap p j (algebraMap k T)),
      truncMap_truncate, map_mul (truncate j)]
    ring
  vanish i w hw := by
    rw [semiExt_tmul, ← truncate_out (μ (D.e i)), truncMap_truncate, ← map_mul, mul_comm]
    refine truncate_mul_map_eq_zero p (a := D.m i) ?_ ?_
    · rw [map_mul, truncate_out, ← hμ, D.psi_pow_mul_e, map_zero]
    · rw [← RingHom.mem_ker, mem_ker_truncate] at hw
      exact hw

theorem coordMap_balanced : Balanced D T (coordMap D T) where
  smul c a w := funext fun i => (semiExt_balanced D T (D.coord i) (D.coord_mul i)).smul c a w
  vanish i w hw := funext fun l =>
    (semiExt_balanced D T (D.coord l) (D.coord_mul l)).vanish i w hw

omit [CharP k p] [PerfectRing k p] in
theorem coordMap_tmul_mul (b : A) (v : 𝕎 T) (x : A ⊗[ℤ] 𝕎 T) (l : D.ι) :
    coordMap D T ((b ⊗ₜ v) * x) l =
      truncate (D.m l) v * semiExt T ((D.coord l).comp (AddMonoidHom.mulLeft b)) x := by
  induction x using TensorProduct.inductionOn with
  | tmul a w =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, coordMap_apply, semiExt_tmul, semiExt_tmul,
      map_mul (truncate (D.m l))]
    change _ = _ * (truncMap p _ (algebraMap k T) (D.coord l (b * a)) * _)
    ring
  | add x y hx hy => rw [mul_add, map_add, Pi.add_apply, hx, hy, map_add, mul_add]

/-- The common kernel of the coordinate functionals; it is an ideal. -/
def kerIdeal : Ideal (A ⊗[ℤ] 𝕎 T) where
  carrier := {x | coordMap D T x = 0}
  add_mem' {x y} hx hy := by
    change coordMap D T (x + y) = 0
    rw [map_add, show coordMap D T x = 0 from hx, show coordMap D T y = 0 from hy, add_zero]
  zero_mem' := map_zero (coordMap D T)
  smul_mem' y x hx := by
    change coordMap D T (y * x) = 0
    have hx' : coordMap D T x = 0 := hx
    induction y using TensorProduct.inductionOn with
    | tmul b v =>
      funext l
      rw [Pi.zero_apply, coordMap_tmul_mul,
        (semiExt_balanced D T _ (D.mulLeft_semilinear b l)).map_eq_zero hx', mul_zero]
    | add y y' hy hy' => rw [add_mul, map_add, hy, hy', add_zero]

theorem mem_kerIdeal {x : A ⊗[ℤ] 𝕎 T} : x ∈ kerIdeal D T ↔ coordMap D T x = 0 :=
  Iff.rfl

/-- **The Greenberg ring** of `T`. -/
abbrev GreenbergRing := (A ⊗[ℤ] 𝕎 T) ⧸ kerIdeal D T

theorem mk_eq_mk_iff {s s' : A ⊗[ℤ] 𝕎 T} :
    Ideal.Quotient.mk (kerIdeal D T) s = Ideal.Quotient.mk (kerIdeal D T) s' ↔
      coordMap D T s = coordMap D T s' := by
  rw [Ideal.Quotient.eq, mem_kerIdeal, map_sub, sub_eq_zero]

/-- The coordinates of an element of the Greenberg ring. -/
def coordRing (x : GreenbergRing D T) : (i : D.ι) → TruncatedWittVector p (D.m i) T :=
  coordMap D T (Function.surjInv Ideal.Quotient.mk_surjective x)

theorem coordRing_mk (s : A ⊗[ℤ] 𝕎 T) :
    coordRing D T (Ideal.Quotient.mk (kerIdeal D T) s) = coordMap D T s :=
  (mk_eq_mk_iff D T).1 (Function.surjInv_eq _ _)

theorem coordRing_zero : coordRing D T 0 = 0 := by
  rw [← map_zero (Ideal.Quotient.mk (kerIdeal D T)), coordRing_mk, map_zero]

theorem ext_coord {x y : GreenbergRing D T} (h : coordRing D T x = coordRing D T y) : x = y := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [coordRing_mk, coordRing_mk] at h
  exact (mk_eq_mk_iff D T).2 h

/-- The element of the Greenberg ring with prescribed coordinates. -/
def ofCoords (y : (i : D.ι) → TruncatedWittVector p (D.m i) T) : GreenbergRing D T :=
  Ideal.Quotient.mk (kerIdeal D T) (∑ i, D.e i ⊗ₜ (y i).out)

omit [CharP k p] [PerfectRing k p] in
theorem coordMap_sum_out (y : (i : D.ι) → TruncatedWittVector p (D.m i) T) :
    coordMap D T (∑ i, D.e i ⊗ₜ (y i).out) = y := by
  funext l
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single l]
  · rw [coordMap_apply, semiExt_tmul, D.coord_e_self, map_one, one_mul, truncate_out]
  · intro i _ hil
    rw [coordMap_apply, semiExt_tmul, D.coord_e_ne l i hil, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ l) h

theorem coordRing_ofCoords (y : (i : D.ι) → TruncatedWittVector p (D.m i) T) :
    coordRing D T (ofCoords D T y) = y := by
  rw [ofCoords, coordRing_mk, coordMap_sum_out]

/-- The natural coordinates of the Greenberg ring. -/
def coordEquiv : GreenbergRing D T ≃ ((ij : Σ i, Fin (D.m i)) → T) where
  toFun x ij := (coordRing D T x ij.1).coeff ij.2
  invFun y := ofCoords D T fun i => TruncatedWittVector.mk p fun j => y ⟨i, j⟩
  left_inv x := ext_coord D T (funext fun i => TruncatedWittVector.ext fun j => by
    rw [coordRing_ofCoords, TruncatedWittVector.coeff_mk])
  right_inv y := funext fun ij => by
    simp only [coordRing_ofCoords, TruncatedWittVector.coeff_mk]

theorem coordEquiv_apply (x : GreenbergRing D T) (ij : Σ i, Fin (D.m i)) :
    coordEquiv D T x ij = (coordRing D T x ij.1).coeff ij.2 :=
  rfl

/-- The image of `A` in the Greenberg ring. -/
def incL : A →+* GreenbergRing D T :=
  (Ideal.Quotient.mk (kerIdeal D T)).comp Algebra.TensorProduct.includeLeftRingHom

/-- The image of `W(T)` in the Greenberg ring. -/
def incR : 𝕎 T →+* GreenbergRing D T :=
  (Ideal.Quotient.mk (kerIdeal D T)).comp
    (Algebra.TensorProduct.includeRight : 𝕎 T →ₐ[ℤ] A ⊗[ℤ] 𝕎 T).toRingHom

theorem incL_apply (a : A) : incL D T a = Ideal.Quotient.mk (kerIdeal D T) (a ⊗ₜ 1) :=
  rfl

theorem incR_apply (w : 𝕎 T) : incR D T w = Ideal.Quotient.mk (kerIdeal D T) (1 ⊗ₜ w) :=
  rfl

theorem ofCoords_eq (y : (i : D.ι) → TruncatedWittVector p (D.m i) T) :
    ofCoords D T y = ∑ i, incL D T (D.e i) * incR D T (y i).out := by
  rw [ofCoords, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [incL_apply, incR_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem eq_sum_incL_mul_incR (x : GreenbergRing D T) :
    x = ∑ i, incL D T (D.e i) * incR D T (coordRing D T x i).out := by
  rw [← ofCoords_eq]
  exact ext_coord D T (by rw [coordRing_ofCoords])

/-! ### Functoriality -/

section Map

variable (R₀ : Type u) [CommRing R₀] [Algebra R₀ A]
variable {T} {T' : Type u} [CommRing T'] [Algebra k T'] {T'' : Type u} [CommRing T'']
  [Algebra k T'']

variable (A) in
/-- The map `A ⊗ W(T) → A ⊗ W(T')` induced by a `k`-algebra map `T → T'`. -/
def preMap (f : T →ₐ[k] T') : A ⊗[ℤ] 𝕎 T →ₐ[R₀] A ⊗[ℤ] 𝕎 T' :=
  Algebra.TensorProduct.map (AlgHom.id R₀ A) (WittVector.map (f : T →+* T')).toIntAlgHom

omit [CharP k p] [PerfectRing k p] in
theorem preMap_tmul (f : T →ₐ[k] T') (a : A) (w : 𝕎 T) :
    preMap A R₀ f (a ⊗ₜ w) = a ⊗ₜ WittVector.map (f : T →+* T') w :=
  Algebra.TensorProduct.map_tmul _ _ _ _

omit [CharP k p] [PerfectRing k p] in
theorem coordMap_preMap (f : T →ₐ[k] T') (s : A ⊗[ℤ] 𝕎 T) (i : D.ι) :
    coordMap D T' (preMap A R₀ f s) i =
      truncMap p (D.m i) (f : T →+* T') (coordMap D T s i) := by
  induction s using TensorProduct.inductionOn with
  | tmul a w =>
    rw [preMap_tmul, coordMap_apply, coordMap_apply, semiExt_tmul, semiExt_tmul, map_mul,
      truncMap_comp, truncMap_truncate, AlgHom.comp_algebraMap]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem kerIdeal_le_comap (f : T →ₐ[k] T') :
    kerIdeal D T ≤ (kerIdeal D T').comap (preMap A R₀ f) := by
  intro s hs
  rw [Ideal.mem_comap, mem_kerIdeal]
  funext i
  rw [coordMap_preMap, (mem_kerIdeal D T).1 hs, Pi.zero_apply, map_zero, Pi.zero_apply]

/-- The Greenberg ring is functorial in `T`. -/
def gmap (f : T →ₐ[k] T') : GreenbergRing D T →ₐ[R₀] GreenbergRing D T' :=
  Ideal.quotientMapₐ (kerIdeal D T') (preMap A R₀ f) (kerIdeal_le_comap D R₀ f)

theorem gmap_mk (f : T →ₐ[k] T') (s : A ⊗[ℤ] 𝕎 T) :
    gmap D R₀ f (Ideal.Quotient.mk _ s) = Ideal.Quotient.mk _ (preMap A R₀ f s) :=
  rfl

theorem coordRing_gmap (f : T →ₐ[k] T') (x : GreenbergRing D T) (i : D.ι) :
    coordRing D T' (gmap D R₀ f x) i = truncMap p (D.m i) (f : T →+* T') (coordRing D T x i) := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [gmap_mk, coordRing_mk, coordRing_mk, coordMap_preMap]

theorem coordEquiv_gmap (f : T →ₐ[k] T') (x : GreenbergRing D T) (ij : Σ i, Fin (D.m i)) :
    coordEquiv D T' (gmap D R₀ f x) ij = f (coordEquiv D T x ij) := by
  rw [coordEquiv_apply, coordEquiv_apply, coordRing_gmap, coeff_truncMap]
  rfl

theorem gmap_id : gmap D R₀ (AlgHom.id k T) = AlgHom.id R₀ (GreenbergRing D T) := by
  refine AlgHom.ext fun x => ext_coord D T (funext fun i => TruncatedWittVector.ext fun j => ?_)
  rw [coordRing_gmap, coeff_truncMap]
  rfl

theorem gmap_comp (f : T →ₐ[k] T') (g : T' →ₐ[k] T'') :
    gmap D R₀ (g.comp f) = (gmap D R₀ g).comp (gmap D R₀ f) := by
  refine AlgHom.ext fun x => ext_coord D T'' (funext fun i => TruncatedWittVector.ext fun j => ?_)
  rw [AlgHom.comp_apply, coordRing_gmap, coordRing_gmap, coordRing_gmap, coeff_truncMap,
    coeff_truncMap, coeff_truncMap]
  rfl

end Map

/-! ### The Greenberg ring of `k` -/

section Level

variable (R₀ : Type u) [CommRing R₀] [Algebra R₀ A]

variable (ψ) in
/-- The multiplication map `A ⊗ W(k) → A`. -/
def theta : A ⊗[ℤ] 𝕎 k →ₐ[R₀] A :=
  Algebra.TensorProduct.productLeftAlgHom (AlgHom.id R₀ A) ψ.toIntAlgHom

omit [CharP k p] [PerfectRing k p] in
theorem theta_tmul (a : A) (w : 𝕎 k) : theta ψ R₀ (a ⊗ₜ w) = a * ψ w :=
  rfl

omit [CharP k p] [PerfectRing k p] in
theorem coord_theta (s : A ⊗[ℤ] 𝕎 k) (l : D.ι) :
    D.coord l (theta ψ R₀ s) = coordMap D k s l := by
  induction s using TensorProduct.inductionOn with
  | tmul a w =>
    rw [theta_tmul, coordMap_apply, semiExt_tmul, mul_comm a, D.coord_mul, Algebra.algebraMap_self,
      truncMap_id, mul_comm]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem ker_theta : RingHom.ker (theta ψ R₀) = kerIdeal D k := by
  ext s
  rw [RingHom.mem_ker, mem_kerIdeal]
  constructor
  · intro h
    funext l
    rw [← coord_theta D R₀, h, map_zero, Pi.zero_apply]
  · intro h
    exact D.eq_zero_of_coord fun l => by rw [coord_theta, h, Pi.zero_apply]

omit [CharP k p] [PerfectRing k p] in
theorem theta_surjective : Function.Surjective (theta ψ R₀) := fun a =>
  ⟨a ⊗ₜ 1, by rw [theta_tmul, map_one, mul_one]⟩

/-- **The Greenberg ring of `k` is `A`.** -/
def levelEquiv : GreenbergRing D k ≃ₐ[R₀] A :=
  (Ideal.quotientEquivAlgOfEq R₀ (ker_theta D R₀).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (theta_surjective R₀))

end Level

/-! ### Reduction -/

section Reduction

variable (r : A →+* k)

/-- The reduction `A ⊗ W(T) → T`, `a ⊗ w ↦ r(a) w₀`. -/
def preRed : A ⊗[ℤ] 𝕎 T →+* T :=
  (Algebra.TensorProduct.productMap ((algebraMap k T).comp r).toIntAlgHom
    (WittVector.constantCoeff : 𝕎 T →+* T).toIntAlgHom).toRingHom

omit [CharP k p] [PerfectRing k p] in
theorem preRed_tmul (a : A) (w : 𝕎 T) :
    preRed T r (a ⊗ₜ w) = algebraMap k T (r a) * w.coeff 0 :=
  rfl

variable (hψr : ∀ c, r (ψ c) = c.coeff 0)
include hψr

omit [CharP k p] [PerfectRing k p] in
theorem preRed_balanced : Balanced D T (preRed T r).toAddMonoidHom where
  smul c a w := by
    change preRed T r ((ψ c * a) ⊗ₜ w) = preRed T r (a ⊗ₜ (WittVector.map (algebraMap k T) c * w))
    rw [preRed_tmul, preRed_tmul, map_mul r, hψr, mul_coeff_zero, map_coeff, map_mul]
    ring
  vanish i w hw := by
    change preRed T r (D.e i ⊗ₜ w) = 0
    rcases Nat.eq_zero_or_pos (D.m i) with h | h
    · rw [D.e_eq_zero_of_m_eq_zero h, zero_tmul, map_zero]
    · rw [preRed_tmul]
      rw [← RingHom.mem_ker, mem_ker_truncate] at hw
      rw [hw 0 h, mul_zero]

/-- **The reduction map** of the Greenberg ring. -/
def red : GreenbergRing D T →+* T :=
  Ideal.Quotient.lift (kerIdeal D T) (preRed T r) fun _ hs =>
    (preRed_balanced D T r hψr).map_eq_zero hs

theorem red_mk (s : A ⊗[ℤ] 𝕎 T) :
    red D T r hψr (Ideal.Quotient.mk _ s) = preRed T r s :=
  Ideal.Quotient.lift_mk _ _ _

theorem red_incL (a : A) : red D T r hψr (incL D T a) = algebraMap k T (r a) := by
  rw [incL_apply, red_mk, preRed_tmul, one_coeff_zero, mul_one]

theorem red_incR (w : 𝕎 T) : red D T r hψr (incR D T w) = w.coeff 0 := by
  rw [incR_apply, red_mk, preRed_tmul, map_one, map_one, one_mul]

/-- The reduction is a fixed linear form in the coordinates. -/
theorem red_eq_sum (x : GreenbergRing D T) :
    red D T r hψr x = ∑ ij : (Σ i, Fin (D.m i)),
      algebraMap k T (if (ij.2 : ℕ) = 0 then r (D.e ij.1) else 0) * coordEquiv D T x ij := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [red_mk]
  refine ((preRed_balanced D T r hψr).eq_sum s).trans ?_
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  change algebraMap k T (r (D.e i)) * (coordMap D T s i).out.coeff 0 = _
  simp only [coordEquiv_apply, coordRing_mk]
  rcases Nat.eq_zero_or_pos (D.m i) with h | h
  · rw [D.e_eq_zero_of_m_eq_zero h, map_zero, map_zero, zero_mul]
    exact (Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)).symm
  · rw [Finset.sum_eq_single (⟨0, h⟩ : Fin (D.m i))]
    · rw [ite_eq_left (rfl : ((⟨0, h⟩ : Fin (D.m i)) : ℕ) = 0)]
      congr 1
      exact TruncatedWittVector.coeff_out _ ⟨0, h⟩
    · intro j _ hj
      rw [ite_eq_right (fun h' => hj (Fin.ext h')), map_zero, zero_mul]
    · intro h'
      exact absurd (Finset.mem_univ _) h'

theorem red_algebraMap (R₀ : Type u) [CommRing R₀] [Algebra R₀ A] (c : R₀) :
    red D T r hψr (algebraMap R₀ (GreenbergRing D T) c) =
      algebraMap k T (r (algebraMap R₀ A c)) := by
  rw [← Ideal.Quotient.mk_algebraMap, Algebra.TensorProduct.algebraMap_apply]
  exact red_incL D T r hψr _

omit hψr in
/-- The image of `ker r` in the Greenberg ring. -/
def auxIdeal : Ideal (GreenbergRing D T) :=
  Ideal.map (incL D T) (RingHom.ker r)

omit hψr in
theorem auxIdeal_pow (N : ℕ) (hN : RingHom.ker r ^ (N + 1) = ⊥) :
    auxIdeal D T r ^ (N + 1) = ⊥ := by
  rw [auxIdeal, ← Ideal.map_pow, hN, Ideal.map_bot]

omit hψr in
theorem natCast_mem_auxIdeal : (p : GreenbergRing D T) ∈ auxIdeal D T r := by
  rw [← map_natCast (incL D T) p]
  exact Ideal.mem_map_of_mem _ (by rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero])

theorem auxIdeal_le_ker_red : auxIdeal D T r ≤ RingHom.ker (red D T r hψr) := by
  rw [auxIdeal, Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, RingHom.mem_ker, red_incL, (RingHom.mem_ker).1 ha, map_zero]

theorem exists_sub_mem_auxIdeal (x : GreenbergRing D T) :
    ∃ W : 𝕎 T, x - incR D T W ∈ auxIdeal D T r := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction s using TensorProduct.inductionOn with
  | tmul a w =>
    set c := teichmuller p (r a)
    refine ⟨WittVector.map (algebraMap k T) c * w, ?_⟩
    have h1 : Ideal.Quotient.mk (kerIdeal D T) ((ψ c * 1) ⊗ₜ w) =
        incR D T (WittVector.map (algebraMap k T) c * w) := by
      rw [incR_apply]
      exact (mk_eq_mk_iff D T).2 ((coordMap_balanced D T).smul _ _ _)
    have h2 : Ideal.Quotient.mk (kerIdeal D T) (a ⊗ₜ w) - incR D T (WittVector.map (algebraMap k T) c * w) =
        incL D T (a - ψ c) * incR D T w := by
      rw [← h1, mul_one, incL_apply, incR_apply, ← map_sub, ← map_mul,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, sub_tmul]
    rw [h2]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [RingHom.mem_ker, map_sub, hψr, teichmuller_coeff_zero, sub_self]
  | add s s' hs hs' =>
    obtain ⟨W, hW⟩ := hs
    obtain ⟨W', hW'⟩ := hs'
    refine ⟨W + W', ?_⟩
    rw [map_add, map_add, add_sub_add_comm]
    exact add_mem hW hW'

theorem mul_mem_auxIdeal_of_red {x y : GreenbergRing D T} (hx : red D T r hψr x = 0)
    (hy : red D T r hψr y = 0) : x * y ∈ auxIdeal D T r := by
  obtain ⟨W, hW⟩ := exists_sub_mem_auxIdeal D T r hψr x
  obtain ⟨W', hW'⟩ := exists_sub_mem_auxIdeal D T r hψr y
  have h0 : ∀ {z : GreenbergRing D T} {V : 𝕎 T}, red D T r hψr z = 0 →
      z - incR D T V ∈ auxIdeal D T r → V.coeff 0 = 0 := by
    intro z V hz hzV
    have := auxIdeal_le_ker_red D T r hψr hzV
    rw [RingHom.mem_ker, map_sub, hz, red_incR, zero_sub, neg_eq_zero] at this
    exact this
  have hW0 := h0 hx hW
  have hW0' := h0 hy hW'
  obtain ⟨z, hz⟩ := mul_eq_natCast_mul (k := k) W W' (by rw [hW0, zero_mul])
    (by rw [hW0, zero_pow hp.out.ne_zero]) (by rw [hW0', zero_pow hp.out.ne_zero])
  have key : x * y = x * (y - incR D T W') + (x - incR D T W) * incR D T W' +
      (p : GreenbergRing D T) * incR D T z := by
    rw [← map_natCast (incR D T) p, ← map_mul (incR D T), ← hz, map_mul (incR D T)]
    ring
  rw [key]
  exact add_mem (add_mem (Ideal.mul_mem_left _ _ hW') (Ideal.mul_mem_right _ _ hW))
    (Ideal.mul_mem_right _ _ (natCast_mem_auxIdeal D T r))

omit hψr in
theorem isNilpotent_of_sq_le (N : ℕ) (hN : RingHom.ker r ^ (N + 1) = ⊥)
    (K : Ideal (GreenbergRing D T)) (hK : ∀ x ∈ K, ∀ y ∈ K, x * y ∈ auxIdeal D T r) :
    K ^ (2 * (N + 1)) = ⊥ := by
  have hsq : K ^ 2 ≤ auxIdeal D T r := by
    rw [sq]
    exact Ideal.mul_le.2 hK
  refine (pow_mul K 2 (N + 1)).trans (le_bot_iff.1 ?_)
  rw [← auxIdeal_pow D T r N hN]
  exact Ideal.pow_right_mono hsq _

/-- **The kernel of the reduction is nilpotent.** -/
theorem ker_red_pow (N : ℕ) (hN : RingHom.ker r ^ (N + 1) = ⊥) :
    RingHom.ker (red D T r hψr) ^ (2 * (N + 1)) = ⊥ :=
  isNilpotent_of_sq_le D T r N hN _ fun _ hx _ hy => mul_mem_auxIdeal_of_red D T r hψr hx hy

end Reduction

/-! ### Square-zero thickenings -/

section SquareZero

variable (R₀ : Type u) [CommRing R₀] [Algebra R₀ A] (r : A →+* k)
variable {T} {T' : Type u} [CommRing T'] [Algebra k T']

theorem mul_mem_auxIdeal_of_gmap (f : T →ₐ[k] T')
    (hf : ∀ a ∈ RingHom.ker f, ∀ b ∈ RingHom.ker f, a * b = 0) {x y : GreenbergRing D T}
    (hx : gmap D R₀ f x = 0) (hy : gmap D R₀ f y = 0) : x * y ∈ auxIdeal D T r := by
  have hw : ∀ {z : GreenbergRing D T}, gmap D R₀ f z = 0 → ∀ i,
      (f : T →+* T') ((coordRing D T z i).out.coeff 0) = 0 := by
    intro z hz i
    rw [← map_coeff, map_out, ← coordRing_gmap D R₀ f z i, hz, coordRing_zero, Pi.zero_apply,
      out_zero, zero_coeff]
  have hpow : ∀ a ∈ RingHom.ker f, a ^ p = 0 := fun a ha =>
    pow_eq_zero_of_le hp.out.two_le (by rw [sq]; exact hf a ha a ha)
  rw [eq_sum_incL_mul_incR D T x, eq_sum_incL_mul_incR D T y, Finset.sum_mul_sum]
  refine Ideal.sum_mem _ fun i _ => Ideal.sum_mem _ fun l _ => ?_
  have ha : (coordRing D T x i).out.coeff 0 ∈ RingHom.ker f := RingHom.mem_ker.2 (hw hx i)
  have hb : (coordRing D T y l).out.coeff 0 ∈ RingHom.ker f := RingHom.mem_ker.2 (hw hy l)
  obtain ⟨z, hz⟩ := mul_eq_natCast_mul (k := k) (coordRing D T x i).out (coordRing D T y l).out
    (hf _ ha _ hb) (hpow _ ha) (hpow _ hb)
  have key : incL D T (D.e i) * incR D T (coordRing D T x i).out *
      (incL D T (D.e l) * incR D T (coordRing D T y l).out) =
      incL D T (D.e i * D.e l) * ((p : GreenbergRing D T) * incR D T z) := by
    calc _ = incL D T (D.e i * D.e l) *
          incR D T ((coordRing D T x i).out * (coordRing D T y l).out) := by
          rw [map_mul (incL D T), map_mul (incR D T)]
          ring
      _ = _ := by rw [hz, map_mul (incR D T), map_natCast]
  rw [key]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (natCast_mem_auxIdeal D T r))

/-- **Square-zero thickenings give nilpotent thickenings of the Greenberg ring.** -/
theorem ker_gmap_pow (f : T →ₐ[k] T')
    (hf : ∀ a ∈ RingHom.ker f, ∀ b ∈ RingHom.ker f, a * b = 0) (N : ℕ)
    (hN : RingHom.ker r ^ (N + 1) = ⊥) :
    RingHom.ker (gmap D R₀ f) ^ (2 * (N + 1)) = ⊥ :=
  isNilpotent_of_sq_le D T r N hN _ fun _ hx _ hy =>
    mul_mem_auxIdeal_of_gmap D R₀ r f hf hx hy

end SquareZero

end Greenberg

end Langlands.GroupScheme.IntegralModel.Greenberg
