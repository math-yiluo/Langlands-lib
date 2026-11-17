import Langlands.Analysis.BoundedSchur
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Finite dimensionality from a faithful tracial vector

Let `H` be a complex Hilbert space, `S` a set of bounded operators on `H`, and let `N` be the
star-commutant of `S` (`StarSubalgebra.centralizer ℂ S`). Suppose that `ξ ∈ H` is

* *tracial* for `N`: `‖x ξ‖ = ‖x† ξ‖` for all `x ∈ N`;
* *separating* for `N`: `x ξ = 0` implies `x = 0` for `x ∈ N`.

If `V ⊆ H` is a subspace on which the elements of `N` preserving `V` act transitively, then
`V` is finite dimensional.

The proof combines the bounded Schur lemma `exists_eq_smul_id_of_commutesOn`, the Jacobson
density theorem `jacobson_density`, and the trace inequality `n ‖q ξ‖² ≤ ‖ξ‖²`. Here `n` is the
size of a linearly independent family in `V`, and `q` is a nonzero projection of `N` that
depends only on `V`.
-/

noncomputable section

namespace Langlands.Analysis

open scoped InnerProductSpace

section Density

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
variable (B : Subalgebra ℂ (H →L[ℂ] H)) (V : Submodule ℂ H)

/-- Restriction of a subalgebra of operators to an invariant subspace `V`. -/
def restrictAlgHom (hBV : ∀ b ∈ B, ∀ v ∈ V, b v ∈ V) : B →ₐ[ℂ] Module.End ℂ V where
  toFun b := ((b : H →L[ℂ] H) : H →ₗ[ℂ] H).restrict fun v hv => hBV b b.2 v hv
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl
  commutes' c := by ext; simp [Algebra.algebraMap_eq_smul_one]

omit [CompleteSpace H] in
theorem restrictAlgHom_apply (hBV : ∀ b ∈ B, ∀ v ∈ V, b v ∈ V) (b : B) (v : V) :
    (restrictAlgHom B V hBV b v : H) = (b : H →L[ℂ] H) v :=
  rfl

/-- **Density.** If a subalgebra `B` of bounded operators on a complex Banach space acts
transitively on an invariant subspace `V`, then every `ℂ`-linear endomorphism of `V` agrees
with an element of `B` on any finite subset of `V`. -/
theorem exists_mem_eq_on_finset (hBV : ∀ b ∈ B, ∀ v ∈ V, b v ∈ V)
    (htrans : ∀ u w : V, u ≠ 0 → ∃ b ∈ B, b u = w)
    (f : V →ₗ[ℂ] V) (s : Finset V) : ∃ b ∈ B, ∀ m ∈ s, (f m : H) = b m := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · refine ⟨0, B.zero_mem, fun m _ => ?_⟩
    rw [Subsingleton.elim m 0]
    simp
  let ρ := restrictAlgHom B V hBV
  let R := ρ.range
  have hR : ∀ (r : R) (m : V), r • m = (r : Module.End ℂ V) m := fun _ _ => rfl
  have hρ : ∀ (b : H →L[ℂ] H) (hb : b ∈ B) (m : V),
      ((((⟨ρ ⟨b, hb⟩, AlgHom.mem_range_self ρ _⟩ : R) • m : V)) : H) = b m :=
    fun _ _ _ => rfl
  have : IsSimpleModule R V := by
    rw [isSimpleModule_iff_toSpanSingleton_surjective]
    refine ⟨hV, fun u hu w => ?_⟩
    obtain ⟨b, hb, hbw⟩ := htrans u w hu
    refine ⟨⟨ρ ⟨b, hb⟩, AlgHom.mem_range_self ρ _⟩, ?_⟩
    apply Subtype.ext
    rw [LinearMap.toSpanSingleton_apply, hρ, hbw]
  have hscalar : ∀ g : Module.End R V, ∃ μ : ℂ, ∀ m, g m = μ • m := by
    intro g
    have h1 : ∀ (c : ℂ) (m : V), (algebraMap ℂ R c) • m = c • m := by
      intro c m
      rw [hR]
      change algebraMap ℂ (Module.End ℂ V) c m = c • m
      exact Module.algebraMap_end_apply ℂ ℂ V c m
    have hsmul : ∀ (c : ℂ) (m : V), g (c • m) = c • g m := by
      intro c m
      rw [← h1, g.map_smul, h1]
    let g' : V →ₗ[ℂ] V := { toFun := g, map_add' := g.map_add, map_smul' := hsmul }
    have hg' : CommutesOn (B : Set (H →L[ℂ] H)) V g' := by
      intro b hb v w hw
      have hw' : w = (⟨ρ ⟨b, hb⟩, AlgHom.mem_range_self ρ _⟩ : R) • v := Subtype.ext hw
      change (g w : H) = b (g v)
      rw [hw', g.map_smul]
      rfl
    obtain ⟨μ, hμ⟩ := exists_eq_smul_id_of_commutesOn (B : Set (H →L[ℂ] H)) V hBV htrans g' hg'
    exact ⟨μ, fun m => LinearMap.congr_fun hμ m⟩
  let F : Module.End (Module.End R V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun g m => by
        obtain ⟨μ, hμ⟩ := hscalar g
        simp only [Module.End.smul_def, RingHom.id_apply, hμ, f.map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density (R := R) (M := V) F s
  obtain ⟨b, hb⟩ := r.2
  refine ⟨b, b.2, fun m hm => ?_⟩
  have := hr m hm
  change f m = r • m at this
  rw [this, hR, ← hb]
  rfl

end Density

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An operator `T` such that both `T` and `T†` preserve the closed subspace `K` commutes with
the orthogonal projection onto `K`. -/
theorem commute_starProjection_of_invariant (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (T : H →L[ℂ] H) (h1 : ∀ x ∈ K, T x ∈ K) (h2 : ∀ x ∈ K, star T x ∈ K) :
    T * K.starProjection = K.starProjection * T := by
  ext x
  rw [mul_apply_eq_comp, mul_apply_eq_comp]
  have hperp : T (x - K.starProjection x) ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint]
    exact (Submodule.mem_orthogonal _ _).mp (K.sub_starProjection_mem_orthogonal x) _ (h2 u hu)
  have hx : x = K.starProjection x + (x - K.starProjection x) := by abel
  conv_rhs => rw [hx, map_add, map_add]
  rw [(Submodule.starProjection_apply_eq_zero_iff K).mpr hperp, add_zero,
    Submodule.starProjection_eq_self_iff.mpr (h1 _ (K.starProjection_apply_mem x))]

/-- The orthogonal projection onto a closed subspace that is invariant under `S` and under the
adjoints of the elements of `S` lies in the star-commutant of `S`. -/
theorem starProjection_mem_centralizer (S : Set (H →L[ℂ] H)) (K : Submodule ℂ H)
    [K.HasOrthogonalProjection] (hK : ∀ s ∈ S, ∀ x ∈ K, s x ∈ K ∧ star s x ∈ K) :
    K.starProjection ∈ StarSubalgebra.centralizer ℂ S := by
  rw [StarSubalgebra.mem_centralizer_iff]
  intro g hg
  refine ⟨commute_starProjection_of_invariant K g (fun x hx => (hK g hg x hx).1)
      (fun x hx => (hK g hg x hx).2), ?_⟩
  refine commute_starProjection_of_invariant K (star g) (fun x hx => (hK g hg x hx).2) ?_
  simpa using fun x hx => (hK g hg x hx).1

/-- Polarization of the tracial identity `‖x ξ‖ = ‖x† ξ‖` on a star subalgebra. -/
theorem inner_eq_inner_star_of_norm_eq (N : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H)
    (hnorm : ∀ x ∈ N, ‖x ξ‖ = ‖star x ξ‖) {z w : H →L[ℂ] H} (hz : z ∈ N) (hw : w ∈ N) :
    ⟪z ξ, w ξ⟫_ℂ = ⟪star w ξ, star z ξ⟫_ℂ := by
  have key : ∀ c : ℂ, ‖z ξ + c • w ξ‖ = ‖star z ξ + (starRingEnd ℂ c) • star w ξ‖ := by
    intro c
    have := hnorm (z + c • w) (N.add_mem hz (N.smul_mem hw c))
    simpa [star_add, star_smul] using this
  set a := z ξ
  set b := w ξ
  set a' := star z ξ
  set b' := star w ξ
  have e1 : ‖a + b‖ = ‖b' + a'‖ := by
    have := key 1
    simp only [one_smul, map_one] at this
    rw [this, add_comm]
  have e2 : ‖a - b‖ = ‖b' - a'‖ := by
    have := key (-1)
    simp only [neg_smul, one_smul, map_neg, map_one, ← sub_eq_add_neg] at this
    rw [this, norm_sub_rev]
  have e3 : ‖a - Complex.I • b‖ = ‖b' - Complex.I • a'‖ := by
    have := key (-Complex.I)
    simp only [neg_smul, map_neg, Complex.conj_I, neg_neg, ← sub_eq_add_neg] at this
    rw [this]
    have h : b' - Complex.I • a' = (-Complex.I) • (a' + Complex.I • b') := by
      rw [smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul,
        sub_eq_add_neg, add_comm]
    rw [h, norm_smul, norm_neg, Complex.norm_I, one_mul]
  have e4 : ‖a + Complex.I • b‖ = ‖b' + Complex.I • a'‖ := by
    have := key Complex.I
    simp only [Complex.conj_I, neg_smul, ← sub_eq_add_neg] at this
    rw [this]
    have h : b' + Complex.I • a' = Complex.I • (a' - Complex.I • b') := by
      rw [smul_sub, smul_smul, Complex.I_mul_I, neg_smul, one_smul, sub_neg_eq_add, add_comm]
    rw [h, norm_smul, Complex.norm_I, one_mul]
  rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) a b, inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) b' a']
  simp only [RCLike.I_to_complex]
  rw [e1, e2, e3, e4]

omit [CompleteSpace H] in
/-- `⟪ξ, P ξ⟫ = ‖P ξ‖²` for an orthogonal projection `P`. -/
theorem inner_starProjection_self (K : Submodule ℂ H) [K.HasOrthogonalProjection] (ξ : H) :
    ⟪ξ, K.starProjection ξ⟫_ℂ = (‖K.starProjection ξ‖ : ℂ) ^ 2 := by
  have h : K.starProjection (K.starProjection ξ) = K.starProjection ξ :=
    K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem ξ)
  rw [← h, ← Submodule.inner_starProjection_left_eq_right, h, inner_self_eq_norm_sq_to_K]
  rfl

/-- **Finite dimensionality from a faithful tracial vector.** Let `N` be the star-commutant of
a set `S` of bounded operators on a complex Hilbert space and `ξ` a vector with
`‖x ξ‖ = ‖x† ξ‖` and `x ξ = 0 → x = 0` for `x ∈ N`. If a subalgebra `B ⊆ N` leaves the
subspace `V` invariant and acts transitively on it, then `V` is finite dimensional. -/
theorem finiteDimensional_of_tracial (S : Set (H →L[ℂ] H)) (ξ : H)
    (hnorm : ∀ x ∈ StarSubalgebra.centralizer ℂ S, ‖x ξ‖ = ‖star x ξ‖)
    (hsep : ∀ x ∈ StarSubalgebra.centralizer ℂ S, x ξ = 0 → x = 0)
    (B : Subalgebra ℂ (H →L[ℂ] H)) (hBN : ∀ b ∈ B, b ∈ StarSubalgebra.centralizer ℂ S)
    (V : Submodule ℂ H) (hBV : ∀ b ∈ B, ∀ v ∈ V, b v ∈ V)
    (htrans : ∀ u w : V, u ≠ 0 → ∃ b ∈ B, b u = w) :
    FiniteDimensional ℂ V := by
  classical
  set N := StarSubalgebra.centralizer ℂ S with hN
  -- the trace property
  have htr : ∀ x ∈ N, ∀ y ∈ N, ⟪ξ, (x * y) ξ⟫_ℂ = ⟪ξ, (y * x) ξ⟫_ℂ := by
    intro x hx y hy
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      ← ContinuousLinearMap.adjoint_inner_left x (y ξ) ξ,
      ← ContinuousLinearMap.adjoint_inner_left y (x ξ) ξ,
      ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
      inner_eq_inner_star_of_norm_eq N ξ hnorm (star_mem hx) hy, star_star]
  rcases subsingleton_or_nontrivial V with hV | hV
  · infer_instance
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  -- the closed subspace killed by the annihilator of `v` in `B`
  let Q : Submodule ℂ H :=
    { carrier := {x | ∀ c ∈ B, c (v : H) = 0 → c x = 0}
      add_mem' := fun {x y} hx hy c hc hcv => by rw [map_add, hx c hc hcv, hy c hc hcv, add_zero]
      zero_mem' := fun c _ _ => map_zero c
      smul_mem' := fun a x hx c hc hcv => by rw [map_smul, hx c hc hcv, smul_zero] }
  have hQc : IsClosed (Q : Set H) := by
    have : (Q : Set H) = ⋂ c ∈ {c | c ∈ B ∧ c (v : H) = 0}, (c : H → H) ⁻¹' {0} := by
      ext x
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
        and_imp]
      rfl
    rw [this]
    exact isClosed_biInter fun c _ => isClosed_singleton.preimage c.continuous
  have : CompleteSpace Q := hQc.completeSpace_coe
  set q := Q.starProjection with hq
  have hcommB : ∀ c ∈ B, ∀ s ∈ S, ∀ x : H, s (c x) = c (s x) ∧ star s (c x) = c (star s x) := by
    intro c hc s hs x
    have h := ((StarSubalgebra.mem_centralizer_iff (R := ℂ)).mp (hBN c hc)) s hs
    exact ⟨congrArg (fun T : H →L[ℂ] H => T x) h.1, congrArg (fun T : H →L[ℂ] H => T x) h.2⟩
  have hqN : q ∈ N := by
    apply starProjection_mem_centralizer
    intro s hs x hx
    refine ⟨fun c hc hcv => ?_, fun c hc hcv => ?_⟩
    · rw [← (hcommB c hc s hs x).1, hx c hc hcv, map_zero]
    · rw [← (hcommB c hc s hs x).2, hx c hc hcv, map_zero]
  have hqv : q v = v := Q.starProjection_eq_self_iff.mpr (fun c _ hcv => hcv)
  have hqξ : q ξ ≠ 0 := by
    intro h
    have h0 := hsep q hqN h
    apply hv
    apply Subtype.ext
    rw [← hqv, h0]
    rfl
  have hqq : q * q = q := Q.isIdempotentElem_starProjection
  have hτq : ⟪ξ, q ξ⟫_ℂ = (‖q ξ‖ : ℂ) ^ 2 := inner_starProjection_self Q ξ
  -- the trace inequality
  have hbound : ∀ s : Finset V, LinearIndependent ℂ (fun i : s => (i : V)) →
      (s.card : ℝ) * ‖q ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
    intro s hs
    have hs' : LinearIndepOn ℂ id (s : Set V) := hs
    let e := Module.Basis.extend hs'
    have hmem : ∀ i : s, (i : V) ∈ hs'.extend (Set.subset_univ _) :=
      fun i => Module.Basis.subset_extend hs' (Finset.mem_coe.mpr i.2)
    let φ : s → (V →ₗ[ℂ] ℂ) := fun i => e.coord ⟨i, hmem i⟩
    have hφ : ∀ i j : s, φ i (j : V) = if j = i then 1 else 0 := by
      intro i j
      have hj : (j : V) = e ⟨j, hmem j⟩ :=
        (Module.Basis.extend_apply_self hs' ⟨j, hmem j⟩).symm
      rw [hj]
      simp only [φ, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      by_cases hij : j = i
      · subst hij
        simp
      · simp [hij]
    have ha : ∀ i : s, ∃ a ∈ B, ∀ m ∈ s, (((φ i).smulRight v) m : H) = a m :=
      fun i => exists_mem_eq_on_finset B V hBV htrans _ s
    choose a haB ha using ha
    have hc : ∀ j : s, ∃ c ∈ B, c v = (j : V) := fun j => htrans v j hv
    choose c hcB hc using hc
    have hacv : ∀ i j : s, (a i * c j) v = if j = i then (v : H) else 0 := by
      intro i j
      rw [mul_apply_eq_comp, hc j, ← ha i j j.2, LinearMap.smulRight_apply, hφ]
      split_ifs <;> simp
    have hacq : ∀ i j : s, a i * c j * q = if j = i then q else 0 := by
      intro i j
      ext x
      have hqx : q x ∈ Q := Q.starProjection_apply_mem x
      have hv' := hacv i j
      split_ifs at hv' ⊢ with hij
      · have hmemB : a i * c j - 1 ∈ B := B.sub_mem (B.mul_mem (haB i) (hcB j)) B.one_mem
        have h := hqx _ hmemB (by rw [sub_apply, hv']; simp)
        rw [mul_apply_eq_comp]
        rw [sub_apply, sub_eq_zero] at h
        simpa using h
      · have hmemB : a i * c j ∈ B := B.mul_mem (haB i) (hcB j)
        have h := hqx _ hmemB hv'
        rw [mul_apply_eq_comp]
        simpa using h
    let x : s → (H →L[ℂ] H) := fun j => c j * q
    let y : s → (H →L[ℂ] H) := fun i => q * a i
    have hxN : ∀ j, x j ∈ N := fun j => N.mul_mem (hBN _ (hcB j)) hqN
    have hyN : ∀ i, y i ∈ N := fun i => N.mul_mem hqN (hBN _ (haB i))
    have hyx : ∀ i j, y i * x j = if j = i then q else 0 := by
      intro i j
      have h : y i * x j = q * (a i * c j * q) := by simp only [x, y, mul_assoc]
      rw [h, hacq]
      split_ifs
      · exact hqq
      · exact mul_zero q
    have hxqy : ∀ j, x j * q * y j = x j * y j := by
      intro j
      simp only [x, y, mul_assoc, ← mul_assoc q q, hqq]
    let p : H →L[ℂ] H := ∑ j, x j * y j
    have hpN : p ∈ N := N.sum_mem fun j _ => N.mul_mem (hxN j) (hyN j)
    have hxyxy : ∀ j k, x j * y j * (x k * y k) = if k = j then x j * y j else 0 := by
      intro j k
      have h : x j * y j * (x k * y k) = x j * (y j * x k) * y k := by
        simp only [mul_assoc]
      rw [h, hyx]
      split_ifs with hkj
      · subst hkj
        exact hxqy k
      · simp
    have hpp : p * p = p := by
      calc p * p = ∑ j, ∑ k, x j * y j * (x k * y k) := by
            simp only [p]
            rw [Finset.sum_mul]
            simp_rw [Finset.mul_sum]
        _ = p := by
            simp only [hxyxy, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
            rfl
    -- the projection onto the range of `p`
    let R : Submodule ℂ H := ((1 : H →L[ℂ] H) - p).ker
    have hmemR : ∀ z, z ∈ R ↔ p z = z := by
      intro z
      change (1 - p) z = 0 ↔ p z = z
      rw [show (1 - p) z = z - p z by simp, sub_eq_zero]
      exact eq_comm
    have hRc : IsClosed (R : Set H) := ContinuousLinearMap.isClosed_ker (1 - p)
    have : CompleteSpace R := hRc.completeSpace_coe
    set r := R.starProjection with hr
    have hrN : r ∈ N := by
      apply starProjection_mem_centralizer
      intro s' hs' z hz
      have hcomm := ((StarSubalgebra.mem_centralizer_iff (R := ℂ)).mp hpN) s' hs'
      rw [hmemR] at hz
      rw [hmemR, hmemR]
      constructor
      · have h := congrArg (fun T : H →L[ℂ] H => T z) hcomm.1
        simp only [mul_apply_eq_comp] at h
        rw [← h, hz]
      · have h := congrArg (fun T : H →L[ℂ] H => T z) hcomm.2
        simp only [mul_apply_eq_comp] at h
        rw [← h, hz]
    have hrp : r * p = p := by
      ext z
      rw [mul_apply_eq_comp]
      refine R.starProjection_eq_self_iff.mpr ((hmemR _).mpr ?_)
      rw [← mul_apply_eq_comp, hpp]
    have hpr : p * r = r := by
      ext z
      rw [mul_apply_eq_comp]
      exact (hmemR _).mp (R.starProjection_apply_mem z)
    have hτp : ⟪ξ, p ξ⟫_ℂ = (‖r ξ‖ : ℂ) ^ 2 := by
      rw [← hrp, htr r hrN p hpN, hpr]
      exact inner_starProjection_self R ξ
    have hτp' : ⟪ξ, p ξ⟫_ℂ = (s.card : ℂ) * (‖q ξ‖ : ℂ) ^ 2 := by
      simp only [p, _root_.sum_apply, inner_sum]
      rw [Finset.sum_congr rfl fun j _ => htr (x j) (hxN j) (y j) (hyN j)]
      simp only [hyx, ite_true, hτq, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        nsmul_eq_mul]
    have hreal : (s.card : ℝ) * ‖q ξ‖ ^ 2 = ‖r ξ‖ ^ 2 := by
      have h := hτp'.symm.trans hτp
      exact_mod_cast h
    rw [hreal]
    exact pow_le_pow_left₀ (norm_nonneg _) (R.norm_starProjection_apply_le ξ) 2
  have hpos : 0 < ‖q ξ‖ ^ 2 := by
    have := norm_pos_iff.mpr hqξ
    positivity
  have hrank : Module.rank ℂ V ≤ (⌊‖ξ‖ ^ 2 / ‖q ξ‖ ^ 2⌋₊ : ℕ) := by
    apply rank_le
    intro s hs
    apply Nat.le_floor
    rw [le_div_iff₀ hpos]
    exact hbound s hs
  exact Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank Cardinal.natCast_lt_aleph0)

/-- Variant of `finiteDimensional_of_tracial` in which the transitive family is the set of all
elements of the star-commutant of `S` that preserve `V`. -/
theorem finiteDimensional_of_tracial' (S : Set (H →L[ℂ] H)) (ξ : H)
    (hnorm : ∀ x ∈ StarSubalgebra.centralizer ℂ S, ‖x ξ‖ = ‖star x ξ‖)
    (hsep : ∀ x ∈ StarSubalgebra.centralizer ℂ S, x ξ = 0 → x = 0)
    (V : Submodule ℂ H)
    (htrans : ∀ u w : V, u ≠ 0 →
      ∃ b ∈ StarSubalgebra.centralizer ℂ S, (∀ v ∈ V, b v ∈ V) ∧ b u = w) :
    FiniteDimensional ℂ V := by
  let B : Subalgebra ℂ (H →L[ℂ] H) :=
    { carrier := {b | b ∈ StarSubalgebra.centralizer ℂ S ∧ ∀ v ∈ V, b v ∈ V}
      mul_mem' := fun {f g} hf hg => ⟨mul_mem hf.1 hg.1, fun v hv => hf.2 _ (hg.2 v hv)⟩
      add_mem' := fun {f g} hf hg =>
        ⟨add_mem hf.1 hg.1, fun v hv => V.add_mem (hf.2 v hv) (hg.2 v hv)⟩
      algebraMap_mem' := fun c =>
        ⟨(StarSubalgebra.centralizer ℂ S).algebraMap_mem c, fun v hv => by
          simpa [Algebra.algebraMap_eq_smul_one] using V.smul_mem c hv⟩ }
  exact finiteDimensional_of_tracial S ξ hnorm hsep B (fun b hb => hb.1) V (fun b hb => hb.2)
    (fun u w hu => by
      obtain ⟨b, hb, hbV, hbu⟩ := htrans u w hu
      exact ⟨b, ⟨hb, hbV⟩, hbu⟩)

end Hilbert

end Langlands.Analysis
