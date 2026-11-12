import Langlands.GroupScheme.Torus.DiagonalizableSmoothConnectedCriteriaStatement
import Langlands.GroupScheme.Torus.SmoothConnectedKernelCocharacters
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Torus.DiagonalizablePowerDecomposition
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Smoothness and connectedness of diagonalizable groups: proof -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace Diagonalizable

namespace SmoothConnectedCriteria

/-! ### Idempotents and connectedness of a prime spectrum -/

section Idempotent

variable {A : Type u} [CommRing A]

/-- In a ring with connected prime spectrum, every idempotent is `0` or `1`. -/
theorem eq_zero_or_one_of_connectedSpace [ConnectedSpace (PrimeSpectrum A)] {e : A}
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hc : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum A)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  rcases isClopen_iff.mp hc with h | h
  · left
    apply he.eq_zero_of_isNilpotent
    rw [← PrimeSpectrum.basicOpen_eq_bot_iff]
    exact SetLike.coe_injective h
  · right
    have h' : (PrimeSpectrum.basicOpen (1 - e) : Set (PrimeSpectrum A)) = ∅ := by
      rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl,
        ← PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem e he, h, Set.compl_univ]
    have h1 : 1 - e = 0 := he.one_sub.eq_zero_of_isNilpotent
      ((PrimeSpectrum.basicOpen_eq_bot_iff _).mp (SetLike.coe_injective h'))
    exact (sub_eq_zero.mp h1).symm

/-- A nonzero ring whose only idempotents are `0` and `1` has connected prime spectrum. -/
theorem connectedSpace_of_forall_idempotent [Nontrivial A]
    (h : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) : ConnectedSpace (PrimeSpectrum A) := by
  rw [connectedSpace_iff_clopen]
  refine ⟨inferInstance, fun s hs => ?_⟩
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
  rcases h e he with rfl | rfl
  · left
    simp
  · right
    simp

/-- The geometric sum of an element of finite order is fixed by multiplication by it. -/
theorem geomSum_mul_self {g : A} {m : ℕ} (hg : g ^ m = 1) :
    (∑ i ∈ Finset.range m, g ^ i) * g = ∑ i ∈ Finset.range m, g ^ i := by
  have h := geom_sum_mul g m
  rw [hg, sub_self, mul_sub, mul_one, sub_eq_zero] at h
  exact h

/-- If `g ^ m = 1` and `m` is invertible, then `m⁻¹ ∑_{i < m} g ^ i` is idempotent. -/
theorem isIdempotentElem_geomSum {g : A} {m : ℕ} (hg : g ^ m = 1) {c : A}
    (hc : c * m = 1) : IsIdempotentElem (c * ∑ i ∈ Finset.range m, g ^ i) := by
  set S := ∑ i ∈ Finset.range m, g ^ i
  have hSg : ∀ i : ℕ, S * g ^ i = S := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, ← mul_assoc, ih, geomSum_mul_self hg]
  have hSS : S * S = (m : A) * S := by
    conv_lhs => rw [show S * S = S * ∑ i ∈ Finset.range m, g ^ i from rfl]
    rw [Finset.mul_sum]
    simp only [hSg, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  change (c * S) * (c * S) = c * S
  calc (c * S) * (c * S) = c * (c * (S * S)) := by ring
    _ = c * S := by rw [hSS, ← mul_assoc c (m : A) S, hc, one_mul]

end Idempotent

/-! ### Part 1, forward: connectedness forces `p`-power torsion -/

section ConnectedForward

variable (k : Type u) [Field k] (p : ℕ) [ExpChar k p] {Λ : Type u} [AddCommGroup Λ]

/-- A positive integer factors as a power of the characteristic exponent times a factor that
is nonzero in the field. -/
theorem exists_pow_mul_ne_zero {N : ℕ} (hN : N ≠ 0) :
    ∃ a m : ℕ, (m : k) ≠ 0 ∧ N = p ^ a * m := by
  rcases ‹ExpChar k p› with _ | ⟨hp⟩
  · exact ⟨0, N, Nat.cast_ne_zero.mpr hN, by simp⟩
  · obtain ⟨a, m, hm, hNm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN _ hp.ne_one
    refine ⟨a, m, ?_, hNm⟩
    rwa [Ne, CharP.cast_eq_zero_iff k p]

/-- If every idempotent of `k[Λ]` is `0` or `1`, then every torsion element of `Λ` is killed by
a power of the characteristic exponent. -/
theorem exists_pow_nsmul_eq_zero
    (h : ∀ e : AddMonoidAlgebra k Λ, IsIdempotentElem e → e = 0 ∨ e = 1)
    {x : Λ} (hx : IsOfFinAddOrder x) : ∃ n : ℕ, p ^ n • x = 0 := by
  classical
  by_contra hcon
  simp only [not_exists] at hcon
  obtain ⟨a, m, hm, hNm⟩ := exists_pow_mul_ne_zero k p hx.addOrderOf_pos.ne'
  set y := p ^ a • x with hy
  have hy0 : y ≠ 0 := hcon a
  have hmy : m • y = 0 := by
    rw [hy, smul_smul, mul_comm, ← hNm, addOrderOf_nsmul_eq_zero]
  let g : AddMonoidAlgebra k Λ := AddMonoidAlgebra.single y 1
  have hg : g ^ m = 1 := by
    simp only [g, AddMonoidAlgebra.single_pow, hmy, one_pow, AddMonoidAlgebra.one_def]
  let c : AddMonoidAlgebra k Λ := algebraMap k _ (m : k)⁻¹
  have hc : c * m = 1 := by
    simp only [c]
    rw [← map_natCast (algebraMap k (AddMonoidAlgebra k Λ)), ← map_mul, inv_mul_cancel₀ hm,
      map_one]
  have he := isIdempotentElem_geomSum hg hc
  rcases h _ he with h0 | h1
  · let ε : AddMonoidAlgebra k Λ →ₐ[k] k := AddMonoidAlgebra.lift k k Λ 1
    have h' := congrArg ε h0
    simp only [ε, c, g, map_mul, AlgHom.commutes, map_sum, map_pow,
      AddMonoidAlgebra.lift_single, MonoidHom.one_apply, one_smul, one_pow,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, map_zero,
      Algebra.algebraMap_self, RingHom.id_apply] at h'
    rw [inv_mul_cancel₀ hm] at h'
    exact one_ne_zero h'
  · have h2 : (g - 1) * (c * ∑ i ∈ Finset.range m, g ^ i) = 0 := by
      rw [mul_left_comm, mul_comm (g - 1), mul_sub, mul_one, geomSum_mul_self hg, sub_self,
        mul_zero]
    rw [h1, mul_one, sub_eq_zero, AddMonoidAlgebra.one_def] at h2
    exact hy0 (AddMonoidAlgebra.single_left_injective one_ne_zero h2)

end ConnectedForward

/-! ### Part 1, backward: `p`-power torsion gives connectedness -/

section ConnectedBackward

variable (k : Type u) [Field k] (p : ℕ) [ExpChar k p]

/-- The connected spectrum of `k[F]` for `F = I → ℤ`, read off from the split torus `D(F)`. -/
theorem eq_zero_or_one_free {I : Type u} [Fintype I] [DecidableEq I]
    {e : AddMonoidAlgebra k (I → ℤ)} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hc : ConnectedSpace (groupScheme (CommRingCat.of k) (I → ℤ)).X.left :=
    IsSplitTorus.connectedSpace (isSplitTorus_free (CommRingCat.of k) (I := I))
  have : ConnectedSpace (PrimeSpectrum (AddMonoidAlgebra k (I → ℤ))) := hc
  exact eq_zero_or_one_of_connectedSpace he

/-- If `p ^ N` kills `A`, then the `p ^ N`-th power on `k[F × A]` factors through the
projection `k[F × A] → k[F]`. -/
theorem pow_expChar_pow_eq {F A : Type u} [AddCommGroup F] [AddCommGroup A] (N : ℕ)
    (hN : ∀ a : A, p ^ N • a = 0) (f : AddMonoidAlgebra k (F × A)) :
    f ^ p ^ N = AddMonoidAlgebra.mapDomainRingHom k
        ((AddMonoidHom.inl F A).comp ((p ^ N) • AddMonoidHom.id F))
      (AddMonoidAlgebra.mapRingHom F (iterateFrobenius k p N)
        (AddMonoidAlgebra.mapDomainRingHom k (AddMonoidHom.fst F A) f)) := by
  have hinj : Function.Injective (algebraMap k (AddMonoidAlgebra k (F × A))) :=
    (algebraMap k _).injective
  have : ExpChar (AddMonoidAlgebra k (F × A)) p := expChar_of_injective_algebraMap hinj p
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => rw [zero_pow (pow_ne_zero _ (expChar_pos k p).ne'), map_zero, map_zero, map_zero]
  | add f g hf hg => rw [add_pow_expChar_pow, hf, hg, map_add, map_add, map_add]
  | single z r =>
    simp only [AddMonoidAlgebra.single_pow, AddMonoidAlgebra.mapDomainRingHom_apply,
      AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.mapRingHom_single]
    rw [iterateFrobenius_def]
    congr 1
    ext <;> simp [hN]

/-- Over `F × A` with `A` killed by `p ^ N`, idempotents of `k[F × A]` are `0` or `1` as soon
as those of `k[F]` are. -/
theorem eq_zero_or_one_prod {F A : Type u} [AddCommGroup F] [AddCommGroup A] (N : ℕ)
    (hN : ∀ a : A, p ^ N • a = 0)
    (hF : ∀ e : AddMonoidAlgebra k F, IsIdempotentElem e → e = 0 ∨ e = 1)
    {e : AddMonoidAlgebra k (F × A)} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hφ := he.map (AddMonoidAlgebra.mapDomainRingHom k (AddMonoidHom.fst F A))
  have hpow : e ^ p ^ N = e := he.pow_eq (pow_ne_zero _ (expChar_pos k p).ne')
  rcases hF _ hφ with h0 | h1
  · left
    rw [← hpow, pow_expChar_pow_eq k p N hN, h0, map_zero, map_zero]
  · right
    rw [← hpow, pow_expChar_pow_eq k p N hN, h1, map_one, map_one]

/-- If every torsion element of a finitely generated `Λ` is killed by a power of `p`, then the
only idempotents of `k[Λ]` are `0` and `1`. -/
theorem eq_zero_or_one_of_pTorsion (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ]
    (h : ∀ x : Λ, IsOfFinAddOrder x → ∃ n : ℕ, p ^ n • x = 0)
    {e : AddMonoidAlgebra k Λ} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  classical
  obtain ⟨I, A, hI, hA, hfin, ⟨b⟩⟩ := exists_freeFiniteEquiv Λ
  have := Fintype.ofFinite A
  have ha : ∀ a : A, ∃ n : ℕ, p ^ n • a = 0 := by
    intro a
    have hx : IsOfFinAddOrder (b.symm (0, a)) := by
      rw [isOfFinAddOrder_iff_nsmul_eq_zero]
      refine ⟨Nat.card A, Nat.card_pos, ?_⟩
      rw [← map_nsmul, Prod.smul_mk, smul_zero, card_nsmul_eq_zero', Prod.mk_zero_zero,
        map_zero]
    obtain ⟨n, hn⟩ := h _ hx
    refine ⟨n, ?_⟩
    have h' := congrArg b hn
    rw [map_nsmul, AddEquiv.apply_symm_apply, map_zero, Prod.smul_mk, smul_zero] at h'
    exact (Prod.mk_eq_zero.mp h').2
  choose n hn using ha
  set N := Finset.univ.sup n
  have hN : ∀ a : A, p ^ N • a = 0 := by
    intro a
    have hle : n a ≤ N := Finset.le_sup (Finset.mem_univ a)
    rw [← pow_sub_mul_pow p hle, ← smul_smul, hn a, smul_zero]
  let φ := AddMonoidAlgebra.domCongr k k b
  rcases eq_zero_or_one_prod k p N hN (fun e he => eq_zero_or_one_free k he) (he.map φ)
    with h0 | h1
  · left
    exact φ.injective (by rw [h0, map_zero])
  · right
    exact φ.injective (by rw [h1, map_one])

end ConnectedBackward

/-! ### Part 2, forward: smoothness forbids `p`-torsion -/

section SmoothForward

variable (k : Type u) [Field k] (p : ℕ) [ExpChar k p] {Λ : Type u} [AddCommGroup Λ]

/-- If `k[Λ]` is reduced, then `Λ` has no nonzero element killed by the characteristic
exponent. -/
theorem eq_zero_of_isReduced [IsReduced (AddMonoidAlgebra k Λ)] {x : Λ} (hx : p • x = 0) :
    x = 0 := by
  have hinj : Function.Injective (algebraMap k (AddMonoidAlgebra k Λ)) :=
    (algebraMap k (AddMonoidAlgebra k Λ)).injective
  have : ExpChar (AddMonoidAlgebra k Λ) p := expChar_of_injective_algebraMap hinj p
  have hnil : IsNilpotent (AddMonoidAlgebra.single x (1 : k) - 1) := by
    refine ⟨p, ?_⟩
    rw [sub_pow_expChar, AddMonoidAlgebra.single_pow, hx, one_pow, one_pow,
      AddMonoidAlgebra.one_def, sub_self]
  have h0 := hnil.eq_zero
  rw [sub_eq_zero, AddMonoidAlgebra.one_def] at h0
  exact AddMonoidAlgebra.single_left_injective one_ne_zero h0

end SmoothForward

/-! ### Part 2, backward: without `p`-torsion, `k[Λ]` is smooth -/

section Lifting

/-- Additive homomorphisms out of `ZMod m` agree once they agree on `1`. -/
theorem zmod_addHom_ext {V : Type*} [AddCommGroup V] {m : ℕ} {f g : ZMod m →+ V}
    (h : f 1 = g 1) : f = g := by
  refine AddMonoidHom.ext fun z => ?_
  obtain ⟨t, rfl⟩ := ZMod.intCast_surjective z
  rw [← zsmul_one, map_zsmul, map_zsmul, h]

/-- Homomorphisms out of `ℤ^(n) × ⨁ i, ZMod (m i)` lift along a surjection `π` that lifts
elements killed by `m i` to elements killed by `m i`. -/
theorem exists_lift_free_prod_zmod {U V : Type*} [AddCommGroup U] [AddCommGroup V]
    (π : U →+ V) (hπ : Function.Surjective π) {n : ℕ} {ι : Type} [DecidableEq ι]
    (m : ι → ℕ) (htors : ∀ i, ∀ v : V, m i • v = 0 → ∃ u : U, π u = v ∧ m i • u = 0)
    (χ : (Fin n →₀ ℤ) × (DirectSum ι fun i => ZMod (m i)) →+ V) :
    ∃ ψ : (Fin n →₀ ℤ) × (DirectSum ι fun i => ZMod (m i)) →+ U, π.comp ψ = χ := by
  classical
  choose uF huF using fun j : Fin n => hπ (χ (Finsupp.single j 1, 0))
  have hv : ∀ i, m i • χ (0, DirectSum.of (fun i => ZMod (m i)) i 1) = 0 := by
    intro i
    rw [← map_nsmul, Prod.smul_mk, smul_zero, ← map_nsmul, nsmul_one, ZMod.natCast_self,
      map_zero, Prod.mk_zero_zero, map_zero]
  choose uT huT using fun i => htors i _ (hv i)
  let ψi : ∀ i, ZMod (m i) →+ U := fun i =>
    ZMod.lift (m i) ⟨zmultiplesHom U (uT i), by
      rw [zmultiplesHom_apply, natCast_zsmul, (huT i).2]⟩
  let ψF : (Fin n →₀ ℤ) →+ U := Finsupp.liftAddHom fun j => zmultiplesHom U (uF j)
  let ψT : (DirectSum ι fun i => ZMod (m i)) →+ U := DirectSum.toAddMonoid ψi
  refine ⟨ψF.coprod ψT, ?_⟩
  have hF : π.comp ψF = χ.comp (AddMonoidHom.inl _ _) := by
    refine Finsupp.addHom_ext' fun j => AddMonoidHom.ext_int ?_
    simp only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply, AddMonoidHom.inl_apply, ψF,
      Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, one_zsmul, huF]
  have hT : π.comp ψT = χ.comp (AddMonoidHom.inr _ _) := by
    refine DirectSum.addHom_ext' fun i => zmod_addHom_ext ?_
    have h1 : ψi i 1 = uT i := by
      have h1' : (1 : ZMod (m i)) = ((1 : ℤ) : ZMod (m i)) := Int.cast_one.symm
      rw [h1']
      simp only [ψi, ZMod.lift_coe, zmultiplesHom_apply, one_zsmul]
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.inr_apply, ψT, DirectSum.toAddMonoid_of, h1,
      (huT i).1]
  rw [AddMonoidHom.comp_coprod, hF, hT, ← AddMonoidHom.comp_coprod, AddMonoidHom.coprod_inl_inr,
    AddMonoidHom.comp_id]

variable {B : Type*} [CommRing B] (I : Ideal B)

/-- Products of two elements of a square-zero ideal vanish. -/
theorem mul_eq_zero_of_sq_eq_bot (hI : I ^ 2 = ⊥) {a b : B} (ha : a ∈ I) (hb : b ∈ I) :
    a * b = 0 := by
  have h : a * b ∈ I ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul ha hb
  rw [hI] at h
  exact h

/-- Units lift along the quotient by a square-zero ideal. -/
theorem exists_unit_lift (hI : I ^ 2 = ⊥) (v : (B ⧸ I)ˣ) :
    ∃ u : Bˣ, Units.map (Ideal.Quotient.mk I : B →* B ⧸ I) u = v := by
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (v : B ⧸ I)
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (↑v⁻¹ : B ⧸ I)
  have ha : b * c - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hb, hc, Units.mul_inv, map_one,
      sub_self]
  have haa := mul_eq_zero_of_sq_eq_bot I hI ha ha
  have hu : b * (c * (1 - (b * c - 1))) = 1 := by
    linear_combination (-1 : B) * haa
  refine ⟨⟨b, c * (1 - (b * c - 1)), hu, by rw [mul_comm]; exact hu⟩, ?_⟩
  ext
  exact hb

/-- An element of `(B ⧸ I)ˣ` killed by `n`, with `n` invertible in `B`, lifts to an element of
`Bˣ` killed by `n`. -/
theorem exists_unit_lift_pow_eq_one (hI : I ^ 2 = ⊥) {n : ℕ} (hn : IsUnit (n : B))
    (v : (B ⧸ I)ˣ) (hv : v ^ n = 1) :
    ∃ u : Bˣ, Units.map (Ideal.Quotient.mk I : B →* B ⧸ I) u = v ∧ u ^ n = 1 := by
  obtain ⟨u₀, hu₀⟩ := exists_unit_lift I hI v
  have ha : ((u₀ : B) ^ n - 1) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one]
    have h' := congrArg (fun w : (B ⧸ I)ˣ => ((w ^ n : (B ⧸ I)ˣ) : B ⧸ I)) hu₀
    simp only [Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe, hv, Units.val_one]
      at h'
    rw [h', sub_self]
  obtain ⟨c, hc⟩ := hn.exists_left_inv
  set a := (u₀ : B) ^ n - 1 with ha_def
  have hca : c * a ∈ I := I.mul_mem_left c ha
  have hsq := mul_eq_zero_of_sq_eq_bot I hI hca hca
  have hpow : ∀ j : ℕ, (1 - c * a) ^ j = 1 - (j : B) * (c * a) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ih]
      push_cast
      linear_combination (j : B) * hsq
  have ht : (1 - c * a) * (1 + c * a) = 1 := by
    linear_combination (-1 : B) * hsq
  let t : Bˣ := ⟨1 - c * a, 1 + c * a, ht, by rw [mul_comm]; exact ht⟩
  have haa : a * a = 0 := mul_eq_zero_of_sq_eq_bot I hI ha ha
  refine ⟨u₀ * t, ?_, ?_⟩
  · rw [map_mul, hu₀]
    have ht1 : Units.map (Ideal.Quotient.mk I : B →* B ⧸ I) t = 1 := by
      ext
      simp only [t, Units.coe_map, MonoidHom.coe_coe, map_sub, map_one, Units.val_one,
        Ideal.Quotient.eq_zero_iff_mem.mpr hca, sub_zero]
    rw [ht1, mul_one]
  · ext
    rw [Units.val_pow_eq_pow_val, Units.val_mul, mul_pow, Units.val_one]
    change (u₀ : B) ^ n * (1 - c * a) ^ n = 1
    rw [hpow n]
    have hu : (u₀ : B) ^ n = 1 + a := by rw [ha_def]; ring
    rw [hu]
    linear_combination (-a) * hc + (-(n : B) * c) * haa

end Lifting

section SmoothBackward

variable (k : Type u) [Field k] (p : ℕ) [ExpChar k p]

/-- A prime power that is zero in `k` produces a nonzero element killed by `p`. -/
theorem primePow_ne_zero {ι : Type} {n : ℕ} {q e : ι → ℕ} (hq : ∀ i, (q i).Prime)
    {Λ : Type u} [AddCommGroup Λ]
    (b : Λ ≃+ (Fin n →₀ ℤ) × DirectSum ι fun i => ZMod (q i ^ e i))
    (h : ∀ x : Λ, p • x = 0 → x = 0) (i : ι) : ((q i ^ e i : ℕ) : k) ≠ 0 := by
  classical
  rcases ‹ExpChar k p› with _ | ⟨hp⟩
  · exact Nat.cast_ne_zero.mpr (pow_ne_zero _ (hq i).ne_zero)
  · intro h0
    rw [CharP.cast_eq_zero_iff k p] at h0
    have hpq : p = q i := (Nat.prime_dvd_prime_iff_eq hp (hq i)).mp (hp.dvd_of_dvd_pow h0)
    have he : e i ≠ 0 := by
      rintro he
      rw [he, pow_zero] at h0
      exact hp.one_lt.ne' (Nat.dvd_one.mp h0)
    set c : ZMod (q i ^ e i) := ((q i ^ (e i - 1) : ℕ) : ZMod (q i ^ e i))
    have hpc : p • c = 0 := by
      rw [nsmul_eq_mul, hpq, ← Nat.cast_mul, ← pow_succ', Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr he), ZMod.natCast_self]
    have hz := h (b.symm (0, DirectSum.of (fun i => ZMod (q i ^ e i)) i c)) (by
      rw [← map_nsmul, Prod.smul_mk, smul_zero, ← map_nsmul, hpc, map_zero, Prod.mk_zero_zero,
        map_zero])
    rw [AddEquivClass.map_eq_zero_iff, Prod.mk_eq_zero] at hz
    have hc0 : c = 0 := DirectSum.of_injective (β := fun i => ZMod (q i ^ e i)) i
      (by rw [hz.2, map_zero])
    rw [CharP.cast_eq_zero_iff (ZMod (q i ^ e i)) (q i ^ e i)] at hc0
    have hpos : 0 < q i ^ (e i - 1) := pow_pos (hq i).pos _
    have hlt : q i ^ (e i - 1) < q i ^ e i :=
      Nat.pow_lt_pow_right (hq i).one_lt (Nat.sub_lt (Nat.pos_of_ne_zero he) one_pos)
    exact absurd (Nat.le_of_dvd hpos hc0) (not_le.mpr hlt)

/-- If `Λ` is finitely generated without nonzero elements killed by `p`, then `k[Λ]` is formally
smooth over `k`. -/
theorem formallySmooth_of_forall (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ]
    (h : ∀ x : Λ, p • x = 0 → x = 0) : Algebra.FormallySmooth k (AddMonoidAlgebra k Λ) := by
  classical
  obtain ⟨n, ι, hι, q, hq, e, ⟨b⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod Λ
  have hne := primePow_ne_zero k p hq b h
  refine Algebra.FormallySmooth.of_comp_surjective fun B _ _ I hI g => ?_
  let π : Additive Bˣ →+ Additive (B ⧸ I)ˣ :=
    MonoidHom.toAdditive (Units.map (Ideal.Quotient.mk I : B →* B ⧸ I))
  have hπ : Function.Surjective π := fun v => by
    obtain ⟨u, hu⟩ := exists_unit_lift I hI v.toMul
    exact ⟨Additive.ofMul u, congrArg Additive.ofMul hu⟩
  have htors : ∀ i, ∀ v : Additive (B ⧸ I)ˣ, (q i ^ e i) • v = 0 →
      ∃ u : Additive Bˣ, π u = v ∧ (q i ^ e i) • u = 0 := by
    intro i v hv
    have hunit : IsUnit (((q i ^ e i : ℕ) : B)) := by
      rw [← map_natCast (algebraMap k B)]
      exact (Ne.isUnit (hne i)).map _
    obtain ⟨u, hu, hu1⟩ := exists_unit_lift_pow_eq_one I hI hunit v.toMul
      (congrArg Additive.toMul hv)
    exact ⟨Additive.ofMul u, congrArg Additive.ofMul hu, congrArg Additive.ofMul hu1⟩
  let χ : Λ →+ Additive (B ⧸ I)ˣ :=
    MonoidHom.toAdditiveRight ((AddMonoidAlgebra.lift k (B ⧸ I) Λ).symm g).toHomUnits
  obtain ⟨ψ, hψ⟩ := exists_lift_free_prod_zmod π hπ (fun i => q i ^ e i) htors
    (χ.comp b.symm.toAddMonoidHom)
  let χ' : Multiplicative Λ →* B :=
    (Units.coeHom B).comp (AddMonoidHom.toMultiplicativeLeft (ψ.comp b.toAddMonoidHom))
  refine ⟨AddMonoidAlgebra.lift k B Λ χ', ?_⟩
  apply AddMonoidAlgebra.algHom_ext
  · intro x
    have hx := DFunLike.congr_fun hψ (b x)
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
      AddEquiv.symm_apply_apply] at hx
    have hx' := congrArg (fun w : Additive (B ⧸ I)ˣ => ((Additive.toMul w : (B ⧸ I)ˣ) : B ⧸ I))
      hx
    simp only [AlgHom.comp_apply, AddMonoidAlgebra.lift_single, one_smul,
      Ideal.Quotient.mkₐ_eq_mk]
    exact hx'
  · exact Subsingleton.elim _ _

end SmoothBackward

/-! ### From the group algebra to the scheme `D(Λ)` -/

section Bridge

variable (k : Type u) [Field k] (Λ : Type u) [AddCommGroup Λ]

/-- Connectedness of `D(Λ)` is connectedness of the prime spectrum of `k[Λ]`. -/
theorem connectedSpace_groupScheme_iff :
    ConnectedSpace (groupScheme (CommRingCat.of k) Λ).X.left ↔
      ConnectedSpace (PrimeSpectrum (AddMonoidAlgebra k Λ)) :=
  Iff.rfl

/-- Smoothness of `D(Λ)` over `k` is smoothness of the `k`-algebra `k[Λ]`. -/
theorem smooth_groupScheme_iff :
    Smooth (groupScheme (CommRingCat.of k) Λ).X.hom ↔ Algebra.Smooth k (AddMonoidAlgebra k Λ) := by
  change Smooth (Spec.map (CommRingCat.ofHom
    (algebraMap (CommRingCat.of k) (AddMonoidAlgebra (CommRingCat.of k) Λ)))) ↔ _
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap

/-- If `D(Λ)` is smooth over `k`, then `k[Λ]` is reduced. -/
theorem isReduced_of_smooth [Smooth (groupScheme (CommRingCat.of k) Λ).X.hom] :
    IsReduced (AddMonoidAlgebra k Λ) := by
  have : ∀ x : (groupScheme (CommRingCat.of k) Λ).X.left,
      IsReduced ((groupScheme (CommRingCat.of k) Λ).X.left.presheaf.stalk x) := fun x => by
    have := (Smooth.isDomain_and_isIntegrallyClosed_stalk
      (groupScheme (CommRingCat.of k) Λ).X.hom x).1
    infer_instance
  have hX : AlgebraicGeometry.IsReduced (groupScheme (CommRingCat.of k) Λ).X.left :=
    isReduced_of_isReduced_stalk _
  have hS : AlgebraicGeometry.IsReduced
      (Spec (CommRingCat.of (AddMonoidAlgebra (CommRingCat.of k) Λ))) := hX
  exact (affine_isReduced_iff _).mp hS

end Bridge

end SmoothConnectedCriteria

open SmoothConnectedCriteria in
/-- **Smoothness and connectedness criteria for `D(Λ)`** (Milne, *Algebraic Groups* (2017),
Remark 12.5). -/
theorem diagonalizableSmoothConnectedCriteria :
    DiagonalizableSmoothConnectedCriteriaStatement.{u} := by
  intro k _ p _ Λ _ _
  have hconn : ConnectedSpace (groupScheme (CommRingCat.of k) Λ).X.left ↔
      ∀ x : Λ, IsOfFinAddOrder x → ∃ n : ℕ, p ^ n • x = 0 := by
    rw [connectedSpace_groupScheme_iff]
    constructor
    · intro hc x hx
      exact exists_pow_nsmul_eq_zero k p (fun e he => eq_zero_or_one_of_connectedSpace he) hx
    · intro h
      exact connectedSpace_of_forall_idempotent fun e he => eq_zero_or_one_of_pTorsion k p Λ h he
  have hsmooth : Smooth (groupScheme (CommRingCat.of k) Λ).X.hom ↔
      ∀ x : Λ, p • x = 0 → x = 0 := by
    constructor
    · intro hs x hx
      have := isReduced_of_smooth k Λ
      exact eq_zero_of_isReduced k p hx
    · intro h
      rw [smooth_groupScheme_iff]
      have : Algebra.FormallySmooth k (AddMonoidAlgebra k Λ) := formallySmooth_of_forall k p Λ h
      have : Algebra.FinitePresentation k (AddMonoidAlgebra k Λ) :=
        Algebra.FinitePresentation.of_finiteType.mp inferInstance
      exact ⟨inferInstance, inferInstance⟩
  refine ⟨hconn, hsmooth, ?_⟩
  constructor
  · rintro ⟨h₁, h₂⟩
    exact free_of_smooth_connected k Λ
  · intro hfree
    have : Module.Finite ℤ Λ := Module.Finite.iff_addGroup_fg.mpr inferInstance
    classical
    let b := Module.Free.chooseBasis ℤ Λ
    have hT := isSplitTorus (CommRingCat.of k) b.equivFun.toAddEquiv
    exact ⟨hT.smooth, hT.connectedSpace⟩

end Diagonalizable

end Langlands.GroupScheme
