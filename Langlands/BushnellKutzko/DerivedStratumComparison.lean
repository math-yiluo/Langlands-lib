import Langlands.BushnellKutzko.DerivedStratumNonsplit
import Langlands.BushnellKutzko.RefinementProof

/-! # Comparison of derived strata through the residue algebra `𝔄/𝔓` -/

open Polynomial ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uO uK uV uF uE

/-! ### The element `y_b` -/

namespace Stratum

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

omit [Field K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] in
theorem _root_.Langlands.BushnellKutzko.RingPrimeElement.mem_jacobson (π : RingPrimeElement O) :
    π.1 ∈ Ring.jacobson O := by
  obtain ⟨p, -, hp⟩ := π
  change p ∈ Ring.jacobson O
  rw [← hp]
  exact Ideal.mem_span_singleton_self p

/-- A prime element moves every lattice of the chain forward by the period. -/
theorem primeElement_smul_mem (C : LatticeChain O K V) (π : RingPrimeElement O) (k : ℕ)
    {i : ℤ} {v : V} (hv : v ∈ C.lattice i) :
    (algebraMap O K π.1) ^ k • v ∈ C.lattice (i + k * C.period) := by
  have hJ : π.1 ∈ Ring.jacobson O := RingPrimeElement.mem_jacobson π
  induction k generalizing i v with
  | zero => simpa using hv
  | succ k ih =>
    rw [pow_succ, mul_smul, algebraMap_smul]
    have h : π.1 • v ∈ C.lattice (i + C.period) := by
      rw [C.lattice_add_period]
      exact Submodule.smul_mem_smul hJ hv
    have h' := ih h
    rwa [show i + C.period + k * C.period = i + ((k + 1 : ℕ) : ℤ) * C.period by
      push_cast; ring] at h'

theorem primeElement_smul_mem_endFiltration (C : LatticeChain O K V) (π : RingPrimeElement O)
    (k : ℕ) {x : Module.End K V} {s : ℤ} (hx : x ∈ C.endFiltration s) :
    (algebraMap O K π.1) ^ k • x ∈ C.endFiltration (s + k * C.period) := by
  intro i v hv
  rw [LinearMap.smul_apply, show i + (s + k * C.period) = i + s + k * C.period by ring]
  exact primeElement_smul_mem C π k (hx i v hv)

/-- The exponents of `y_b` cancel: `e/g · (−n) + n/g · e = 0` for `g = gcd(e,n)`. -/
theorem fundamental_shift_zero (e : ℕ) (n : ℤ) (hn : 0 ≤ n) :
    ((e / Nat.gcd e n.natAbs : ℕ) : ℤ) * -n +
      ((n / (Nat.gcd e n.natAbs : ℤ)).toNat : ℤ) * e = 0 := by
  have hge : (Nat.gcd e n.natAbs : ℤ) ∣ e := by exact_mod_cast Nat.gcd_dvd_left e n.natAbs
  have hgn : (Nat.gcd e n.natAbs : ℤ) ∣ n := by
    rw [Int.natCast_dvd]
    exact Nat.gcd_dvd_right e n.natAbs
  have ha : 0 ≤ n / (Nat.gcd e n.natAbs : ℤ) := Int.ediv_nonneg hn (Int.natCast_nonneg _)
  rw [Int.toNat_of_nonneg ha, Int.natCast_div]
  generalize (Nat.gcd e n.natAbs : ℤ) = g at hge hgn ⊢
  obtain ⟨n', rfl⟩ := hgn
  obtain ⟨e', he'⟩ := hge
  rw [he']
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · rw [Int.mul_ediv_cancel_left _ hg, Int.mul_ediv_cancel_left _ hg]
    ring

/-- The power `π^{n/g}` of `y_b` written with a natural exponent. -/
theorem fundamentalElement_eq_pow (S : Stratum O K V) (π : RingPrimeElement O) (hn : 0 ≤ S.n) :
    S.fundamentalElement π =
      (algebraMap O K π.1) ^ (S.n / (Nat.gcd S.chain.period S.n.natAbs : ℤ)).toNat •
        S.b ^ (S.chain.period / Nat.gcd S.chain.period S.n.natAbs) := by
  have ha : 0 ≤ S.n / (Nat.gcd S.chain.period S.n.natAbs : ℤ) :=
    Int.ediv_nonneg hn (Int.natCast_nonneg _)
  change (algebraMap O K π.1 ^ (S.n / (Nat.gcd S.chain.period S.n.natAbs : ℤ))) • _ = _
  rw [← zpow_natCast, Int.toNat_of_nonneg ha]

/-- For `n ≥ 0` and `b ∈ 𝔓^{−n}`, the element `y_b` lies in the order. -/
theorem fundamentalElement_mem_order (S : Stratum O K V) (π : RingPrimeElement O)
    (hn : 0 ≤ S.n) (hb : S.b ∈ S.chain.endFiltration (-S.n)) :
    S.fundamentalElement π ∈ S.chain.order := by
  rw [fundamentalElement_eq_pow S π hn]
  have h := primeElement_smul_mem_endFiltration S.chain π
    (S.n / (Nat.gcd S.chain.period S.n.natAbs : ℤ)).toNat
    (S.chain.pow_mem_endFiltration_mul hb (S.chain.period / Nat.gcd S.chain.period S.n.natAbs))
  rwa [fundamental_shift_zero S.chain.period S.n hn] at h

/-- Congruent elements give congruent `y_b`. -/
theorem fundamentalElement_sub_mem (S T : Stratum O K V) (π : RingPrimeElement O)
    (hc : T.chain = S.chain) (hnT : T.n = S.n) (hn : 0 ≤ S.n)
    (hb : S.b ∈ S.chain.endFiltration (-S.n)) (hbT : T.b ∈ S.chain.endFiltration (-S.n))
    (hd : S.b - T.b ∈ S.chain.endFiltration (1 - S.n)) :
    S.fundamentalElement π - T.fundamentalElement π ∈ S.chain.endFiltration 1 := by
  have hT := fundamentalElement_eq_pow T π (hnT ▸ hn)
  rw [hc, hnT] at hT
  rw [fundamentalElement_eq_pow S π hn, hT, ← smul_sub]
  have hd' : S.b - T.b ∈ S.chain.endFiltration (-S.n + 1) := by
    rwa [show -S.n + 1 = 1 - S.n by ring]
  have h := primeElement_smul_mem_endFiltration S.chain π
    (S.n / (Nat.gcd S.chain.period S.n.natAbs : ℤ)).toNat
    (S.chain.pow_sub_pow_mem_endFiltration hb hbT hd'
      (S.chain.period / Nat.gcd S.chain.period S.n.natAbs))
  rwa [add_right_comm, fundamental_shift_zero S.chain.period S.n hn, zero_add] at h

end Stratum


/-! ### Residues through `𝔄/𝔓` -/

section Local

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]

/-- BK93 (2.3.2) for an endomorphism shifting the chain by `−k`: no element of
`g + 𝔓^{1−k}` is nilpotent. -/
theorem LatticeChain.not_isNilpotent_of_shift [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (L : LatticeChain 𝒪[F] F V)
    {g x : Module.End F V} {k : ℤ}
    (hg : ∀ i (v : V), g v ∈ L.lattice (i + -k) ↔ v ∈ L.lattice i)
    (hx : x - g ∈ L.endFiltration (-(k - 1))) : ¬ IsNilpotent x := by
  have hker : ∀ v, x v = 0 → v = 0 := by
    intro v hxv
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    obtain ⟨i₀, hi₀⟩ := L.exists_lattice_depth hϖ v
    have hstep : ∀ i, v ∈ L.lattice i → v ∈ L.lattice (i + 1) := by
      intro i hi
      have hd := hx i v hi
      have hb : g v ∈ L.lattice (i + 1 + -k) := by
        have heq : g v = -((x - g) v) := by
          rw [LinearMap.sub_apply, hxv, zero_sub, neg_neg]
        rw [heq, show i + 1 + -k = i + -(k - 1) by ring]
        exact neg_mem hd
      exact (hg (i + 1) v).mp hb
    have hall : ∀ n : ℕ, v ∈ L.lattice (i₀ + n) := by
      intro n
      induction n with
      | zero => simpa using hi₀
      | succ n ih =>
        have h := hstep _ ih
        rwa [Nat.cast_succ, ← add_assoc]
    apply L.lattice_eq_zero_of_forall
    intro j
    by_cases hj : j ≤ i₀
    · exact L.antitone hj hi₀
    · have h := hall (j - i₀).toNat
      rwa [show i₀ + ((j - i₀).toNat : ℤ) = j by omega] at h
  have hinj : Function.Injective x := by
    intro v w hvw
    have h := hker (v - w) (by rw [map_sub, hvw, sub_self])
    exact sub_eq_zero.mp h
  rintro ⟨n, hn⟩
  have := L.nontrivialSpace
  obtain ⟨v, hv0⟩ := exists_ne (0 : V)
  have h1 : (x ^ n) v = (x ^ n) 0 := by rw [hn]; rfl
  rw [Module.End.coe_pow] at h1
  exact hv0 (hinj.iterate n h1)

variable {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
  {O : Type uO} [CommRing O] [Algebra O E] [Module O V] [IsScalarTower O E V]
  {L : LatticeChain 𝒪[F] F V} {C : LatticeChain O E V}

/-- Restriction of scalars from the order of a chain over `E` with the same lattices,
followed by reduction modulo `𝔓`. -/
def residueRestrict (h : ∀ i, (C.lattice i : Set V) = L.lattice i) :
    C.order →+* L.order ⧸ L.firstFiltrationIdeal :=
  (Ideal.Quotient.mk L.firstFiltrationIdeal).comp
    { toFun := fun x => ⟨(x : Module.End E V).restrictScalars F, by
        rw [LatticeChain.mem_order_iff_mem_endFiltration,
          ← mem_endFiltration_restrictScalars h]
        exact x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

theorem residueRestrict_apply (h : ∀ i, (C.lattice i : Set V) = L.lattice i) (x : C.order) :
    residueRestrict h x = Ideal.Quotient.mk L.firstFiltrationIdeal
      ⟨(x : Module.End E V).restrictScalars F, by
        rw [LatticeChain.mem_order_iff_mem_endFiltration,
          ← mem_endFiltration_restrictScalars h]
        exact x.2⟩ := rfl

theorem residueRestrict_eq_zero_iff (h : ∀ i, (C.lattice i : Set V) = L.lattice i)
    (x : C.order) : residueRestrict h x = 0 ↔ x ∈ C.firstFiltrationIdeal := by
  rw [residueRestrict_apply, Ideal.Quotient.eq_zero_iff_mem]
  change (x : Module.End E V).restrictScalars F ∈ L.endFiltration 1 ↔
    (x : Module.End E V) ∈ C.endFiltration 1
  rw [mem_endFiltration_restrictScalars h]

theorem residueRestrict_eq_iff (h : ∀ i, (C.lattice i : Set V) = L.lattice i)
    (x : C.order) (y : L.order) :
    residueRestrict h x = Ideal.Quotient.mk L.firstFiltrationIdeal y ↔
      (x : Module.End E V).restrictScalars F - (y : Module.End F V) ∈ L.endFiltration 1 := by
  rw [residueRestrict_apply, Ideal.Quotient.eq]
  rfl

/-- The injective map `𝔅/𝔔 → 𝔄/𝔓` induced by restriction of scalars. -/
def residueQuotientMap (h : ∀ i, (C.lattice i : Set V) = L.lattice i) :
    C.order ⧸ C.firstFiltrationIdeal →+* L.order ⧸ L.firstFiltrationIdeal :=
  Ideal.Quotient.lift C.firstFiltrationIdeal (residueRestrict h)
    (fun x hx => (residueRestrict_eq_zero_iff h x).mpr hx)

theorem residueQuotientMap_mk (h : ∀ i, (C.lattice i : Set V) = L.lattice i) (x : C.order) :
    residueQuotientMap h (Ideal.Quotient.mk C.firstFiltrationIdeal x) = residueRestrict h x :=
  rfl

theorem residueQuotientMap_injective (h : ∀ i, (C.lattice i : Set V) = L.lattice i) :
    Function.Injective (residueQuotientMap h) := by
  intro z w hzw
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
  rw [residueQuotientMap_mk, residueQuotientMap_mk] at hzw
  rw [Ideal.Quotient.eq, ← residueRestrict_eq_zero_iff h, RingHom.map_sub, hzw, sub_self]

end Local

/-! ### Residue centralizers of two derived strata -/

section Centralizer

universe uO₂ uE₂

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]
  {L : LatticeChain 𝒪[F] F V}
  {E₁ : Type uE} [Field E₁] [Algebra F E₁] [Module E₁ V] [IsScalarTower F E₁ V]
  {O₁ : Type uO} [CommRing O₁] [Algebra O₁ E₁] [Module O₁ V] [IsScalarTower O₁ E₁ V]
  {E₂ : Type uE₂} [Field E₂] [Algebra F E₂] [Module E₂ V] [IsScalarTower F E₂ V]
  {O₂ : Type uO₂} [CommRing O₂] [Algebra O₂ E₂] [Module O₂ V] [IsScalarTower O₂ E₂ V]

/-- If the orders and the elements of two strata agree modulo `𝔓` and `𝔓^{1−n}`, then every
residue class centralizing the first symbol is the image of one centralizing the second. -/
theorem residueCentralizer_map_le (D₁ : Stratum O₁ E₁ V) (D₂ : Stratum O₂ E₂ V)
    (h₁ : ∀ i, (D₁.chain.lattice i : Set V) = L.lattice i)
    (h₂ : ∀ i, (D₂.chain.lattice i : Set V) = L.lattice i) (hn : D₂.n = D₁.n)
    (hb₁ : D₁.b ∈ D₁.chain.endFiltration (-D₁.n)) (hb₂ : D₂.b ∈ D₂.chain.endFiltration (-D₂.n))
    (hcong : D₁.b.restrictScalars F - D₂.b.restrictScalars F ∈ L.endFiltration (1 - D₁.n))
    (hA : ∀ x : D₁.chain.order, ∃ y : D₂.chain.order,
      (x : Module.End E₁ V).restrictScalars F - (y : Module.End E₂ V).restrictScalars F ∈
        L.endFiltration 1) :
    D₁.residueCentralizer.toSubring.map (residueQuotientMap h₁) ≤
      D₂.residueCentralizer.toSubring.map (residueQuotientMap h₂) := by
  rintro q ⟨z, hz, rfl⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hx := (Stratum.mk_mem_residueCentralizer_iff D₁ hb₁ x).mp hz
  rw [mem_endFiltration_restrictScalars h₁] at hx
  obtain ⟨y, hxy⟩ := hA x
  set X := (x : Module.End E₁ V).restrictScalars F
  set Y := (y : Module.End E₂ V).restrictScalars F
  set B₁ := D₁.b.restrictScalars F
  set B₂ := D₂.b.restrictScalars F
  have hX : (adjointMap O₁ D₁.b (x : Module.End E₁ V)).restrictScalars F = B₁ * X - X * B₁ := rfl
  have hY : (adjointMap O₂ D₂.b (y : Module.End E₂ V)).restrictScalars F = B₂ * Y - Y * B₂ := rfl
  have hB₁ : B₁ ∈ L.endFiltration (-D₁.n) := (mem_endFiltration_restrictScalars h₁).mp hb₁
  have hYo : Y ∈ L.endFiltration 0 := (mem_endFiltration_restrictScalars h₂).mp y.2
  refine ⟨Ideal.Quotient.mk _ y, ?_, ?_⟩
  · change Ideal.Quotient.mk _ y ∈ D₂.residueCentralizer
    rw [Stratum.mk_mem_residueCentralizer_iff D₂ hb₂ y, mem_endFiltration_restrictScalars h₂, hY,
      hn]
    rw [hX] at hx
    rw [show B₂ * Y - Y * B₂ = (B₁ * X - X * B₁) - B₁ * (X - Y) + (X - Y) * B₁ -
        (B₁ - B₂) * Y + Y * (B₁ - B₂) by noncomm_ring]
    refine add_mem (sub_mem (add_mem (sub_mem hx ?_) ?_) ?_) ?_
    · have h := L.mul_mem_endFiltration hB₁ hxy
      rwa [show -D₁.n + 1 = 1 - D₁.n by ring] at h
    · have h := L.mul_mem_endFiltration hxy hB₁
      rwa [show 1 + -D₁.n = 1 - D₁.n by ring] at h
    · have h := L.mul_mem_endFiltration hcong hYo
      rwa [add_zero] at h
    · have h := L.mul_mem_endFiltration hYo hcong
      rwa [zero_add] at h
  · change residueQuotientMap h₂ (Ideal.Quotient.mk _ y) =
      residueQuotientMap h₁ (Ideal.Quotient.mk _ x)
    rw [residueQuotientMap_mk, residueQuotientMap_mk, residueRestrict_apply, residueRestrict_apply,
      Ideal.Quotient.eq]
    change Y - X ∈ L.endFiltration 1
    rw [← neg_sub]
    exact neg_mem hxy

/-- A subalgebra and its underlying subring are isomorphic rings. -/
def subalgebraToSubringEquiv {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) : S ≃+* S.toSubring where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

set_option maxHeartbeats 1600000 in
/-- Equal images of the residue centralizers in `𝔄/𝔓` transfer semisimplicity. -/
theorem isSemisimpleRing_residueCentralizer_of_map_eq (D₁ : Stratum O₁ E₁ V)
    (D₂ : Stratum O₂ E₂ V) (h₁ : ∀ i, (D₁.chain.lattice i : Set V) = L.lattice i)
    (h₂ : ∀ i, (D₂.chain.lattice i : Set V) = L.lattice i)
    (heq : D₁.residueCentralizer.toSubring.map (residueQuotientMap h₁) =
      D₂.residueCentralizer.toSubring.map (residueQuotientMap h₂))
    (hs : IsSemisimpleRing D₁.residueCentralizer) : IsSemisimpleRing D₂.residueCentralizer := by
  let j₁ : D₁.chain.order ⧸ D₁.chain.firstFiltrationIdeal →+* L.order ⧸ L.firstFiltrationIdeal :=
    residueQuotientMap h₁
  let j₂ : D₂.chain.order ⧸ D₂.chain.firstFiltrationIdeal →+* L.order ⧸ L.firstFiltrationIdeal :=
    residueQuotientMap h₂
  let e₁ := Subring.equivMapOfInjective D₁.residueCentralizer.toSubring j₁
    (residueQuotientMap_injective h₁)
  let e₂ := Subring.equivMapOfInjective D₂.residueCentralizer.toSubring j₂
    (residueQuotientMap_injective h₂)
  have heq' : Subring.map j₁ D₁.residueCentralizer.toSubring =
      Subring.map j₂ D₂.residueCentralizer.toSubring := heq
  let e : D₁.residueCentralizer.toSubring ≃+* D₂.residueCentralizer.toSubring :=
    (e₁.trans (RingEquiv.subringCongr heq')).trans e₂.symm
  have hs₁ : IsSemisimpleRing D₁.residueCentralizer.toSubring :=
    (subalgebraToSubringEquiv D₁.residueCentralizer).isSemisimpleRing
  have hs₂ : IsSemisimpleRing D₂.residueCentralizer.toSubring := e.isSemisimpleRing
  exact (subalgebraToSubringEquiv D₂.residueCentralizer).symm.isSemisimpleRing

end Centralizer

end Langlands.BushnellKutzko
