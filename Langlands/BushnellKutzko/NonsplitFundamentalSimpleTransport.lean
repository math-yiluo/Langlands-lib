import Langlands.BushnellKutzko.NonsplitFundamentalSimpleStatement

/-! # Changing the integer ring of a stratum

Let `O₁ ≃+* O₂` be an isomorphism of commutative rings compatible with algebra maps to a field
`K`. Lattices, lattice chains and strata over `O₁` in a `K`-vector space `V` become lattices,
lattice chains and strata over `O₂` with the same vectors (`transportSubmodule`,
`transportChain`, `transportStratum`). Cosets, normalizers, valuations, critical exponents,
simplicity and the nonsplit fundamental condition are preserved, and the residue centralizers
are isomorphic rings. Consequently the criterion `Stratum.NonsplitSimpleCriterion` for the
transported stratum gives it for the original one (`nonsplitSimpleCriterion_of_transport`).
-/

noncomputable section

namespace Langlands.BushnellKutzko.NonsplitSimple

open LatticeChain

universe u₁ u₂ uK uV

variable {O₁ : Type u₁} {O₂ : Type u₂} {K : Type uK} {V : Type uV} [CommRing O₁] [CommRing O₂]
  [Field K] [Algebra O₁ K] [Algebra O₂ K] [AddCommGroup V] [Module K V] [Module O₁ V]
  [Module O₂ V] [IsScalarTower O₁ K V] [IsScalarTower O₂ K V]
  (φ : O₁ ≃+* O₂) (hφ : ∀ a, algebraMap O₂ K (φ a) = algebraMap O₁ K a)

include hφ in
/-- The two integer rings act on `V` through the same scalars of `K`. -/
theorem transport_smul (a : O₁) (v : V) : φ a • v = a • v := by
  rw [← algebraMap_smul K (φ a) v, hφ, algebraMap_smul]

include hφ in
/-- The inverse isomorphism is also compatible with the maps to `K`. -/
theorem transport_symm (a : O₂) : algebraMap O₁ K (φ.symm a) = algebraMap O₂ K a := by
  rw [← hφ, φ.apply_symm_apply]

omit [Algebra O₁ K] [Algebra O₂ K] in
/-- A ring isomorphism matches the Jacobson radicals. -/
theorem transport_mem_jacobson_iff (a : O₁) :
    φ a ∈ Ring.jacobson O₂ ↔ a ∈ Ring.jacobson O₁ := by
  rw [← Ideal.jacobson_bot, ← Ideal.jacobson_bot, Ideal.mem_jacobson_bot, Ideal.mem_jacobson_bot]
  constructor
  · intro h y
    have := h (φ y)
    rw [← map_mul, ← map_one φ, ← map_add] at this
    exact (isUnit_map_iff φ _).mp this
  · intro h y
    obtain ⟨y, rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_one φ, ← map_add]
    exact (h y).map φ

/-- An `O₁`-submodule of `V` as an `O₂`-submodule with the same vectors. -/
def transportSubmodule (M : Submodule O₁ V) : Submodule O₂ V where
  carrier := M
  add_mem' := M.add_mem
  zero_mem' := M.zero_mem
  smul_mem' a v hv := by
    rw [← φ.apply_symm_apply a, transport_smul φ hφ]
    exact M.smul_mem _ hv

@[simp] theorem mem_transportSubmodule {M : Submodule O₁ V} {v : V} :
    v ∈ transportSubmodule φ hφ M ↔ v ∈ M := Iff.rfl

@[simp] theorem coe_transportSubmodule (M : Submodule O₁ V) :
    (transportSubmodule φ hφ M : Set V) = M := rfl

theorem transportSubmodule_le_iff {M N : Submodule O₁ V} :
    transportSubmodule φ hφ M ≤ transportSubmodule φ hφ N ↔ M ≤ N := Iff.rfl

theorem transportSubmodule_lt_iff {M N : Submodule O₁ V} :
    transportSubmodule φ hφ M < transportSubmodule φ hφ N ↔ M < N := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, transportSubmodule_le_iff, transportSubmodule_le_iff]

/-- Spans over the two integer rings coincide. -/
theorem transportSubmodule_span (s : Set V) :
    transportSubmodule φ hφ (Submodule.span O₁ s) = Submodule.span O₂ s := by
  apply le_antisymm
  · intro v hv
    change v ∈ Submodule.span O₁ s at hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx =>
      rw [← transport_smul φ hφ]
      exact Submodule.smul_mem _ _ hx
  · rw [Submodule.span_le]
    intro v hv
    exact Submodule.subset_span hv

/-- Finite generation is preserved. -/
theorem transportSubmodule_fg {M : Submodule O₁ V} (h : M.FG) :
    (transportSubmodule φ hφ M).FG := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, by rw [← transportSubmodule_span φ hφ, hs]⟩

/-- Multiplication by the Jacobson radical is preserved. -/
theorem transportSubmodule_jacobson_smul (M : Submodule O₁ V) :
    transportSubmodule φ hφ (Ring.jacobson O₁ • M) =
      Ring.jacobson O₂ • transportSubmodule φ hφ M := by
  apply le_antisymm
  · intro v hv
    change v ∈ Ring.jacobson O₁ • M at hv
    refine Submodule.smul_induction_on hv ?_ ?_
    · intro a ha m hm
      rw [← transport_smul φ hφ]
      exact Submodule.smul_mem_smul ((transport_mem_jacobson_iff φ a).mpr ha) hm
    · intro x y hx hy
      exact add_mem hx hy
  · rw [Submodule.smul_le]
    intro a ha m hm
    obtain ⟨a, rfl⟩ := φ.surjective a
    change φ a • m ∈ Ring.jacobson O₁ • M
    rw [transport_smul φ hφ]
    exact Submodule.smul_mem_smul ((transport_mem_jacobson_iff φ a).mp ha) hm

/-- A lattice chain over `O₁` as a lattice chain over `O₂`, with the same lattices. -/
def transportChain (𝓛 : LatticeChain O₁ K V) : LatticeChain O₂ K V where
  lattice i := transportSubmodule φ hφ (𝓛.lattice i)
  isLattice i := ⟨transportSubmodule_fg φ hφ (𝓛.isLattice i).fg, (𝓛.isLattice i).span_eq_top⟩
  lattice_succ_lt i := (transportSubmodule_lt_iff φ hφ).mpr (𝓛.lattice_succ_lt i)
  exists_period := ⟨𝓛.period, 𝓛.period_pos, fun i => by
    rw [𝓛.lattice_add_period, transportSubmodule_jacobson_smul]⟩

variable (𝓛 : LatticeChain O₁ K V)

@[simp] theorem transportChain_lattice (i : ℤ) :
    (transportChain φ hφ 𝓛).lattice i = transportSubmodule φ hφ (𝓛.lattice i) := rfl

/-- The filtration lattices `𝔓^n` have the same elements. -/
theorem transportChain_mem_endFiltration {x : Module.End K V} {n : ℤ} :
    x ∈ (transportChain φ hφ 𝓛).endFiltration n ↔ x ∈ 𝓛.endFiltration n := Iff.rfl

/-- The two chains have the same period. -/
theorem transportChain_period : (transportChain φ hφ 𝓛).period = 𝓛.period := by
  refine ((transportChain φ hφ 𝓛).period_unique (e := 𝓛.period) fun i => ?_).symm
  change transportSubmodule φ hφ (𝓛.lattice (i + 𝓛.period)) = _
  rw [𝓛.lattice_add_period, transportSubmodule_jacobson_smul]
  rfl

/-- The two chains define the same valuation on `End_K(V)`. -/
theorem transportChain_valuation (x : Module.End K V) :
    (transportChain φ hφ 𝓛).valuation x = 𝓛.valuation x := rfl

/-- The two chains have the same normalizer. -/
theorem transportChain_mem_stabilizer {g : (Module.End K V)ˣ} :
    g ∈ (transportChain φ hφ 𝓛).stabilizer ↔ g ∈ 𝓛.stabilizer := by
  rw [mem_stabilizer, mem_stabilizer]
  refine forall_congr' fun i => exists_congr fun j => ?_
  constructor <;> intro h <;> apply SetLike.coe_injective <;>
    simpa only [Submodule.map_coe, LinearMap.coe_restrictScalars, transportChain_lattice,
      coe_transportSubmodule] using congrArg SetLike.coe h

/-- The adjoint map does not depend on the integer ring. -/
theorem adjointMap_apply' {O : Type*} [CommRing O] [Algebra O K] [Module O V]
    [IsScalarTower O K V] (β x : Module.End K V) : adjointMap O β x = β * x - x * β :=
  rfl

/-- The two chains give the same critical exponent. -/
theorem transportChain_criticalExponent (β : Module.End K V) :
    criticalExponent (transportChain φ hφ 𝓛) β = criticalExponent 𝓛 β := by
  have hset : criticalIndexSet (transportChain φ hφ 𝓛) β = criticalIndexSet 𝓛 β := by
    ext k
    simp only [criticalIndexSet, Set.mem_ofPred_eq, IsConcreteLE.le_iff, adjointLattice,
      centralizerLattice, Submodule.mem_inf, Submodule.mem_comap, LinearMap.mem_ker,
      Submodule.mem_sup, adjointMap_apply', transportChain_mem_endFiltration]
  simp only [criticalExponent, hset]

/-- A stratum over `O₁` as a stratum over `O₂`. -/
def transportStratum (S : Stratum O₁ K V) : Stratum O₂ K V :=
  ⟨transportChain φ hφ S.chain, S.n, S.r, S.b, S.r_lt_n, S.valuation_ge⟩

variable (S : Stratum O₁ K V)

/-- A stratum and its transport have the same coset. -/
theorem transportStratum_coset : (transportStratum φ hφ S).coset = S.coset := rfl

theorem transportStratum_isFundamental :
    (transportStratum φ hφ S).IsFundamental ↔ S.IsFundamental := Iff.rfl

/-- Simplicity does not depend on the integer ring. -/
theorem transportStratum_isSimple : (transportStratum φ hφ S).IsSimple ↔ S.IsSimple := by
  unfold Stratum.IsSimple Stratum.IsPure
  change ((∃ h : IsField (elementAlgebra S.b),
    letI := h.toField
    ∀ a : (elementAlgebra S.b)ˣ,
      subfieldUnits K (elementAlgebra S.b) V a ∈ (transportChain φ hφ S.chain).stabilizer) ∧
    (transportChain φ hφ S.chain).valuation S.b = (-S.n : WithTop ℤ)) ∧
    criticalExponent (transportChain φ hφ S.chain) S.b < ((-S.r : ℤ) : WithBot ℤ) ↔ _
  simp only [transportChain_mem_stabilizer, transportChain_valuation,
    transportChain_criticalExponent]

omit [Algebra O₁ K] [Algebra O₂ K] in
/-- The Jacobson radical of `O₂` is the image of that of `O₁`. -/
theorem jacobson_eq_map : Ring.jacobson O₂ = (Ring.jacobson O₁).map (φ : O₁ →+* O₂) := by
  rw [Ideal.map_comap_of_equiv]
  ext a
  rw [Ideal.mem_comap, ← transport_mem_jacobson_iff φ, RingEquiv.apply_symm_apply]

/-- The induced isomorphism of residue rings. -/
def residueRingEquiv : O₁ ⧸ Ring.jacobson O₁ ≃+* O₂ ⧸ Ring.jacobson O₂ :=
  Ideal.quotientEquiv _ _ φ (jacobson_eq_map φ)

theorem residueRingEquiv_mk (a : O₁) :
    residueRingEquiv φ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (φ a) := rfl

include hφ in
/-- Coefficientwise reduction commutes with the change of integer ring. -/
theorem transport_reduceIntegralPolynomial (hinj : Function.Injective (algebraMap O₂ K))
    (p : Polynomial K) :
    reduceIntegralPolynomial O₂ K p =
      (reduceIntegralPolynomial O₁ K p).map (residueRingEquiv φ) := by
  classical
  unfold reduceIntegralPolynomial
  rw [← Polynomial.coe_mapRingHom, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.coe_mapRingHom, Polynomial.map_monomial]
  congr 1
  by_cases h₁ : ∃ a : O₁, algebraMap O₁ K a = p.coeff i
  · have h₂ : ∃ a : O₂, algebraMap O₂ K a = p.coeff i := ⟨φ h₁.choose, by rw [hφ, h₁.choose_spec]⟩
    rw [dite_eq_left h₂, dite_eq_left h₁, RingEquiv.coe_toRingHom, residueRingEquiv_mk]
    congr 1
    exact hinj (by rw [h₂.choose_spec, hφ, h₁.choose_spec])
  · have h₂ : ¬ ∃ a : O₂, algebraMap O₂ K a = p.coeff i := fun ⟨a, ha⟩ =>
      h₁ ⟨φ.symm a, by rw [transport_symm φ hφ, ha]⟩
    rw [dite_eq_right h₂, dite_eq_right h₁, map_zero]

/-- A nonsplit fundamental stratum stays nonsplit fundamental. -/
theorem transportStratum_isNonsplit (hinj : Function.Injective (algebraMap O₂ K))
    (h : S.IsNonsplit) : (transportStratum φ hφ S).IsNonsplit := by
  obtain ⟨hfund, π, p, m, hpm, hpi, hm, hφp⟩ := h
  have hspan : Ideal.span ({φ π.1} : Set O₂) = Ring.jacobson O₂ := by
    have h := congrArg (Ideal.map (φ : O₁ →+* O₂)) π.2.2
    rw [Ideal.map_span, Set.image_singleton] at h
    rw [jacobson_eq_map φ, ← h]
    rfl
  let π' : RingPrimeElement O₂ := ⟨φ π.1, (map_ne_zero_iff φ φ.injective).mpr π.2.1, hspan⟩
  let ψ : O₁ ⧸ Ring.jacobson O₁ →+* O₂ ⧸ Ring.jacobson O₂ := residueRingEquiv φ
  have hirr : Irreducible (p.map ψ) :=
    (MulEquiv.irreducible_iff (Polynomial.mapEquiv (residueRingEquiv φ)).toMulEquiv).mpr hpi
  refine ⟨(transportStratum_isFundamental φ hφ S).mpr hfund, π', p.map ψ, m, hpm.map _, hirr,
    hm, ?_⟩
  have hel : (transportStratum φ hφ S).fundamentalElement π' = S.fundamentalElement π := by
    simp only [Stratum.fundamentalElement]
    rw [show (transportStratum φ hφ S).chain.period = S.chain.period from
      transportChain_period φ hφ S.chain]
    change (algebraMap O₂ K (φ π.1) ^ _) • S.b ^ _ = _
    rw [hφ]
    rfl
  unfold Stratum.fundamentalPolynomial
  rw [hel, transport_reduceIntegralPolynomial φ hφ hinj]
  change (S.fundamentalPolynomial π).map _ = _
  rw [hφp, Polynomial.map_pow]

theorem transportSubmodule_symm (M : Submodule O₁ V) :
    transportSubmodule φ.symm (transport_symm φ hφ) (transportSubmodule φ hφ M) = M := by
  ext v
  rfl

/-- Transporting back recovers the original chain. -/
theorem transportChain_symm :
    transportChain φ.symm (transport_symm φ hφ) (transportChain φ hφ 𝓛) = 𝓛 := by
  obtain ⟨L, h₁, h₂, h₃⟩ := 𝓛
  simp only [transportChain, LatticeChain.mk.injEq]
  funext i
  exact transportSubmodule_symm φ hφ (L i)

/-- The orders of the two chains coincide as rings. -/
def transportOrderEquiv : 𝓛.order ≃+* (transportChain φ hφ 𝓛).order where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem transport_firstFiltrationIdeal :
    (transportChain φ hφ 𝓛).firstFiltrationIdeal =
      𝓛.firstFiltrationIdeal.map (transportOrderEquiv φ hφ 𝓛 : 𝓛.order →+* _) := by
  rw [Ideal.map_comap_of_equiv]
  rfl

/-- The rings `𝔄/𝔓` of the two chains coincide. -/
def transportResidueEquiv :
    𝓛.order ⧸ 𝓛.firstFiltrationIdeal ≃+*
      (transportChain φ hφ 𝓛).order ⧸ (transportChain φ hφ 𝓛).firstFiltrationIdeal :=
  Ideal.quotientEquiv _ _ (transportOrderEquiv φ hφ 𝓛) (transport_firstFiltrationIdeal φ hφ 𝓛)

theorem transportResidueEquiv_mk (x : 𝓛.order) :
    transportResidueEquiv φ hφ 𝓛 (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (transportOrderEquiv φ hφ 𝓛 x) := rfl

theorem transportResidueEquiv_symm_mk (x : (transportChain φ hφ 𝓛).order) :
    (transportResidueEquiv φ hφ 𝓛).symm (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ ((transportOrderEquiv φ hφ 𝓛).symm x) := rfl

/-- The rings `𝔄/𝔓` of a stratum and of its transport. -/
def transportStratumResidueEquiv :
    S.chain.order ⧸ S.chain.firstFiltrationIdeal ≃+*
      (transportStratum φ hφ S).chain.order ⧸
        (transportStratum φ hφ S).chain.firstFiltrationIdeal :=
  transportResidueEquiv φ hφ S.chain

/-- The isomorphism of the rings `𝔄/𝔓` matches the residue centralizers. -/
theorem mem_transport_residueCentralizer_iff (hb : S.b ∈ S.chain.endFiltration (-S.n))
    (x : S.chain.order ⧸ S.chain.firstFiltrationIdeal) :
    transportStratumResidueEquiv φ hφ S x ∈ (transportStratum φ hφ S).residueCentralizer ↔
      x ∈ S.residueCentralizer := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hb' : (transportStratum φ hφ S).b ∈
      (transportStratum φ hφ S).chain.endFiltration (-(transportStratum φ hφ S).n) := hb
  change Ideal.Quotient.mk (transportStratum φ hφ S).chain.firstFiltrationIdeal
      (⟨(x : Module.End K V), x.2⟩ : (transportStratum φ hφ S).chain.order) ∈
        (transportStratum φ hφ S).residueCentralizer ↔ _
  rw [Stratum.mk_mem_residueCentralizer_iff _ hb', Stratum.mk_mem_residueCentralizer_iff _ hb]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
/-- The residue centralizers of the two presentations are isomorphic rings. -/
def transportResidueCentralizerEquiv (hb : S.b ∈ S.chain.endFiltration (-S.n)) :
    S.residueCentralizer ≃+* (transportStratum φ hφ S).residueCentralizer where
  toFun x := ⟨transportStratumResidueEquiv φ hφ S x.1,
    (mem_transport_residueCentralizer_iff φ hφ S hb x.1).mpr x.2⟩
  invFun y := ⟨(transportStratumResidueEquiv φ hφ S).symm y.1, by
    rw [← mem_transport_residueCentralizer_iff φ hφ S hb, RingEquiv.apply_symm_apply]
    exact y.2⟩
  left_inv x := Subtype.ext ((transportStratumResidueEquiv φ hφ S).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((transportStratumResidueEquiv φ hφ S).apply_symm_apply y.1)
  map_mul' x y := Subtype.ext (map_mul (transportStratumResidueEquiv φ hφ S) x.1 y.1)
  map_add' x y := Subtype.ext (map_add (transportStratumResidueEquiv φ hφ S) x.1 y.1)

/-- The criterion transfers from the `O₂` presentation of a stratum to its `O₁` presentation. -/
theorem nonsplitSimpleCriterion_of_transport (hinj : Function.Injective (algebraMap O₂ K))
    (hb : S.b ∈ S.chain.endFiltration (-S.n))
    (h : (transportStratum φ hφ S).NonsplitSimpleCriterion) : S.NonsplitSimpleCriterion := by
  intro hn hS
  have key := h hn (transportStratum_isNonsplit φ hφ S hinj hS)
  rw [(transportResidueCentralizerEquiv φ hφ S hb).isSemisimpleRing_iff, ← key]
  constructor
  · rintro ⟨T, hTc, hTn, hTr, hST, hT⟩
    refine ⟨transportStratum φ hφ T, ?_, hTn, hTr, ?_, (transportStratum_isSimple φ hφ T).mpr hT⟩
    · change transportChain φ hφ T.chain = transportChain φ hφ S.chain
      rw [hTc]
    · change (transportStratum φ hφ S).coset = (transportStratum φ hφ T).coset
      rw [transportStratum_coset, transportStratum_coset]
      exact hST
  · rintro ⟨T, hTc, hTn, hTr, hST, hT⟩
    have hφ' := transport_symm φ hφ
    refine ⟨transportStratum φ.symm hφ' T, ?_, hTn, hTr, ?_,
      (transportStratum_isSimple φ.symm hφ' T).mpr hT⟩
    · change transportChain φ.symm hφ' T.chain = S.chain
      rw [hTc]
      exact transportChain_symm φ hφ S.chain
    · change S.coset = (transportStratum φ.symm hφ' T).coset
      rw [transportStratum_coset]
      exact hST

end Langlands.BushnellKutzko.NonsplitSimple
