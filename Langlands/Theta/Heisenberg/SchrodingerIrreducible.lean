import Langlands.Theta.Heisenberg.InducedModel
import Langlands.Theta.Heisenberg.Schrodinger
import Langlands.HarmonicAnalysis.Bicharacter.Fourier
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# The Schrödinger model is smooth, irreducible and admissible

GKT §1.2.2 (Theorem 1.13, p. 25) and Proposition 1.29 (p. 35). Let `F` be a nonarchimedean local
field with `2` invertible, `X`, `Y` finite-dimensional `F`-vector spaces with their module
topologies, `β : X × Y → F` a perfect pairing and `ψ` a continuous non-trivial character of `F`.
The Schrödinger representation `schrodingerSB ψ β` of the Heisenberg group of
`polarizedForm β` on the Schwartz–Bruhat functions on `X` is

* smooth (`isSmooth_schrodingerSB`; perfectness is not needed),
* irreducible (`isIrreducible_schrodingerSB`),
* admissible (`isAdmissible_schrodingerSB`).

So it is a model of the Heisenberg representation with central character `ψ`
(GKT Definition 1.14), isomorphic to every other one by the Stone–von Neumann theorem.

The proof is not the book's (which identifies the model with the induced model of the Lagrangian
`X`, Theorem 1.13). It uses the self-dual subgroups `A = L × M` of `X × Y` with `M = L^⊥` and
`L = M^⊥` for the pairing `ψ ∘ β`, for which the indicator `1_L` is an eigenvector of the operators
of `A` with eigenvalue `(l, m) ↦ ψ(½ β(l, m))`, and the only one up to a scalar; such pairs exist
(take `M = L₀^⊥`, `L = M^⊥` for a compact open subgroup `L₀`: then `L^⊥ = L₀^⊥⊥⊥ = M`). Every
non-zero subrepresentation contains an eigenvector of every scaled subgroup `tL × t⁻¹M`
(`SelfDualDatum.exists_eigenvector_mem`), hence all the indicators `1_{tL}`, hence everything,
since a Schwartz–Bruhat function is a finite combination of translates of `1_{tL}` for `t`
small. Admissibility: a vector fixed by `tL × tM` is `tL`-invariant and supported in `t⁻¹L`.
-/

noncomputable section

open Filter Topology ValuativeRel

namespace Langlands.HeisenbergGroup

open Langlands.HarmonicAnalysis

universe u v w

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

namespace SchrodingerIrreducible.Internal

/-- A continuous additive character of a nonarchimedean local field is unitary: its values on
`𝒪 t` form a bounded set containing all the powers `ψ(t)^n`, `n ∈ ℤ`. -/
theorem norm_addChar_eq_one {ψ : AddChar F ℂ} (hψ : Continuous ψ) (t : F) : ‖ψ t‖ = 1 := by
  have hK : IsCompact ((fun o : F => ψ (o * t)) '' (𝒪[F] : Set F)) :=
    (IsNonarchimedeanLocalField.isCompact_closedBall F 1).image (by fun_prop)
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  have hpow : ∀ n : ℤ, ‖ψ t‖ ^ n ≤ C := fun n => by
    have e : ψ ((n : F) * t) = ψ t ^ n := by
      rw [← zsmul_eq_mul, AddChar.map_zsmul_eq_zpow]
    rw [← norm_zpow, ← e]
    exact hC _ ⟨n, intCast_mem _ n, rfl⟩
  have h0 : ψ t ≠ 0 := fun h => by
    have := AddChar.map_add_eq_mul ψ t (-t)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
    exact one_ne_zero this
  have hpos : 0 < ‖ψ t‖ := norm_pos_iff.2 h0
  rcases lt_trichotomy ‖ψ t‖ 1 with h | h | h
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (one_lt_inv₀ hpos |>.2 h)
    have := hpow (-(n : ℤ))
    rw [zpow_neg, zpow_natCast, ← inv_pow] at this
    exact absurd this (not_le.2 hn)
  · exact h
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
    have := hpow n
    rw [zpow_natCast] at this
    exact absurd this (not_le.2 hn)

/-- A continuous additive character is `1` near `0`. -/
theorem eventually_addChar_eq_one {ψ : AddChar F ℂ} (hψ : Continuous ψ) :
    ∀ᶠ t in 𝓝 (0 : F), ψ t = 1 := by
  filter_upwards [(isLocallyConstant_of_continuous_addChar ψ hψ).eventually_eq 0] with t ht
  rw [ht, AddChar.map_zero_eq_one]

/-- Some non-zero scalar satisfies an eventual property at `0`. -/
theorem exists_ne_zero_of_eventually {p : F → Prop} (hp : ∀ᶠ r in 𝓝 (0 : F), p r) :
    ∃ r, r ≠ 0 ∧ p r := by
  obtain ⟨γ, hγ, hs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.1 hp
  obtain ⟨y, rfl⟩ := ValuativeRel.valuation_surjective γ
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation F)
  refine ⟨y * r, mul_ne_zero (by simpa using hγ) hr, hs ?_⟩
  show ValuativeRel.valuation F (y * r) < ValuativeRel.valuation F y
  rw [map_mul]
  exact mul_lt_of_lt_one_right (zero_lt_iff.2 hγ) hr1

/-- A compact set of an additive group is finite modulo an open subgroup. -/
theorem finite_image_quotient {W : Type*} [AddCommGroup W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] (U : AddSubgroup W) (hU : IsOpen (U : Set W)) {K : Set W}
    (hK : IsCompact K) : ((QuotientAddGroup.mk : W → W ⧸ U) '' K).Finite := by
  have := QuotientAddGroup.discreteTopology hU
  exact (hK.image QuotientAddGroup.continuous_mk).finite_of_discrete

section Algebra

variable {K : Type*} [Field K] {X : Type v} [AddCommGroup X] [Module K X] {Y : Type w}
  [AddCommGroup Y] [Module K Y] (β : X →ₗ[K] Y →ₗ[K] K) (ψ : AddChar K ℂ)

/-! ### Orthogonals for the pairing `ψ ∘ β` -/

/-- The orthogonal `{y | ψ(β(x, y)) = 1 for x ∈ T}` in `Y` of a set `T` of `X`. -/
def orthRight (T : Set X) : AddSubgroup Y where
  carrier := {y | ∀ x ∈ T, ψ (β x y) = 1}
  add_mem' {a b} ha hb x hx := by
    rw [map_add, AddChar.map_add_eq_mul, ha x hx, hb x hx, mul_one]
  zero_mem' x _ := by simp
  neg_mem' {a} ha x hx := by
    rw [map_neg, AddChar.map_neg_eq_inv, ha x hx, inv_one]

/-- The orthogonal `{x | ψ(β(x, y)) = 1 for y ∈ T}` in `X` of a set `T` of `Y`. -/
def orthLeft (T : Set Y) : AddSubgroup X where
  carrier := {x | ∀ y ∈ T, ψ (β x y) = 1}
  add_mem' {a b} ha hb y hy := by
    rw [map_add, LinearMap.add_apply, AddChar.map_add_eq_mul, ha y hy, hb y hy, mul_one]
  zero_mem' y _ := by simp
  neg_mem' {a} ha y hy := by
    rw [map_neg, LinearMap.neg_apply, AddChar.map_neg_eq_inv, ha y hy, inv_one]

variable {β ψ}

theorem mem_orthRight {T : Set X} {y : Y} : y ∈ orthRight β ψ T ↔ ∀ x ∈ T, ψ (β x y) = 1 :=
  Iff.rfl

theorem mem_orthLeft {T : Set Y} {x : X} : x ∈ orthLeft β ψ T ↔ ∀ y ∈ T, ψ (β x y) = 1 :=
  Iff.rfl

/-- `L^⊥⊥⊥ = L^⊥`. -/
theorem orthRight_orthLeft_orthRight (T : Set X) :
    orthRight β ψ (orthLeft β ψ (orthRight β ψ T)) = orthRight β ψ T := by
  ext y
  refine ⟨fun hy x hx => hy x fun y' hy' => hy' x hx, fun hy x hx => hx y hy⟩

/-- The symmetric form `((x, y), (x', y')) ↦ β(x, y') + β(x', y)` on `X × Y`. -/
def symmForm (β : X →ₗ[K] Y →ₗ[K] K) : (X × Y) →ₗ[K] (X × Y) →ₗ[K] K :=
  LinearMap.mk₂ K (fun v w => β v.1 w.2 + β w.1 v.2)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

theorem symmForm_apply (v w : X × Y) : symmForm β v w = β v.1 w.2 + β w.1 v.2 := rfl

end Algebra

variable {X : Type v} [AddCommGroup X] [Module F X] [FiniteDimensional F X] [TopologicalSpace X]
  [IsModuleTopology F X] {Y : Type w} [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y]
  [TopologicalSpace Y] [IsModuleTopology F Y] {β : X →ₗ[F] Y →ₗ[F] F} {ψ : AddChar F ℂ}

omit [FiniteDimensional F Y] in
/-- The orthogonal of a compact set is a neighbourhood of `0`. -/
theorem orthRight_mem_nhds (hψ : Continuous ψ) {K : Set X} (hK : IsCompact K) :
    (orthRight β ψ K : Set Y) ∈ 𝓝 0 := by
  have hc : Continuous fun z : Y × X => β z.2 z.1 :=
    (IsModuleTopology.continuous_bilinear_of_finite_left β).comp continuous_swap
  have := hK.eventually_forall_of_forall_eventually (x₀ := (0 : Y))
    (P := fun y x => ψ (β x y) = 1) fun x _ =>
      (hc.tendsto' ((0 : Y), x) 0 (by simp)).eventually (eventually_addChar_eq_one hψ)
  filter_upwards [this] with y hy using hy

omit [FiniteDimensional F Y] in
/-- The orthogonal of a compact set is a neighbourhood of `0`. -/
theorem orthLeft_mem_nhds (hψ : Continuous ψ) {K : Set Y} (hK : IsCompact K) :
    (orthLeft β ψ K : Set X) ∈ 𝓝 0 := by
  have hc : Continuous fun z : X × Y => β z.1 z.2 :=
    IsModuleTopology.continuous_bilinear_of_finite_left β
  have := hK.eventually_forall_of_forall_eventually (x₀ := (0 : X))
    (P := fun x y => ψ (β x y) = 1) fun y _ =>
      (hc.tendsto' ((0 : X), y) 0 (by simp)).eventually (eventually_addChar_eq_one hψ)
  filter_upwards [this] with x hx using hx

omit [FiniteDimensional F X] [TopologicalSpace X] [IsModuleTopology F X] [FiniteDimensional F Y] in
/-- The orthogonals are closed. -/
theorem isClosed_orthRight (hψ : Continuous ψ) (T : Set X) :
    IsClosed (orthRight β ψ T : Set Y) := by
  have : (orthRight β ψ T : Set Y) = ⋂ x ∈ T, (fun y => ψ (β x y)) ⁻¹' {1} := by
    ext y; simp [mem_orthRight]
  rw [this]
  refine isClosed_biInter fun x _ => isClosed_singleton.preimage (hψ.comp ?_)
  exact IsModuleTopology.continuous_of_linearMap (β x)

omit [FiniteDimensional F X] [FiniteDimensional F Y] [TopologicalSpace Y] [IsModuleTopology F Y] in
/-- The orthogonals are closed. -/
theorem isClosed_orthLeft (hψ : Continuous ψ) (T : Set Y) :
    IsClosed (orthLeft β ψ T : Set X) := by
  have : (orthLeft β ψ T : Set X) = ⋂ y ∈ T, (fun x => ψ (β x y)) ⁻¹' {1} := by
    ext x; simp [mem_orthLeft]
  rw [this]
  refine isClosed_biInter fun y _ => isClosed_singleton.preimage (hψ.comp ?_)
  exact IsModuleTopology.continuous_of_linearMap (β.flip y)

/-- For a perfect pairing, `ψ ∘ symmForm β` is a self-dual bicharacter of `X × Y`. -/
theorem isSelfDualBicharacter_symmForm [β.IsPerfPair] (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) :
    IsSelfDualBicharacter fun v w : X × Y => ψ (symmForm β v w) := by
  refine isSelfDualBicharacter_of_symm hψ (norm_addChar_eq_one hψ) hψ1 (symmForm β)
    (fun v w => by simp only [symmForm_apply]; ring) fun w hw => ?_
  have h2 : w.2 = 0 := (LinearMap.IsPerfPair.bijective_right β).1 <| LinearMap.ext fun x => by
    simpa [symmForm_apply] using hw (x, 0)
  have h1 : w.1 = 0 := (LinearMap.IsPerfPair.bijective_left β).1 <| LinearMap.ext fun y => by
    simpa [symmForm_apply] using hw (0, y)
  exact Prod.ext h1 h2

/-- The orthogonal of a neighbourhood of `0` is compact. -/
theorem isCompact_orthRight [β.IsPerfPair] (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {N : Set X}
    (hN : N ∈ 𝓝 0) : IsCompact (orthRight β ψ N : Set Y) := by
  obtain ⟨K, hK, hKy⟩ := (isSelfDualBicharacter_symmForm (β := β) hψ hψ1).big (N ×ˢ Set.univ)
    (prod_mem_nhds hN Filter.univ_mem)
  refine (hK.image (show Continuous (Prod.snd : X × Y → Y) from continuous_snd)).of_isClosed_subset
    (isClosed_orthRight hψ N) fun y hy => ?_
  refine ⟨(0, y), hKy (0, y) fun v hv => ?_, rfl⟩
  simpa [symmForm_apply] using hy v.1 hv.1

/-- The orthogonal of a neighbourhood of `0` is compact. -/
theorem isCompact_orthLeft [β.IsPerfPair] (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {N : Set Y}
    (hN : N ∈ 𝓝 0) : IsCompact (orthLeft β ψ N : Set X) := by
  obtain ⟨K, hK, hKx⟩ := (isSelfDualBicharacter_symmForm (β := β) hψ hψ1).big (Set.univ ×ˢ N)
    (prod_mem_nhds Filter.univ_mem hN)
  refine (hK.image (show Continuous (Prod.fst : X × Y → X) from continuous_fst)).of_isClosed_subset
    (isClosed_orthLeft hψ N) fun x hx => ?_
  refine ⟨(x, 0), hKx (x, 0) fun v hv => ?_, rfl⟩
  simpa [symmForm_apply] using hx v.2 hv.2

/-- A compact subgroup is finite modulo a neighbourhood subgroup. -/
theorem finite_quotient_addSubgroupOf {W : Type*} [AddCommGroup W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] (A U : AddSubgroup W) (hU : (U : Set W) ∈ 𝓝 0)
    (hA : IsCompact (A : Set W)) : Finite (A ⧸ U.addSubgroupOf A) := by
  have hfin := finite_image_quotient U (U.isOpen_of_mem_nhds hU) hA
  refine Set.finite_univ_iff.1 (Set.Finite.of_finite_image
    (f := fun q : A ⧸ U.addSubgroupOf A => (q.out.1 : W ⧸ U)) (hfin.subset ?_)
    fun p _ q _ hpq => ?_)
  · rintro _ ⟨q, -, rfl⟩
    exact ⟨_, q.out.2, rfl⟩
  · rw [← p.out_eq, ← q.out_eq]
    have := QuotientAddGroup.eq.1 hpq
    exact QuotientAddGroup.eq.2 this

/-- The values of an additive character are non-zero. -/
theorem addChar_ne_zero {K : Type*} [AddGroup K] (ψ : AddChar K ℂ) (t : K) : ψ t ≠ 0 := fun h => by
  have := AddChar.map_add_eq_mul ψ t (-t)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

/-! ### Pairs of lattices orthogonal to each other -/

variable (β ψ) in
/-- A pair of compact open subgroups `L ⊆ X`, `M ⊆ Y`, each the orthogonal of the other for the
pairing `ψ ∘ β`. -/
structure LatticePair where
  /-- The subgroup `L` of `X`. -/
  left : AddSubgroup X
  /-- The subgroup `M` of `Y`. -/
  right : AddSubgroup Y
  left_eq : left = orthLeft β ψ (right : Set Y)
  right_eq : right = orthRight β ψ (left : Set X)
  isCompact_left : IsCompact (left : Set X)
  isOpen_left : IsOpen (left : Set X)
  isCompact_right : IsCompact (right : Set Y)
  isOpen_right : IsOpen (right : Set Y)

namespace LatticePair

variable (P : LatticePair β ψ)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F X]
  [IsModuleTopology F X] [FiniteDimensional F Y] [IsModuleTopology F Y] in
theorem apply_eq_one {x : X} {y : Y} (hx : x ∈ P.left) (hy : y ∈ P.right) : ψ (β x y) = 1 := by
  rw [P.right_eq] at hy
  exact hy x hx

/-- Such pairs exist for a perfect pairing and a non-trivial character: `M = L₀^⊥`, `L = M^⊥`
for a compact open subgroup `L₀` of `X`. -/
theorem nonempty [β.IsPerfPair] (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) :
    Nonempty (LatticePair β ψ) := by
  have := IsModuleTopology.isTopologicalAddGroup F X
  have := IsModuleTopology.isTopologicalAddGroup F Y
  have := compactOpenExhaustion_of_finiteDimensional F X
  obtain ⟨L₀, hc, ho, -⟩ := CompactOpenExhaustion.exists_subset (X := X) Set.univ univ_mem
  have hMn : (orthRight β ψ (L₀ : Set X) : Set Y) ∈ 𝓝 0 := orthRight_mem_nhds hψ hc
  have hMc : IsCompact (orthRight β ψ (L₀ : Set X) : Set Y) :=
    isCompact_orthRight hψ hψ1 (ho.mem_nhds L₀.zero_mem)
  exact ⟨⟨orthLeft β ψ (orthRight β ψ (L₀ : Set X) : Set Y), orthRight β ψ (L₀ : Set X), rfl,
    (orthRight_orthLeft_orthRight _).symm, isCompact_orthLeft hψ hψ1 hMn,
    AddSubgroup.isOpen_of_mem_nhds _ (orthLeft_mem_nhds hψ hMc), hMc,
    AddSubgroup.isOpen_of_mem_nhds _ hMn⟩⟩

omit [FiniteDimensional F X] [TopologicalSpace X] [IsModuleTopology F X] [FiniteDimensional F Y]
  [TopologicalSpace Y] [IsModuleTopology F Y] in
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem pair_smul (c : F) (x : X) (y : Y) : β (c • x) y = β x (c • y) := by
  rw [map_smul, LinearMap.smul_apply, map_smul]

/-- The scaled pair `(t L, t⁻¹ M)`. -/
def smul (t : Fˣ) : LatticePair β ψ where
  left :=
    { carrier := {x | (t : F)⁻¹ • x ∈ P.left}
      add_mem' := fun {a b} ha hb => by
        change (t : F)⁻¹ • (a + b) ∈ P.left
        rw [smul_add]; exact P.left.add_mem ha hb
      zero_mem' := by change (t : F)⁻¹ • (0 : X) ∈ P.left; simp
      neg_mem' := fun {a} ha => by
        change (t : F)⁻¹ • (-a) ∈ P.left
        rw [smul_neg]; exact P.left.neg_mem ha }
  right :=
    { carrier := {y | (t : F) • y ∈ P.right}
      add_mem' := fun {a b} ha hb => by
        change (t : F) • (a + b) ∈ P.right
        rw [smul_add]; exact P.right.add_mem ha hb
      zero_mem' := by change (t : F) • (0 : Y) ∈ P.right; simp
      neg_mem' := fun {a} ha => by
        change (t : F) • (-a) ∈ P.right
        rw [smul_neg]; exact P.right.neg_mem ha }
  left_eq := by
    ext x
    change (t : F)⁻¹ • x ∈ P.left ↔ ∀ y, (t : F) • y ∈ P.right → ψ (β x y) = 1
    rw [P.left_eq]
    refine ⟨fun h y hy => ?_, fun h m hm => ?_⟩
    · have := h _ hy
      rwa [pair_smul, smul_smul, inv_mul_cancel₀ t.ne_zero, one_smul] at this
    · have := h ((t : F)⁻¹ • m) (by rwa [smul_smul, mul_inv_cancel₀ t.ne_zero, one_smul])
      rwa [← pair_smul] at this
  right_eq := by
    ext y
    change (t : F) • y ∈ P.right ↔ ∀ x, (t : F)⁻¹ • x ∈ P.left → ψ (β x y) = 1
    rw [P.right_eq]
    refine ⟨fun h x hx => ?_, fun h l hl => ?_⟩
    · have := h _ hx
      rwa [pair_smul, smul_smul, inv_mul_cancel₀ t.ne_zero, one_smul] at this
    · have := h ((t : F) • l) (by rwa [smul_smul, inv_mul_cancel₀ t.ne_zero, one_smul])
      rwa [pair_smul] at this
  isCompact_left := by
    have := IsModuleTopology.toContinuousSMul F X
    exact (Homeomorph.smulOfNeZero _ (inv_ne_zero t.ne_zero)).isCompact_preimage.2
      P.isCompact_left
  isOpen_left := by
    have := IsModuleTopology.toContinuousSMul F X
    exact P.isOpen_left.preimage (continuous_const_smul _)
  isCompact_right := by
    have := IsModuleTopology.toContinuousSMul F Y
    exact (Homeomorph.smulOfNeZero _ t.ne_zero).isCompact_preimage.2 P.isCompact_right
  isOpen_right := by
    have := IsModuleTopology.toContinuousSMul F Y
    exact P.isOpen_right.preimage (continuous_const_smul _)

omit [FiniteDimensional F X] [FiniteDimensional F Y] [ValuativeRel F]
  [IsNonarchimedeanLocalField F] in
theorem mem_smul_left {t : Fˣ} {x : X} : x ∈ (P.smul t).left ↔ (t : F)⁻¹ • x ∈ P.left :=
  Iff.rfl

omit [FiniteDimensional F X] [FiniteDimensional F Y] [ValuativeRel F]
  [IsNonarchimedeanLocalField F] in
theorem mem_smul_right {t : Fˣ} {y : Y} : y ∈ (P.smul t).right ↔ (t : F) • y ∈ P.right :=
  Iff.rfl

omit [FiniteDimensional F X] [FiniteDimensional F Y] in
/-- For `t` small, `t L` lies in a given neighbourhood of `0`. -/
theorem exists_smul_left_subset {U : Set X} (hU : U ∈ 𝓝 0) :
    ∃ t : Fˣ, ((P.smul t).left : Set X) ⊆ U := by
  have := IsModuleTopology.toContinuousSMul F X
  have hev : ∀ᶠ r in 𝓝 (0 : F), ∀ l ∈ (P.left : Set X), r • l ∈ U :=
    P.isCompact_left.eventually_forall_of_forall_eventually fun l _ =>
      (continuous_smul.tendsto' ((0 : F), l) 0 (by simp)).eventually hU
  obtain ⟨r, hr, hrU⟩ := exists_ne_zero_of_eventually hev
  refine ⟨Units.mk0 r hr, fun x hx => ?_⟩
  have := hrU _ hx
  rwa [Units.val_mk0, smul_inv_smul₀ hr] at this

omit [FiniteDimensional F X] [FiniteDimensional F Y] in
/-- For `t` large, `t⁻¹ M` lies in a given neighbourhood of `0`. -/
theorem exists_smul_right_subset {V : Set Y} (hV : V ∈ 𝓝 0) :
    ∃ t : Fˣ, ((P.smul t).right : Set Y) ⊆ V := by
  have := IsModuleTopology.toContinuousSMul F Y
  have hev : ∀ᶠ r in 𝓝 (0 : F), ∀ m ∈ (P.right : Set Y), r • m ∈ V :=
    P.isCompact_right.eventually_forall_of_forall_eventually fun m _ =>
      (continuous_smul.tendsto' ((0 : F), m) 0 (by simp)).eventually hV
  obtain ⟨r, hr, hrV⟩ := exists_ne_zero_of_eventually hev
  refine ⟨(Units.mk0 r hr)⁻¹, fun y hy => ?_⟩
  have := hrV _ hy
  rwa [Units.val_inv_eq_inv_val, Units.val_mk0, smul_inv_smul₀ hr] at this

end LatticePair

/-! ### The self-dual datum of a pair of lattices -/

variable [Invertible (2 : F)]

namespace LatticePair

variable (P : LatticePair β ψ)

omit [Invertible (2 : F)] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [FiniteDimensional F X] [IsModuleTopology F X] [FiniteDimensional F Y] [IsModuleTopology F Y] in
/-- `A = L × M` is self-orthogonal for `ψ ∘ polarizedForm β`. -/
theorem polarizedForm_eq_one {a b : X × Y} (ha : a ∈ P.left.prod P.right)
    (hb : b ∈ P.left.prod P.right) : ψ (polarizedForm β a b) = 1 := by
  rw [polarizedForm_apply, sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
    P.apply_eq_one ha.1 hb.2, P.apply_eq_one hb.1 ha.2, inv_one, mul_one]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F X]
  [IsModuleTopology F X] [FiniteDimensional F Y] [IsModuleTopology F Y] [Invertible (2 : F)] in
/-- The orthogonal of `A = L × M` for `ψ ∘ polarizedForm β` is `A`. -/
theorem mem_of_mem_charOrthogonal {w : X × Y}
    (hw : w ∈ charOrthogonal (polarizedForm β) ψ (P.left.prod P.right : Set (X × Y))) :
    w ∈ P.left.prod P.right := by
  rw [mem_charOrthogonal] at hw
  refine ⟨?_, ?_⟩
  · rw [P.left_eq]
    intro m hm
    have := hw (0, m) ⟨P.left.zero_mem, hm⟩
    simpa [polarizedForm_apply] using this
  · rw [P.right_eq]
    intro l hl
    have := hw (l, 0) ⟨hl, P.right.zero_mem⟩
    simp only [polarizedForm_apply, map_zero, zero_sub, AddChar.map_neg_eq_inv, inv_eq_one] at this
    exact this

/-- **The self-dual datum** `A = L × M`, `ψ_A(l, m) = ψ(½ β(l, m))`, of a pair of lattices. -/
def toSelfDualDatum (hψ : Continuous ψ) : SelfDualDatum (polarizedForm β) ψ where
  subgroup := P.left.prod P.right
  character w := ψ (⅟2 * β w.1 w.2)
  character_ne_zero a _ := addChar_ne_zero ψ _
  character_mul a ha b hb := by
    have h2 : (⅟2 : F) + ⅟2 = 1 := by rw [← two_mul, mul_invOf_self]
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    have e : ⅟2 * polarizedForm β a b + ⅟2 * β (a + b).1 (a + b).2 =
        (⅟2 * β a.1 a.2 + ⅟2 * β b.1 b.2) + β a.1 b.2 := by
      simp only [polarizedForm_apply, Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
      linear_combination (β a.1 b.2) * h2
    rw [e, AddChar.map_add_eq_mul _ (⅟2 * β a.1 a.2 + ⅟2 * β b.1 b.2) (β a.1 b.2),
      P.apply_eq_one ha.1 hb.2, mul_one]
  charOrthogonal_le w hw := P.mem_of_mem_charOrthogonal hw
  eventually_mem := by
    have hA : ((P.left.prod P.right : AddSubgroup (X × Y)) : Set (X × Y)) ∈ 𝓝 0 := by
      rw [AddSubgroup.coe_prod]
      exact prod_mem_nhds (P.isOpen_left.mem_nhds P.left.zero_mem)
        (P.isOpen_right.mem_nhds P.right.zero_mem)
    have hc : Continuous fun w : X × Y => ⅟2 * β w.1 w.2 :=
      continuous_const.mul (IsModuleTopology.continuous_bilinear_of_finite_left β)
    filter_upwards [hA, (hc.tendsto' 0 0 (by simp)).eventually (eventually_addChar_eq_one hψ)]
      with u hu hu' using ⟨hu, hu'⟩
  exists_finite N hN := by
    have := IsModuleTopology.toContinuousSMul F (X × Y)
    have := IsModuleTopology.isTopologicalAddGroup F (X × Y)
    set A := P.left.prod P.right
    have hAc : IsCompact (A : Set (X × Y)) := by
      rw [AddSubgroup.coe_prod]; exact P.isCompact_left.prod P.isCompact_right
    have hAo : IsOpen (A : Set (X × Y)) := by
      rw [AddSubgroup.coe_prod]; exact P.isOpen_left.prod P.isOpen_right
    have hev : ∀ᶠ r in 𝓝 (0 : F), ∀ a ∈ (A : Set (X × Y)), r • a ∈ N :=
      hAc.eventually_forall_of_forall_eventually fun a _ =>
        (continuous_smul.tendsto' ((0 : F), a) 0 (by simp)).eventually hN
    obtain ⟨r, hr, hrN⟩ := exists_ne_zero_of_eventually hev
    have key : ∀ w, w ∈ charOrthogonal (polarizedForm β) ψ ((fun a => r⁻¹ • a) '' (A : Set _)) ↔
        r⁻¹ • w ∈ A := by
      intro w
      have e : ∀ a, polarizedForm β w (r⁻¹ • a) = polarizedForm β (r⁻¹ • w) a := fun a => by
        rw [map_smul, map_smul, LinearMap.smul_apply]
      constructor
      · intro hw
        refine P.mem_of_mem_charOrthogonal fun a ha => ?_
        rw [← e]; exact hw _ ⟨a, ha, rfl⟩
      · rintro hw _ ⟨a, ha, rfl⟩
        rw [e]; exact P.polarizedForm_eq_one hw ha
    refine ⟨(fun a => r⁻¹ • a) '' (A : Set _), fun w hw => ?_, ?_⟩
    · have := hrN _ ((key w).1 hw)
      rwa [smul_inv_smul₀ hr] at this
    · refine finite_quotient_addSubgroupOf A _ ?_ hAc
      have : (fun w : X × Y => r⁻¹ • w) ⁻¹' (A : Set _) ∈ 𝓝 0 :=
        (hAo.preimage (continuous_const_smul _)).mem_nhds (by simp)
      filter_upwards [this] with w hw using (key w).2 hw

omit [FiniteDimensional F Y] in
@[simp] theorem toSelfDualDatum_subgroup (hψ : Continuous ψ) :
    (P.toSelfDualDatum hψ).subgroup = P.left.prod P.right := rfl

omit [FiniteDimensional F Y] in
@[simp] theorem toSelfDualDatum_character (hψ : Continuous ψ) (w : X × Y) :
    (P.toSelfDualDatum hψ).character w = ψ (⅟2 * β w.1 w.2) := rfl

end LatticePair

/-! ### Eigenvectors and translates in the Schrödinger model -/

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F X]
  [IsModuleTopology F X] [FiniteDimensional F Y] [IsModuleTopology F Y] in
/-- The eigenvectors of the operators of `A = L × M` with eigenvalue `ψ(½ β(l, m))` in the
Schrödinger model are the multiples of `1_L`: they are `L`-invariant, and supported in
`M^⊥ = L`. -/
theorem LatticePair.eq_indicator_of_eigen (P : LatticePair β ψ) {f : X → ℂ}
    (hf : ∀ a ∈ P.left.prod P.right, schrodingerFun ψ β a f = ψ (⅟2 * β a.1 a.2) • f) :
    f = f 0 • (P.left : Set X).indicator (fun _ => (1 : ℂ)) := by
  have hinv : ∀ l ∈ P.left, ∀ x, f (x + l) = f x := fun l hl x => by
    have := congrFun (hf (l, 0) ⟨hl, P.right.zero_mem⟩) x
    simpa [schrodingerFun_apply] using this
  have hsupp : ∀ x, f x ≠ 0 → x ∈ P.left := fun x hx => by
    rw [P.left_eq]
    intro m hm
    have := congrFun (hf (0, m) ⟨P.left.zero_mem, hm⟩) x
    simp only [schrodingerFun_apply, map_zero, LinearMap.zero_apply, mul_zero, add_zero,
      AddChar.map_zero_eq_one, one_smul] at this
    exact (mul_eq_right₀ hx).1 this
  funext x
  by_cases hx : x ∈ (P.left : Set X)
  · rw [Pi.smul_apply, Set.indicator_of_mem hx, smul_eq_mul, mul_one]
    simpa using hinv x hx 0
  · rw [Pi.smul_apply, Set.indicator_of_notMem hx, smul_zero]
    by_contra h
    exact hx (hsupp x h)

/-- A function invariant under an open subgroup `U` and vanishing off a compact set `C` is a finite
combination of translates of `1_U`, indexed by the classes of `C` modulo `U`. -/
theorem eq_sum_translates [IsTopologicalAddGroup X] (U : AddSubgroup X) (hU : IsOpen (U : Set X))
    {f : X → ℂ} (hfU : ∀ u ∈ U, ∀ x, f (x + u) = f x) {C : Set X} (hC : IsCompact C)
    (hfC : ∀ x ∉ C, f x = 0) :
    f = ∑ c ∈ (finite_image_quotient U hU hC).toFinset,
      f (Quotient.out c) •
        fun x => (U : Set X).indicator (fun _ => (1 : ℂ)) (x - Quotient.out c) := by
  classical
  have hmem : ∀ (c : X ⧸ U) (x : X), x - Quotient.out c ∈ U ↔ (x : X ⧸ U) = c := fun c x => by
    conv_rhs => rw [← QuotientAddGroup.out_eq' c]
    rw [eq_comm, QuotientAddGroup.eq, neg_add_eq_sub]
  have hout : ∀ x : X, f (Quotient.out (x : X ⧸ U)) = f x := fun x => by
    have h := (hmem (x : X ⧸ U) x).2 rfl
    have := hfU _ (U.neg_mem h) x
    rwa [neg_sub, add_sub_cancel] at this
  funext x
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hx : (x : X ⧸ U) ∈ (QuotientAddGroup.mk : X → X ⧸ U) '' C
  · rw [Finset.sum_eq_single (x : X ⧸ U)]
    · rw [Set.indicator_of_mem ((hmem _ x).2 rfl), mul_one, hout]
    · intro c _ hc
      rw [Set.indicator_of_notMem fun h => hc ((hmem c x).1 h).symm, mul_zero]
    · intro h
      exact absurd (Set.Finite.mem_toFinset _ |>.2 hx) h
  · rw [hfC x fun hxC => hx ⟨x, hxC, rfl⟩]
    refine (Finset.sum_eq_zero fun c hc => ?_).symm
    rw [Set.indicator_of_notMem fun h => hx ?_, mul_zero]
    rw [(hmem c x).1 h]
    exact (Set.Finite.mem_toFinset _).1 hc

end SchrodingerIrreducible.Internal

open SchrodingerIrreducible.Internal

variable {X : Type v} [AddCommGroup X] [Module F X] [FiniteDimensional F X] [TopologicalSpace X]
  [IsModuleTopology F X] [IsTopologicalAddGroup X] {Y : Type w} [AddCommGroup Y] [Module F Y]
  [FiniteDimensional F Y] [TopologicalSpace Y] [IsModuleTopology F Y] {β : X →ₗ[F] Y →ₗ[F] F}
  {ψ : AddChar F ℂ} [Invertible (2 : F)]

/-- **The Schrödinger model is smooth** (GKT Theorem 1.13, p. 25: it is a model of the Heisenberg
representation): a Schwartz–Bruhat function `φ` is invariant under the translations by a
neighbourhood of `0`, and the characters `ψ(β(·, y))` are trivial on its support for `y` near
`0`. -/
theorem isSmooth_schrodingerSB (hψ : Continuous ψ) (hβ : ∀ y, Continuous fun x => β x y) :
    IsSmooth (schrodingerSB hψ hβ) := by
  refine isSmooth_of_eventually hψ (schrodingerSB_hasCentralCharacter hψ hβ) fun v => ?_
  have hv := v.2
  have h1 := HarmonicAnalysis.eventually_add_eq_of_mem_schwartzBruhatSubmodule hv
  have h2 : (orthRight β ψ (tsupport (v : X → ℂ)) : Set Y) ∈ 𝓝 0 :=
    orthRight_mem_nhds hψ hv.2
  have hc : Continuous fun w : X × Y => ⅟2 * β w.1 w.2 :=
    continuous_const.mul (IsModuleTopology.continuous_bilinear_of_finite_left β)
  have h3 := (hc.tendsto' 0 0 (by simp)).eventually (eventually_addChar_eq_one hψ)
  filter_upwards [(continuous_fst.tendsto' (0 : X × Y) 0 rfl).eventually h1,
    (continuous_snd.tendsto' (0 : X × Y) 0 rfl).eventually h2, h3] with u hu1 hu2 hu3
  apply Subtype.ext
  funext x
  rw [schrodingerSB_apply, schrodinger_ofVec, schrodingerFun_apply, hu1 x,
    AddChar.map_add_eq_mul, hu3, mul_one]
  by_cases hx : x ∈ tsupport (v : X → ℂ)
  · rw [hu2 x hx, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

/-- The indicator of a compact open subgroup, as a Schwartz–Bruhat function. -/
private def indicatorSB (U : AddSubgroup X) (hc : IsCompact (U : Set X)) (ho : IsOpen (U : Set X)) :
    SchwartzBruhat X :=
  ⟨_, HarmonicAnalysis.indicator_one_mem_schwartzBruhatSubmodule U hc ho⟩

omit [FiniteDimensional F X] [IsModuleTopology F X] [FiniteDimensional F Y] [TopologicalSpace Y]
  [IsModuleTopology F Y] in
/-- The translate `x ↦ 1_U(x - x₀)` is the Schrödinger operator of `(-x₀, 0)` applied to `1_U`. -/
private theorem schrodingerSB_indicatorSB (hψ : Continuous ψ)
    (hβ : ∀ y, Continuous fun x => β x y) (U : AddSubgroup X) (hc : IsCompact (U : Set X))
    (ho : IsOpen (U : Set X)) (x₀ x : X) :
    (schrodingerSB hψ hβ (ofVec (-x₀, 0)) (indicatorSB U hc ho) : X → ℂ) x =
      (U : Set X).indicator (fun _ => (1 : ℂ)) (x - x₀) := by
  rw [schrodingerSB_apply, schrodinger_ofVec, schrodingerFun_apply]
  simp only [map_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul, sub_eq_add_neg]
  rfl

omit [FiniteDimensional F X] [IsModuleTopology F X] [FiniteDimensional F Y] [TopologicalSpace Y]
  [IsModuleTopology F Y] in
/-- A Schwartz–Bruhat function invariant under a compact open subgroup `U` and vanishing off a
compact set `C` lies in the span of the translates of `1_U` by the representatives of `C / U`. -/
private theorem mem_span_translates (hψ : Continuous ψ) (hβ : ∀ y, Continuous fun x => β x y)
    (U : AddSubgroup X) (hc : IsCompact (U : Set X)) (ho : IsOpen (U : Set X)) {C : Set X}
    (hC : IsCompact C) (f : SchwartzBruhat X) (hfU : ∀ u ∈ U, ∀ x, (f : X → ℂ) (x + u) = f x)
    (hfC : ∀ x ∉ C, (f : X → ℂ) x = 0) :
    f = ∑ c ∈ (finite_image_quotient U ho hC).toFinset,
      (f : X → ℂ) (Quotient.out c) •
        schrodingerSB hψ hβ (ofVec (-Quotient.out c, 0)) (indicatorSB U hc ho) := by
  have h := eq_sum_translates U ho hfU hC hfC
  apply Subtype.ext
  refine h.trans ?_
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  funext x
  rw [schrodingerSB_indicatorSB]

/-- **The Schrödinger model is irreducible** (GKT Theorem 1.13, p. 25): for a perfect pairing `β`
and a non-trivial continuous `ψ`, every non-zero subrepresentation of `schrodingerSB` contains
the indicators `1_{tL}` of the lattices of all the scaled pairs `(tL, t⁻¹M)`, as the only
eigenvectors of `tL × t⁻¹M`, and these span the Schwartz–Bruhat functions. -/
theorem isIrreducible_schrodingerSB [β.IsPerfPair] (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (hβ : ∀ y, Continuous fun x => β x y) : (schrodingerSB hψ hβ).IsIrreducible := by
  obtain ⟨P₀⟩ := LatticePair.nonempty (β := β) hψ hψ1
  have hs := isSmooth_schrodingerSB hψ hβ
  have hπ := schrodingerSB_hasCentralCharacter hψ hβ
  have key : ∀ P : Subrepresentation (schrodingerSB hψ hβ), P ≠ ⊥ → ∀ t : Fˣ,
      indicatorSB (P₀.smul t).left (P₀.smul t).isCompact_left (P₀.smul t).isOpen_left ∈
        P.toSubmodule := by
    intro P hP t
    obtain ⟨e, heP, he0, he⟩ := ((P₀.smul t).toSelfDualDatum hψ).exists_eigenvector_mem
      (polarizedForm_isAlt β) hπ hs P hP
    have hfun := (P₀.smul t).eq_indicator_of_eigen (f := (e : X → ℂ)) fun a ha => by
      have := congrArg Subtype.val (he a ha)
      simpa [schrodingerSB_apply, schrodinger_ofVec] using this
    have he00 : (e : X → ℂ) 0 ≠ 0 := fun h => he0 (Subtype.ext (by rw [hfun, h, zero_smul]; rfl))
    have : indicatorSB (P₀.smul t).left (P₀.smul t).isCompact_left (P₀.smul t).isOpen_left =
        ((e : X → ℂ) 0)⁻¹ • e := by
      apply Subtype.ext
      set c := (e : X → ℂ) 0
      rw [Submodule.coe_smul, hfun, smul_smul, inv_mul_cancel₀ he00, one_smul]
      rfl
    rw [this]
    exact P.toSubmodule.smul_mem _ heP
  have hne : indicatorSB P₀.left P₀.isCompact_left P₀.isOpen_left ≠ 0 := fun h => by
    have := congrFun (congrArg Subtype.val h) 0
    simp [indicatorSB] at this
  have : Nontrivial (Subrepresentation (schrodingerSB hψ hβ)) := ⟨⊥, ⊤, fun h => hne (by
    have : indicatorSB P₀.left P₀.isCompact_left P₀.isOpen_left ∈
        (⊥ : Subrepresentation (schrodingerSB hψ hβ)).toSubmodule := h ▸ Submodule.mem_top
    exact this)⟩
  refine ⟨fun P => or_iff_not_imp_left.2 fun hP => ?_⟩
  refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun f _ => ?_)
  obtain ⟨t, ht⟩ := P₀.exists_smul_left_subset
    (HarmonicAnalysis.eventually_add_eq_of_mem_schwartzBruhatSubmodule f.2)
  rw [mem_span_translates hψ hβ (P₀.smul t).left (P₀.smul t).isCompact_left
    (P₀.smul t).isOpen_left f.2.2 f (fun u hu => ht hu)
    (fun x hx => image_eq_zero_of_notMem_tsupport hx)]
  exact P.toSubmodule.sum_mem fun c _ => P.toSubmodule.smul_mem _
    (P.apply_mem_toSubmodule _ (key P hP t))

/-- **The Schrödinger model is admissible** (GKT Proposition 1.29, p. 35): an open subgroup `K` of
the Heisenberg group contains `(tL × s⁻¹M, 0)` for suitable `t`, `s`; a vector fixed by it is
`tL`-invariant and supported in `(s⁻¹ M)^⊥ = sL`, so it lies in the span of the finitely many
translates of `1_{tL}` by the representatives of `sL / tL`. -/
theorem isAdmissible_schrodingerSB [β.IsPerfPair] (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (hβ : ∀ y, Continuous fun x => β x y) : IsAdmissible (schrodingerSB hψ hβ) := by
  refine ⟨isSmooth_schrodingerSB hψ hβ, fun K => ?_⟩
  obtain ⟨P₀⟩ := LatticePair.nonempty (β := β) hψ hψ1
  have hK : (ofVec ⁻¹' (K : Set (HeisenbergGroup (polarizedForm β))) : Set (X × Y)) ∈
      𝓝 ((0 : X), (0 : Y)) :=
    continuous_ofVec.continuousAt.preimage_mem_nhds (K.isOpen.mem_nhds K.one_mem)
  obtain ⟨V₁, hV₁, V₂, hV₂, hV⟩ := mem_nhds_prod_iff.1 hK
  obtain ⟨t, ht⟩ := P₀.exists_smul_left_subset hV₁
  obtain ⟨s, hs⟩ := P₀.exists_smul_right_subset hV₂
  have hfin := finite_image_quotient (P₀.smul t).left (P₀.smul t).isOpen_left
    (P₀.smul s).isCompact_left
  let g : (X ⧸ (P₀.smul t).left) → SchwartzBruhat X := fun c =>
    schrodingerSB hψ hβ (ofVec (-Quotient.out c, 0))
      (indicatorSB (P₀.smul t).left (P₀.smul t).isCompact_left (P₀.smul t).isOpen_left)
  have hle : fixedVectors (schrodingerSB hψ hβ) K.toSubgroup ≤
      Submodule.span ℂ (g '' (hfin.toFinset : Set (X ⧸ (P₀.smul t).left))) := by
    intro f hf
    have hfix : ∀ w ∈ V₁ ×ˢ V₂, schrodingerSB hψ hβ (ofVec w) f = f := fun w hw =>
      (Representation.mem_invariants _ f).1 hf ⟨ofVec w, hV hw⟩
    have hfU : ∀ u ∈ (P₀.smul t).left, ∀ x, (f : X → ℂ) (x + u) = f x := fun u hu x => by
      have := congrFun (congrArg Subtype.val (hfix (u, 0) ⟨ht hu, mem_of_mem_nhds hV₂⟩)) x
      simpa [schrodingerSB_apply, schrodinger_ofVec] using this
    have hfC : ∀ x ∉ ((P₀.smul s).left : Set X), (f : X → ℂ) x = 0 := fun x hx => by
      by_contra h0
      apply hx
      rw [(P₀.smul s).left_eq]
      intro m hm
      have := congrFun (congrArg Subtype.val (hfix (0, m) ⟨mem_of_mem_nhds hV₁, hs hm⟩)) x
      simp only [schrodingerSB_apply, schrodinger_ofVec, schrodingerFun_apply, map_zero,
        LinearMap.zero_apply, mul_zero, add_zero] at this
      exact (mul_eq_right₀ h0).1 this
    rw [mem_span_translates hψ hβ (P₀.smul t).left (P₀.smul t).isCompact_left
      (P₀.smul t).isOpen_left (P₀.smul s).isCompact_left f hfU hfC]
    exact Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨c, by simpa using hc, rfl⟩)
  have : FiniteDimensional ℂ
      (Submodule.span ℂ (g '' (hfin.toFinset : Set (X ⧸ (P₀.smul t).left)))) :=
    FiniteDimensional.span_of_finite ℂ ((Finset.finite_toSet _).image g)
  exact Submodule.finiteDimensional_of_le hle

end Langlands.HeisenbergGroup
