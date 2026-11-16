import Langlands.Representation.Archimedean.LowerVermaFiltration

/-!
# Projectivity of lower Verma modules of `𝔤𝔩_n(ℂ)`

`lowerVermaProjective : VermaGL.LowerVermaProjectiveStatement`. See the paired Markdown.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.VermaPBW

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Algebra.UniversalEnveloping
open scoped TensorProduct

/-! ## The tensor product representation -/

section Tensor

variable (n : ℕ) (lam : Fin n → ℂ) {Wt : Type*} [AddCommGroup Wt] [Module ℂ Wt]
  (σ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ Wt)

/-- The tensor product representation `Y ↦ σ(Y) ⊗ 1 + 1 ⊗ Y` on `W ⊗ M⁻(λ)`: the Library's
`BGChase.tensorLie` for `σ` and the action on `M⁻(λ)`. -/
abbrev rhoT : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆
    Module.End ℂ (Wt ⊗[ℂ] VermaGL.LowerVerma n lam) :=
  BGChase.tensorLie σ (VermaGL.action n lam)

theorem rhoT_apply (Y : Matrix (Fin n) (Fin n) ℂ) :
    rhoT n lam σ Y = VermaGL.tensorEnd (σ Y) (VermaGL.action n lam Y) := rfl

theorem rhoT_tmul (Y : Matrix (Fin n) (Fin n) ℂ) (w : Wt) (x : VermaGL.LowerVerma n lam) :
    rhoT n lam σ Y (w ⊗ₜ x) = σ Y w ⊗ₜ x + w ⊗ₜ (UniversalEnvelopingAlgebra.ι ℂ Y • x) := by
  rw [rhoT_apply, VermaGL.tensorEnd, LinearMap.add_apply, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul]
  rfl

variable {D : ℕ} (b : Module.Basis (Fin D) ℂ Wt) (m : Fin D → Fin n → ℤ)
  (hb : ∀ k p, σ (unitE n (p, p)) (b k) = (m k p : ℂ) • b k)

/-- The generators `b_j ⊗ gen`. -/
def Gt (j : Fin D) : Wt ⊗[ℂ] VermaGL.LowerVerma n lam := b j ⊗ₜ VermaGL.gen n lam

include hb in
theorem isWt_Gt (j : Fin D) : IsWt n (rhoT n lam σ) (Gt n lam b j) (lam + wtC n m j) := by
  intro p
  rw [Gt, rhoT_tmul, hb,
    show UniversalEnvelopingAlgebra.ι ℂ (unitE n (p, p)) • VermaGL.gen n lam =
      lam p • VermaGL.gen n lam from unitU_smul_gen n lam p,
    TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', ← add_smul]
  congr 1
  simp only [Pi.add_apply, wtC]
  ring

theorem tmul_eq_sum (w : Wt) (x : VermaGL.LowerVerma n lam) :
    w ⊗ₜ[ℂ] x = ∑ i, b.repr w i • (b i ⊗ₜ[ℂ] x) := by
  conv_lhs => rw [← b.sum_repr w]
  rw [TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.smul_tmul']

theorem rhoT_Gt_lower (j : Fin D) {p q : Fin n} (hqp : q < p) :
    rhoT n lam σ (unitE n (p, q)) (Gt n lam b j) =
      ∑ i, b.repr (σ (unitE n (p, q)) (b j)) i • Gt n lam b i := by
  have h0 : UniversalEnvelopingAlgebra.ι ℂ (unitE n (p, q)) • VermaGL.gen n lam = 0 := by
    have h := unitE_lo_smul_gen n lam 0 ⟨(p, q), not_lt.mpr hqp.le⟩
    rw [vVal_of_lt n lam 0 hqp, zero_smul] at h
    exact h
  rw [Gt, rhoT_tmul, h0, TensorProduct.tmul_zero, add_zero, tmul_eq_sum n lam b]
  rfl

include hb in
theorem Gt_lower_mem {T : Finset (Fin D)} {k : Fin D} (hk : k ∈ T)
    (hT : ∀ j, htZ n m j < htZ n m k → j ∈ T) {p q : Fin n} (hqp : q < p) :
    rhoT n lam σ (unitE n (p, q)) (Gt n lam b k) ∈ FG n (rhoT n lam σ) (Gt n lam b) (T.erase k) := by
  rw [rhoT_Gt_lower n lam σ b k hqp]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases h : b.repr (σ (unitE n (p, q)) (b k)) i = 0
  · rw [h, zero_smul]
    exact Submodule.zero_mem _
  · have hw := wtC_eq_of_lower_coeff n σ b m hb (p, q) (k := i) (i := k)
      (by rwa [Module.Basis.coord_apply])
    have hlt := htZ_lt_of_wtC_eq n m hqp hw
    have hiT : i ∈ T.erase k := Finset.mem_erase.mpr ⟨fun hik => by subst hik; omega, hT i hlt⟩
    exact Submodule.smul_mem _ _ (G_mem_FG n _ _ hiT)

theorem tmul_W_mem_FG (l : List (Idx n)) (j : Fin D) :
    b j ⊗ₜ[ℂ] (W n l • VermaGL.gen n lam) ∈
      FG n (rhoT n lam σ) (Gt n lam b) Finset.univ := by
  induction l generalizing j with
  | nil =>
    rw [W_nil, one_smul]
    exact G_mem_FG n _ _ (Finset.mem_univ j)
  | cons c l ih =>
    rw [W_cons, mul_smul]
    have h := rhoT_tmul n lam σ (unitE n c) (b j) (W n l • VermaGL.gen n lam)
    rw [tmul_eq_sum n lam b (σ (unitE n c) (b j))] at h
    rw [eq_sub_of_add_eq' h.symm]
    refine Submodule.sub_mem _ (isInv_FG n _ _ _ c _ (ih j)) ?_
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (ih i)

theorem tmul_mem_FG (j : Fin D) (x : VermaGL.LowerVerma n lam) :
    b j ⊗ₜ[ℂ] x ∈ FG n (rhoT n lam σ) (Gt n lam b) Finset.univ := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [mk_eq_smul_gen]
  have hu : u ∈ Submodule.span ℂ (Set.range (basisU n)) := by
    rw [(basisU n).span_eq]
    trivial
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨α, rfl⟩ := hu
    rw [basisU_apply]
    exact tmul_W_mem_FG n lam σ b _ j
  | zero => rw [zero_smul, TensorProduct.tmul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_smul, TensorProduct.tmul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_assoc, TensorProduct.tmul_smul]; exact Submodule.smul_mem _ a hx

theorem FP_univ : FG n (rhoT n lam σ) (Gt n lam b) Finset.univ = ⊤ := by
  refine eq_top_iff.mpr ?_
  rintro t -
  induction t using TensorProduct.inductionOn with
  | tmul w x =>
    rw [tmul_eq_sum n lam b]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (tmul_mem_FG n lam σ b i x)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

end Tensor

/-! ## Central characters as algebra maps -/

section Chi

variable (n : ℕ)

theorem smul_gen_inj (μ : Fin n → ℂ) {c c' : ℂ}
    (h : c • VermaGL.gen n μ = c' • VermaGL.gen n μ) : c = c' :=
  smul_left_injective ℂ (gen_ne_zero n μ) h

/-- The scalar by which a central element acts on `M⁻(μ)`. -/
def chiFun (μ : Fin n → ℂ) (z : VermaGL.center n) : ℂ := (center_smul_gen n μ z.2).choose

theorem chiFun_spec (μ : Fin n → ℂ) (z : VermaGL.center n) :
    (z : VermaGL.glU n) • VermaGL.gen n μ = chiFun n μ z • VermaGL.gen n μ :=
  (center_smul_gen n μ z.2).choose_spec

/-- The central character `χ_μ` of `M⁻(μ)`. -/
def chi (μ : Fin n → ℂ) : VermaGL.center n →ₐ[ℂ] ℂ where
  toFun := chiFun n μ
  map_one' := smul_gen_inj n μ (by rw [← chiFun_spec]; simp)
  map_mul' z z' := smul_gen_inj n μ (by
    rw [← chiFun_spec, Subalgebra.coe_mul, mul_smul, chiFun_spec n μ z', smul_comm,
      chiFun_spec n μ z, smul_smul, mul_comm])
  map_zero' := smul_gen_inj n μ (by rw [← chiFun_spec]; simp)
  map_add' z z' := smul_gen_inj n μ (by
    rw [← chiFun_spec, Subalgebra.coe_add, add_smul, chiFun_spec n μ z, chiFun_spec n μ z',
      add_smul])
  commutes' a := smul_gen_inj n μ (by
    rw [← chiFun_spec, Subalgebra.coe_algebraMap, algebraMap_smul]; rfl)

theorem chi_spec (μ : Fin n → ℂ) (z : VermaGL.center n) :
    (z : VermaGL.glU n) • VermaGL.gen n μ = chi n μ z • VermaGL.gen n μ :=
  chiFun_spec n μ z

/-- A singular vector of weight `μ` in any representation is an eigenvector of the center, with
eigenvalue `χ_μ`. -/
theorem env_singular {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ V) (μ : Fin n → ℂ) {x : V}
    (hlow : ∀ p q : Fin n, q < p → ρ (unitE n (p, q)) x = 0) (hw : IsWt n ρ x μ)
    (z : VermaGL.center n) : envelopingAction ρ z x = chi n μ z • x := by
  have h := env_center_sub_mem n ρ (isInv_bot n ρ) μ x
    (fun p q hqp => by rw [hlow p q hqp]; exact Submodule.zero_mem _)
    (fun p => by rw [hw p, sub_self]; exact Submodule.zero_mem _) (chi_spec n μ z)
  rwa [Submodule.mem_bot, sub_eq_zero] at h

/-- `Z`-extremality in terms of central characters. -/
theorem exists_chi_ne_of_isZExtremal {lam : Fin n → ℂ} (hZ : VermaGL.IsZExtremal n lam)
    {μ : Fin n → ℂ} (hμ : lam - μ ∈ VermaGL.posRootCone n) (hne : μ ≠ lam) :
    ∃ z : VermaGL.center n, chi n lam z ≠ chi n μ z := by
  obtain ⟨z, hz, c, h1, h2⟩ := hZ μ hμ hne
  refine ⟨⟨z, hz⟩, fun h => h2 ?_⟩
  have e1 := smul_gen_inj n lam (h1.symm.trans (chi_spec n lam ⟨z, hz⟩))
  rw [chi_spec n μ ⟨z, hz⟩, ← h, ← e1]

theorem aeval_apply_of_eigen {V : Type*} [AddCommGroup V] [Module ℂ V] {T : Module.End ℂ V}
    {c : ℂ} {x : V} (hx : T x = c • x) (p : Polynomial ℂ) :
    Polynomial.aeval T p x = p.eval c • x := by
  induction p using Polynomial.induction_on with
  | C a => simp [Module.algebraMap_end_apply]
  | add p q hp hq => simp [hp, hq, add_smul]
  | monomial k a ih =>
    rw [mul_comm, pow_succ', mul_assoc, map_mul, Module.End.mul_apply, mul_comm, ih]
    simp only [hx, smul_smul, Polynomial.aeval_X, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, map_smul]
    congr 1
    ring

end Chi

/-! ## The separating central element -/

section Separate

variable (n : ℕ) (lam : Fin n → ℂ) {D : ℕ} (m : Fin D → Fin n → ℤ)

/-- `j` is bad when the central character of `M⁻(λ + wt(b_j))` differs from that of `M⁻(λ)`. -/
def IsBad (j : Fin D) : Prop := ∃ z : VermaGL.center n, chi n lam z ≠ chi n (lam + wtC n m j) z

open Classical in
/-- One factor of the separating element. -/
def sepFactor (j : Fin D) : VermaGL.center n :=
  if h : IsBad n lam m j then
    h.choose - algebraMap ℂ (VermaGL.center n) (chi n (lam + wtC n m j) h.choose)
  else 1

/-- A central element on which `χ_λ` is nonzero and every other `χ_{λ + wt(b_j)}` vanishes. -/
def zSep : VermaGL.center n := ∏ j, sepFactor n lam m j

theorem chi_zSep_ne_zero : chi n lam (zSep n lam m) ≠ 0 := by
  classical
  rw [zSep, map_prod]
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  rw [sepFactor]
  split_ifs with h
  · simp only [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    exact sub_ne_zero.mpr h.choose_spec
  · rw [map_one]
    exact one_ne_zero

theorem chi_zSep_bad {k : Fin D} (hk : IsBad n lam m k) :
    chi n (lam + wtC n m k) (zSep n lam m) = 0 := by
  classical
  rw [zSep, map_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
  rw [sepFactor, dite_eq_left hk]
  simp only [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]

theorem chi_zSep_good {k : Fin D} (hk : ¬ IsBad n lam m k) :
    chi n (lam + wtC n m k) (zSep n lam m) = chi n lam (zSep n lam m) := by
  by_contra h
  exact hk ⟨zSep n lam m, Ne.symm h⟩

theorem chi_zSep_mem (k : Fin D) :
    chi n (lam + wtC n m k) (zSep n lam m) * (chi n lam (zSep n lam m) -
      chi n (lam + wtC n m k) (zSep n lam m)) = 0 := by
  by_cases hk : IsBad n lam m k
  · rw [chi_zSep_bad n lam m hk, zero_mul]
  · rw [chi_zSep_good n lam m hk, sub_self, mul_zero]

end Separate

/-! ## The main argument -/

section Main

variable (n : ℕ) (lam : Fin n → ℂ) {Wt : Type*} [AddCommGroup Wt] [Module ℂ Wt]
  (σ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ Wt)
  {D : ℕ} (b : Module.Basis (Fin D) ℂ Wt) (m : Fin D → Fin n → ℤ)
  (hb : ∀ k p, σ (unitE n (p, p)) (b k) = (m k p : ℂ) • b k)

theorem aeval_mem_center (z : VermaGL.center n) (p : Polynomial ℂ) :
    Polynomial.aeval (z : VermaGL.glU n) p ∈ VermaGL.center n := by
  have h := Polynomial.aeval_algHom_apply (VermaGL.center n).val z p
  rw [Subalgebra.coe_val] at h
  rw [h]
  exact (Polynomial.aeval z p).2

theorem aeval_X_sub_C (z : VermaGL.glU n) (c : ℂ) :
    Polynomial.aeval z (Polynomial.X - Polynomial.C c) = z - algebraMap ℂ (VermaGL.glU n) c := by
  rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]

include hb in
/-- `∏_{j ∈ T} (z - χ_{λ + wt(b_j)}(z))` kills `F_T` for downward closed `T`. -/
theorem env_prod_eq_zero (z : VermaGL.center n) : ∀ T : Finset (Fin D),
    (∀ i ∈ T, ∀ j, htZ n m j < htZ n m i → j ∈ T) →
      ∀ x ∈ FG n (rhoT n lam σ) (Gt n lam b) T,
        envelopingAction (rhoT n lam σ) (Polynomial.aeval (z : VermaGL.glU n)
          (∏ j ∈ T, (Polynomial.X - Polynomial.C (chi n (lam + wtC n m j) z)))) x = 0 := by
  classical
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
  intro hdown x hx
  rcases T.eq_empty_or_nonempty with rfl | hne
  · rw [FG_empty, Submodule.mem_bot] at hx
    rw [hx, map_zero]
  · obtain ⟨k, hk, hmax⟩ := T.exists_max_image (htZ n m) hne
    have hT : ∀ j, htZ n m j < htZ n m k → j ∈ T := hdown k hk
    have hdownT' : ∀ i ∈ T.erase k, ∀ j, htZ n m j < htZ n m i → j ∈ T.erase k := by
      intro i hi j hij
      have hiT := Finset.mem_of_mem_erase hi
      refine Finset.mem_erase.mpr ⟨fun hjk => ?_, hdown i hiT j hij⟩
      subst hjk
      have := hmax i hiT
      omega
    have hstep := FG_center_sub_mem n (rhoT n lam σ) (Gt n lam b) (fun j => lam + wtC n m j)
      (isWt_Gt n lam σ b m hb) (T := T) (k := k)
      (fun p q hqp => Gt_lower_mem n lam σ b m hb hk hT hqp) z.2 (chi_spec n _ z) hx
    rw [← Finset.prod_erase_mul T _ hk, map_mul, map_mul, Module.End.mul_apply, aeval_X_sub_C,
      map_sub, AlgHom.commutes, LinearMap.sub_apply, Module.algebraMap_end_apply]
    exact ih (T.erase k) (Finset.erase_ssubset hk) hdownT' _ hstep

theorem poly_factor (c d : ℂ) (h : d * (c - d) = 0) :
    (Polynomial.X - Polynomial.C (c - d)) * (Polynomial.X - Polynomial.C d) =
      Polynomial.X * (Polynomial.X - Polynomial.C c) := by
  have h' : Polynomial.C d * (Polynomial.C c - Polynomial.C d) = 0 := by
    rw [← Polynomial.C_sub, ← Polynomial.C_mul, h, Polynomial.C_0]
  rw [Polynomial.C_sub]
  linear_combination h'

include hb in
/-- `(z (z - χ_λ(z)))^D` kills `W ⊗ M⁻(λ)` for `z = zSep`. -/
theorem env_kill_all (x : Wt ⊗[ℂ] VermaGL.LowerVerma n lam) :
    envelopingAction (rhoT n lam σ) (Polynomial.aeval (zSep n lam m : VermaGL.glU n)
      ((Polynomial.X * (Polynomial.X - Polynomial.C (chi n lam (zSep n lam m)))) ^ D)) x = 0 := by
  classical
  have hprod : (Polynomial.X * (Polynomial.X - Polynomial.C (chi n lam (zSep n lam m)))) ^ D =
      (∏ j, (Polynomial.X - Polynomial.C (chi n lam (zSep n lam m) -
        chi n (lam + wtC n m j) (zSep n lam m)))) *
        ∏ j, (Polynomial.X - Polynomial.C (chi n (lam + wtC n m j) (zSep n lam m))) := by
    rw [← Finset.prod_mul_distrib,
      Finset.prod_congr rfl fun j _ => poly_factor _ _ (chi_zSep_mem n lam m j),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hx : x ∈ FG n (rhoT n lam σ) (Gt n lam b) Finset.univ := by
    rw [FP_univ]
    trivial
  have h0 := env_prod_eq_zero n lam σ b m hb (zSep n lam m) Finset.univ
    (fun _ _ j _ => Finset.mem_univ j) x hx
  rw [hprod, map_mul, map_mul, Module.End.mul_apply, h0, map_zero]

include hb in
/-- A vector of weight in `λ - Q₊ ∖ {λ}` killed by `(z - χ_λ(z))^D` vanishes. -/
theorem eq_zero_of_kill (hZ : VermaGL.IsZExtremal n lam) (N : ℕ) : ∀ T : Finset (Fin D),
    (∀ i ∈ T, ∀ j, htZ n m j < htZ n m i → j ∈ T) →
      ∀ w ∈ FG n (rhoT n lam σ) (Gt n lam b) T, ∀ ν : Fin n → ℂ,
        IsWt n (rhoT n lam σ) w ν → lam - ν ∈ VermaGL.posRootCone n → ν ≠ lam →
          envelopingAction (rhoT n lam σ) (((zSep n lam m : VermaGL.glU n) -
            algebraMap ℂ (VermaGL.glU n) (chi n lam (zSep n lam m))) ^ N) w = 0 →
            w = 0 := by
  classical
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
  intro hdown w hw ν hwν hcone hne hkill
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · rwa [FG_empty, Submodule.mem_bot] at hw
  · obtain ⟨k, hk, hmax⟩ := T.exists_max_image (htZ n m) hTne
    have hT : ∀ j, htZ n m j < htZ n m k → j ∈ T := hdown k hk
    have hdownT' : ∀ i ∈ T.erase k, ∀ j, htZ n m j < htZ n m i → j ∈ T.erase k := by
      intro i hi j hij
      have hiT := Finset.mem_of_mem_erase hi
      refine Finset.mem_erase.mpr ⟨fun hjk => ?_, hdown i hiT j hij⟩
      subst hjk
      have := hmax i hiT
      omega
    have hlow : ∀ p q : Fin n, q < p → rhoT n lam σ (unitE n (p, q)) (Gt n lam b k) ∈
        FG n (rhoT n lam σ) (Gt n lam b) (T.erase k) :=
      fun p q hqp => Gt_lower_mem n lam σ b m hb hk hT hqp
    have hsep := mem_FG_weight n (rhoT n lam σ) (Gt n lam b) (fun j => lam + wtC n m j)
      (isWt_Gt n lam σ b m hb) hlow hw hwν
    have hwT' : w ∈ FG n (rhoT n lam σ) (Gt n lam b) (T.erase k) := by
      by_cases hQ : ∃ l : List (Idx n), (∀ c ∈ l, c.1 < c.2) ∧
          lam + wtC n m k + shiftOf n l = ν
      · obtain ⟨l₀, hl₀, hν⟩ := hQ
        have hcone' : lam - (lam + wtC n m k) ∈ VermaGL.posRootCone n := by
          have : lam - (lam + wtC n m k) = (lam - ν) + shiftOf n l₀ := by
            rw [← hν]
            abel
          rw [this]
          exact AddSubmonoid.add_mem _ hcone (shiftOf_mem_posRootCone n hl₀)
        have hne' : lam + wtC n m k ≠ lam := by
          intro h
          apply hne
          have h1 : -(shiftOf n l₀) ∈ VermaGL.posRootCone n := by
            have : lam - ν = -(shiftOf n l₀) := by
              rw [← hν, h]
              abel
            rw [← this]
            exact hcone
          have h2 := posRootCone_antisymm n (shiftOf_mem_posRootCone n hl₀) h1
          rw [← hν, h, h2, add_zero]
        have hbad : IsBad n lam m k := exists_chi_ne_of_isZExtremal n hZ hcone' hne'
        have hd := chi_zSep_bad n lam m hbad
        have hpow := FG_center_pow_sub_mem n (rhoT n lam σ) (Gt n lam b)
          (fun j => lam + wtC n m j) (isWt_Gt n lam σ b m hb) hlow (zSep n lam m).2
          (chi_spec n _ (zSep n lam m)) (chi n lam (zSep n lam m)) N hw
        rw [hd] at hpow
        rw [hkill, zero_sub, neg_mem_iff] at hpow
        have hc : (0 - chi n lam (zSep n lam m)) ^ N ≠ 0 :=
          pow_ne_zero _ (by rw [zero_sub, neg_ne_zero]; exact chi_zSep_ne_zero n lam m)
        exact (Submodule.smul_mem_iff _ hc).mp hpow
      · have hQe : Submodule.span ℂ {v | ∃ l : List (Idx n), (∀ c ∈ l, c.1 < c.2) ∧
            lam + wtC n m k + shiftOf n l = ν ∧
              v = envelopingAction (rhoT n lam σ) (W n l) (Gt n lam b k)} = ⊥ := by
          rw [Submodule.span_eq_bot]
          rintro v ⟨l, hl, hν, rfl⟩
          exact absurd ⟨l, hl, hν⟩ hQ
        rw [hQe, sup_bot_eq] at hsep
        exact hsep
    exact ih (T.erase k) (Finset.erase_ssubset hk) hdownT' w hwT' ν hwν hcone hne hkill

end Main

/-! ## Projectivity -/

section Final

variable (n : ℕ)

theorem env_comm_central {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ V) {u : VermaGL.glU n}
    (hu : u ∈ VermaGL.center n) (Y : Matrix (Fin n) (Fin n) ℂ) (v : V) :
    ρ Y (envelopingAction ρ u v) = envelopingAction ρ u (ρ Y v) := by
  have hY : ρ Y = envelopingAction ρ (UniversalEnvelopingAlgebra.ι ℂ Y) :=
    (UniversalEnvelopingAlgebra.lift_ι_apply ℂ ρ Y).symm
  rw [hY, ← Module.End.mul_apply, ← map_mul, Subalgebra.mem_center_iff.mp hu, map_mul,
    Module.End.mul_apply]

theorem isWt_env_central {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ V) {u : VermaGL.glU n}
    (hu : u ∈ VermaGL.center n) {v : V} {μ : Fin n → ℂ} (hv : IsWt n ρ v μ) :
    IsWt n ρ (envelopingAction ρ u v) μ := by
  intro p
  rw [env_comm_central n ρ hu, hv p, map_smul]

theorem isWt_of_mem_span {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ V) {s : Set V} {μ : Fin n → ℂ} {a : V}
    (ha : a ∈ Submodule.span ℂ {v | v ∈ s ∧ IsWt n ρ v μ}) : IsWt n ρ a μ := by
  induction ha using Submodule.span_induction with
  | mem v hv => exact hv.2
  | zero => intro p; rw [map_zero, smul_zero]
  | add x y _ _ hx hy => intro p; rw [map_add, hx p, hy p, smul_add]
  | smul c x _ hx => intro p; rw [map_smul, hx p, smul_comm]

theorem env_equivariant {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
    [Module ℂ V'] (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ V)
    (τ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ V') (f : V →ₗ[ℂ] V')
    (hf : ∀ Y t, f (ρ Y t) = τ Y (f t)) (u : VermaGL.glU n) (t : V) :
    f (envelopingAction ρ u t) = envelopingAction τ u (f t) := by
  have hu : u ∈ Submodule.span ℂ (Set.range (basisU n)) := by
    rw [(basisU n).span_eq]
    trivial
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨α, rfl⟩ := hu
    rw [basisU_apply]
    induction (Kostant.expand (bsList n) α) with
    | nil => rw [W_nil, map_one, map_one, Module.End.one_apply, Module.End.one_apply]
    | cons c l ih => rw [env_W_cons, env_W_cons, hf, ih]
  | zero => rw [map_zero, map_zero, LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add,
      hx, hy]
  | smul a x _ hx => rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
      map_smul, hx]

theorem rootOf_ne_zero {p q : Fin n} (hqp : q < p) : rootOf n (p, q) ≠ 0 := by
  intro h
  have := congrFun h p
  simp [rootOf, ne_of_gt hqp] at this

end Final

universe uW uN

/-- **Projectivity of lower Verma modules.** -/
theorem lowerVermaProjective : VermaGL.LowerVermaProjectiveStatement.{uW, uN} := by
  intro n lam hZ Wt _ _ _ σ hσ N _ _ τ f hf hfeq x hxlow hxdiag
  classical
  obtain ⟨D, b, m, hb⟩ := exists_weight_basis n σ hσ
  have hfeq' : ∀ Y t, f (rhoT n lam σ Y t) = τ Y (f t) := hfeq
  have hxw : IsWt n τ x lam := hxdiag
  have hxlow' : ∀ p q : Fin n, q < p → τ (unitE n (p, q)) x = 0 := hxlow
  -- a preimage of weight `λ`
  obtain ⟨t₀, ht₀w, ht₀x⟩ : ∃ t₀, IsWt n (rhoT n lam σ) t₀ lam ∧ f t₀ = x := by
    obtain ⟨t₁, rfl⟩ := hf x
    set s := gensG n (rhoT n lam σ) (Gt n lam b) Finset.univ with hsdef
    have hs : ∀ v ∈ s, ∃ μ, IsWt n (rhoT n lam σ) v μ := fun v hv =>
      isWt_gensG n _ _ _ (isWt_Gt n lam σ b m hb) hv
    have ht₁ : t₁ ∈ Submodule.span ℂ s := by
      have h := FP_univ n lam σ b
      rw [FG] at h
      rw [h]
      trivial
    have hle : Submodule.span ℂ s ≤
        Submodule.span ℂ {v | v ∈ s ∧ IsWt n (rhoT n lam σ) v lam} ⊔
          Submodule.span ℂ {v | v ∈ s ∧ ¬ IsWt n (rhoT n lam σ) v lam} := by
      refine Submodule.span_le.mpr fun v hv => ?_
      by_cases h : IsWt n (rhoT n lam σ) v lam
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨hv, h⟩)
      · exact Submodule.mem_sup_right (Submodule.subset_span ⟨hv, h⟩)
    obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.mp (hle ht₁)
    have haw : IsWt n (rhoT n lam σ) a lam := isWt_of_mem_span n _ ha
    refine ⟨a, haw, ?_⟩
    have hfa : IsWt n τ (f a) lam := fun p => by rw [← hfeq', haw p, map_smul]
    have hfa'w : IsWt n τ (f a') lam := fun p => by
      have h1 := hxw p
      rw [map_add, map_add, hfa p, smul_add] at h1
      exact add_left_cancel h1
    have hfa' : f a' ∈ Submodule.span ℂ
        (f '' {v | v ∈ s ∧ ¬ IsWt n (rhoT n lam σ) v lam}) := by
      rw [← Submodule.map_span]
      exact Submodule.mem_map_of_mem ha'
    have hsep := mem_span_wt n τ (fun y hy => by
        obtain ⟨v, hv, rfl⟩ := hy
        obtain ⟨μ, hμ⟩ := hs v hv.1
        exact ⟨μ, fun p => by rw [← hfeq', hμ p, map_smul]⟩) hfa' hfa'w
    have hbot : Submodule.span ℂ {y | y ∈ f '' {v | v ∈ s ∧ ¬ IsWt n (rhoT n lam σ) v lam} ∧
        IsWt n τ y lam} = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro y ⟨⟨v, hv, rfl⟩, hyw⟩
      by_contra hne
      obtain ⟨μ, hμ⟩ := hs v hv.1
      have hfμ : IsWt n τ (f v) μ := fun p => by rw [← hfeq', hμ p, map_smul]
      have := isWt_unique n τ hfμ hyw hne
      subst this
      exact hv.2 hμ
    rw [hbot, Submodule.mem_bot] at hsep
    rw [map_add, hsep, add_zero]
  -- the separating central element and the projector
  set z := zSep n lam m with hz
  set c₀ := chi n lam z with hc₀
  have hc₀ne : c₀ ≠ 0 := chi_zSep_ne_zero n lam m
  have hcop : IsCoprime (Polynomial.X : Polynomial ℂ) (Polynomial.X - Polynomial.C c₀) := by
    refine ⟨Polynomial.C c₀⁻¹, -Polynomial.C c₀⁻¹, ?_⟩
    have h : Polynomial.C c₀⁻¹ * Polynomial.C c₀ = 1 := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hc₀ne, Polynomial.C_1]
    linear_combination h
  obtain ⟨A, B, hAB⟩ := hcop.pow (m := D + 1) (n := D + 1)
  set u : VermaGL.glU n := Polynomial.aeval (z : VermaGL.glU n) (A * Polynomial.X ^ (D + 1))
    with hu
  have huc : u ∈ VermaGL.center n := aeval_mem_center n z _
  refine ⟨envelopingAction (rhoT n lam σ) u t₀, ?_, ?_, ?_⟩
  · -- `f t = x`
    rw [env_equivariant n _ τ f hfeq', ht₀x, hu, ← Polynomial.aeval_algHom_apply,
      aeval_apply_of_eigen (env_singular n τ lam hxlow' hxw z)]
    have he := congrArg (Polynomial.eval c₀) hAB
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_sub, Polynomial.eval_C, sub_self, Polynomial.eval_one] at he
    rw [zero_pow (Nat.succ_ne_zero D), mul_zero, add_zero] at he
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, he, one_smul]
  · -- killed by the strictly lower triangular matrix units
    intro p q hqp
    change rhoT n lam σ (unitE n (p, q)) (envelopingAction (rhoT n lam σ) u t₀) = 0
    rw [env_comm_central n _ huc]
    set v := rhoT n lam σ (unitE n (p, q)) t₀
    have hvw : IsWt n (rhoT n lam σ) v (lam + rootOf n (p, q)) :=
      isWt_unitE n _ ht₀w (p, q)
    have hww := isWt_env_central n (rhoT n lam σ) huc hvw
    refine eq_zero_of_kill n lam σ b m hb hZ (D + 1) Finset.univ
      (fun _ _ j _ => Finset.mem_univ j) _ (by rw [FP_univ]; trivial) _ hww ?_ ?_ ?_
    · have h : lam - (lam + rootOf n (p, q)) = Pi.single q 1 - Pi.single p 1 := by
        rw [rootOf]
        abel
      rw [h]
      exact AddSubmonoid.subset_closure ⟨q, p, hqp, rfl⟩
    · intro h
      apply rootOf_ne_zero n hqp
      have := congrArg (fun g => g - lam) h
      simpa using this
    · have hpoly : (Polynomial.X - Polynomial.C c₀) ^ (D + 1) * (A * Polynomial.X ^ (D + 1)) =
          (A * (Polynomial.X * (Polynomial.X - Polynomial.C c₀))) *
            (Polynomial.X * (Polynomial.X - Polynomial.C c₀)) ^ D := by
        rw [mul_pow]
        ring
      have hpow : ((z : VermaGL.glU n) - algebraMap ℂ (VermaGL.glU n) c₀) ^ (D + 1) =
          Polynomial.aeval (z : VermaGL.glU n) ((Polynomial.X - Polynomial.C c₀) ^ (D + 1)) := by
        rw [map_pow, aeval_X_sub_C]
      rw [← Module.End.mul_apply, ← map_mul, hpow, hu, ← map_mul, hpoly, map_mul, map_mul,
        Module.End.mul_apply, env_kill_all n lam σ b m hb v, map_zero]
  · -- weight `λ`
    exact isWt_env_central n (rhoT n lam σ) huc ht₀w

end Langlands.Archimedean.VermaPBW
