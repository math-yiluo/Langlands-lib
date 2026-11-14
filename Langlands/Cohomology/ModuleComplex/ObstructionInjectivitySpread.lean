import Langlands.Cohomology.ModuleComplex.ObstructionConeOpenProof

/-! # Spreading injectivity of an obstruction map from a flat field point

For a bounded complex `C` of flat modules over a noetherian ring `A` with finite cohomology and
a cocycle `z ∈ C² ⊗ Q`, `InjVanishes C d z M` says that `ψ ↦ [ψ_* z] ∈ H²(C ⊗ M)` is
injective on `Hom(Q, M)`. If this holds at a field `k` that is flat over `A`, it holds for every
module on which some `g` with nonzero image in `k` acts bijectively.
-/

set_option autoImplicit false

universe u

open TensorProduct

noncomputable section

namespace Langlands.Cohomology.ModuleComplex.ObstructionInjectivity

open ObstructionCone

variable {A : Type u} [CommRing A]

/-- With coefficients in `M`, the obstruction map `ψ ↦ [ψ_* z]` is injective: if `ψ_* z` is a
coboundary `-(d c)`, then `ψ = 0`. -/
def InjVanishes (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module A (C i)]
    (d : ∀ i, C i →ₗ[A] C (i + 1)) {Q : Type u} [AddCommGroup Q] [Module A Q]
    (z : C 2 ⊗[A] Q) (M : Type u) [AddCommGroup M] [Module A M] : Prop :=
  ∀ (c : C 1 ⊗[A] M) (ψ : Q →ₗ[A] M), (d 1).rTensor M c + ψ.lTensor (C 2) z = 0 → ψ = 0

section Transfer

variable {K C : ℕ → Type u} [∀ i, AddCommGroup (K i)] [∀ i, Module A (K i)]
  [∀ i, AddCommGroup (C i)] [∀ i, Module A (C i)]
  {dK : ∀ i, K i →ₗ[A] K (i + 1)} {d : ∀ i, C i →ₗ[A] C (i + 1)} {φ : ∀ i, K i →ₗ[A] C i}
  (hφ : ∀ i, d i ∘ₗ φ i = φ (i + 1) ∘ₗ dK i)
  {Q : Type u} [AddCommGroup Q] [Module A Q] (z : C 2 ⊗[A] Q) (zh : K 2 ⊗[A] Q)
  (w : C 1 ⊗[A] Q) (hφzh : (φ 2).rTensor Q zh = z + (d 1).rTensor Q w)

include hφ hφzh in
/-- Injectivity for the original complex gives injectivity for a model. -/
lemma injVanishes_model (M : Type u) [AddCommGroup M] [Module A M]
    (h : InjVanishes C d z M) : InjVanishes K dK zh M := by
  intro ch ψ hch
  apply h ((φ 1).rTensor M ch + ψ.lTensor (C 1) w)
  have h1 := congrArg ((φ 2).rTensor M) hch
  rw [map_add, map_zero, ← Transfer.rTensor_chain hφ M, Transfer.rTensor_lTensor, hφzh,
    map_add, ← Transfer.rTensor_lTensor] at h1
  rw [map_add, ← h1]
  abel

include hφzh in
/-- Injectivity for a model gives injectivity for the original complex, given injectivity on
second cohomology after `⊗ M`. -/
lemma injVanishes_of_model (hzh : (dK 2).rTensor Q zh = 0) (M : Type u) [AddCommGroup M]
    [Module A M] (hM : Transfer.CohIso K C dK d φ M) (h : InjVanishes K dK zh M) :
    InjVanishes C d z M := by
  intro c ψ hc
  have hcyc : (dK 2).rTensor M (ψ.lTensor (K 2) zh) = 0 := by
    rw [Transfer.rTensor_lTensor, hzh, map_zero]
  have hbd : (φ 2).rTensor M (ψ.lTensor (K 2) zh) ∈ LinearMap.range ((d 1).rTensor M) := by
    refine ⟨ψ.lTensor (C 1) w - c, ?_⟩
    rw [Transfer.rTensor_lTensor, hφzh, map_add, map_sub, ← Transfer.rTensor_lTensor]
    rw [eq_neg_of_add_eq_zero_left hc]
    abel
  obtain ⟨c₀, hc₀⟩ := hM.1 1 _ hcyc hbd
  apply h (-c₀)
  rw [map_neg, hc₀, neg_add_cancel]

end Transfer

section Model

variable {K : ℕ → Type u} [∀ i, AddCommGroup (K i)] [∀ i, Module A (K i)]
  (dK : ∀ i, K i →ₗ[A] K (i + 1))
  {Q G₀ G₁ : Type u} [AddCommGroup Q] [Module A Q]
  [AddCommGroup G₀] [Module A G₀] [AddCommGroup G₁] [Module A G₁]
  (p : G₀ →ₗ[A] Q) (g : G₁ →ₗ[A] G₀) (z₀ : K 2 ⊗[A] G₀)

/-- The first map of the injectivity model: degree-one cocycles of the model enter the
middle term with zero linear form. -/
def aZ : LinearMap.ker (dK 1) →ₗ[A] (Module.Dual A G₀ × K 1) :=
  LinearMap.prod 0 (LinearMap.ker (dK 1)).subtype

/-- The first map with coefficients in `M`. -/
def aZM (M : Type u) [AddCommGroup M] [Module A M] :
    LinearMap.ker (dK 1) ⊗[A] M →ₗ[A] ((G₀ →ₗ[A] M) × (K 1 ⊗[A] M)) :=
  LinearMap.prod 0 ((LinearMap.ker (dK 1)).subtype.rTensor M)

lemma aZ_comp : Model.b dK g z₀ ∘ₗ aZ (G₀ := G₀) dK = 0 := by
  refine LinearMap.ext fun x => ?_
  have hx : aZ (G₀ := G₀) dK x = (0, (x : K 1)) := rfl
  rw [LinearMap.comp_apply, hx, Model.b_apply, LinearMap.zero_apply]
  refine Prod.ext ?_ ?_
  · simp
  · rw [show (0 : Module.Dual A G₀).lTensor (K 2) z₀ = 0 by simp, map_zero, zero_add]
    exact x.2

variable [Module.Finite A G₀] [Module.Projective A G₀] [Module.Finite A G₁]
  [Module.Projective A G₁]

lemma ladder_aZ (M : Type u) [AddCommGroup M] [Module A M] :
    (Model.termEquiv M G₀ (K 1)).toLinearMap ∘ₗ (aZ (G₀ := G₀) dK).rTensor M =
      aZM (G₀ := G₀) dK M ∘ₗ (LinearEquiv.refl A _).toLinearMap := by
  apply TensorProduct.ext'
  intro x m
  simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe, aZ, aZM,
    LinearMap.prod_apply, LinearEquiv.refl_apply]
  rw [Model.termEquiv_tmul]
  refine Prod.ext ?_ ?_
  · ext y
    simp
  · rfl

lemma exact_rTensor_iff (M : Type u) [AddCommGroup M] [Module A M] :
    Function.Exact ((aZ (G₀ := G₀) dK).rTensor M) ((Model.b dK g z₀).rTensor M) ↔
      Function.Exact (aZM (G₀ := G₀) dK M) (Model.bM dK g z₀ M) :=
  (Function.Exact.iff_of_ladder_linearEquiv (ladder_aZ dK M).symm
    (Model.ladder_b dK g z₀ M).symm).symm

end Model

section Exactness

variable {K : ℕ → Type u} [∀ i, AddCommGroup (K i)] [∀ i, Module A (K i)]
  (dK : ∀ i, K i →ₗ[A] K (i + 1))
  {Q G₀ G₁ : Type u} [AddCommGroup Q] [Module A Q]
  [AddCommGroup G₀] [Module A G₀] [AddCommGroup G₁] [Module A G₁]
  (p : G₀ →ₗ[A] Q) (g : G₁ →ₗ[A] G₀) (z₀ : K 2 ⊗[A] G₀) (zh : K 2 ⊗[A] Q)
  (hz₀ : p.lTensor (K 2) z₀ = zh)

include hz₀ in
/-- Middle exactness of the model with coefficients in `M` gives injectivity. -/
lemma injVanishes_of_exact (hp : Function.Surjective p) (hpg : p ∘ₗ g = 0)
    (M : Type u) [AddCommGroup M] [Module A M]
    (hex : Function.Exact (aZM (G₀ := G₀) dK M) (Model.bM dK g z₀ M)) :
    InjVanishes K dK zh M := by
  intro ch ψ hch
  have h0 : Model.bM dK g z₀ M (ψ ∘ₗ p, ch) = 0 := by
    rw [Model.bM_apply, LinearMap.comp_assoc, hpg, LinearMap.comp_zero,
      LinearMap.lTensor_comp, LinearMap.comp_apply, hz₀, add_comm, hch]
    rfl
  obtain ⟨x, hx⟩ := (hex _).mp h0
  have h1 : (0 : G₀ →ₗ[A] M) = ψ ∘ₗ p := congrArg Prod.fst hx
  ext q
  obtain ⟨y, rfl⟩ := hp q
  have := LinearMap.congr_fun h1 y
  simpa using this.symm

include hz₀ in
/-- At a flat coefficient module, injectivity gives middle exactness of the model. -/
lemma exact_of_injVanishes (hp : Function.Surjective p) (hgp : Function.Exact g p)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Flat A M]
    (h : InjVanishes K dK zh M) :
    Function.Exact (aZM (G₀ := G₀) dK M) (Model.bM dK g z₀ M) := by
  have hpg : p ∘ₗ g = 0 := hgp.linearMap_comp_eq_zero
  have hlt : ∀ ψ : Q →ₗ[A] M, (ψ ∘ₗ p).lTensor (K 2) z₀ = ψ.lTensor (K 2) zh := by
    intro ψ
    rw [LinearMap.lTensor_comp, LinearMap.comp_apply, hz₀]
  have hZ : Function.Exact ((LinearMap.ker (dK 1)).subtype.rTensor M) ((dK 1).rTensor M) :=
    Module.Flat.rTensor_exact M (LinearMap.exact_subtype_ker_map (dK 1))
  intro y
  obtain ⟨w, γ⟩ := y
  constructor
  · intro hy
    rw [Model.bM_apply] at hy
    have hy₁ : w ∘ₗ g = 0 := congrArg Prod.fst hy
    have hy₂ : w.lTensor (K 2) z₀ + (dK 1).rTensor M γ = 0 := congrArg Prod.snd hy
    have hle : LinearMap.range g ≤ LinearMap.ker w := by
      rintro _ ⟨x, rfl⟩
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hy₁, LinearMap.zero_apply]
    let ψ : Q →ₗ[A] M :=
      (LinearMap.range g).liftQ w hle ∘ₗ (hgp.linearEquivOfSurjective hp).symm.toLinearMap
    have hψ : ψ ∘ₗ p = w := by
      ext x
      simp [ψ, Function.Exact.linearEquivOfSurjective_symm_apply]
    have hc : (dK 1).rTensor M γ + ψ.lTensor (K 2) zh = 0 := by
      have h1 := hlt ψ
      rw [hψ] at h1
      rw [← h1]
      exact (add_comm _ _).trans hy₂
    have hψ0 : ψ = 0 := h γ ψ hc
    have hw : w = 0 := by rw [← hψ, hψ0, LinearMap.zero_comp]
    have hγ : (dK 1).rTensor M γ = 0 := by
      rw [hψ0, LinearMap.lTensor_zero, LinearMap.zero_apply, add_zero] at hc
      exact hc
    obtain ⟨x, hx⟩ := (hZ γ).mp hγ
    refine ⟨x, ?_⟩
    rw [hw, ← hx]
    rfl
  · rintro ⟨x, hx⟩
    have hx' : aZM (G₀ := G₀) dK M x = (0, (LinearMap.ker (dK 1)).subtype.rTensor M x) := rfl
    rw [← hx, hx', Model.bM_apply]
    refine Prod.ext ?_ ?_
    · simp
    · simp only [Prod.snd_zero]
      rw [show (0 : G₀ →ₗ[A] M).lTensor (K 2) z₀ = 0 by simp, zero_add,
        ← LinearMap.comp_apply ((dK 1).rTensor M), ← LinearMap.rTensor_comp]
      have : dK 1 ∘ₗ (LinearMap.ker (dK 1)).subtype = 0 := by
        ext v
        exact v.2
      rw [this, LinearMap.rTensor_zero, LinearMap.zero_apply]

end Exactness

/-- Spreading of injectivity of the obstruction map from a flat field point. Let `A` be
noetherian, `C` a bounded complex of flat `A`-modules with finite cohomology, `Q` a finite
`A`-module and `z ∈ C² ⊗ Q` a cocycle. If `InjVanishes C d z k` holds for a field `k` that is
flat over `A`, there is `g : A` with nonzero image in `k` such that `InjVanishes C d z M` holds
for every `A`-module `M` on which multiplication by `g` is bijective. -/
theorem exists_injVanishes_spread [IsNoetherianRing A]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module A (C i)] [∀ i, Module.Flat A (C i)]
    (d : ∀ i, C i →ₗ[A] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin0 : Module.Finite A (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite A
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    {Q : Type u} [AddCommGroup Q] [Module A Q] [Module.Finite A Q]
    (z : C 2 ⊗[A] Q) (hz : (d 2).rTensor Q z = 0)
    (k : Type u) [Field k] [Algebra A k] [Module.Flat A k]
    (hk : InjVanishes C d z k) :
    ∃ g : A, algebraMap A k g ≠ 0 ∧ ∀ (M : Type u) [AddCommGroup M] [Module A M],
      Function.Bijective (fun m : M => g • m) → InjVanishes C d z M := by
  obtain ⟨K, _, _, _, _, dK, hdKK, hKbdd, φ, hφ, h0inj, h0surj, hinj, hsurj⟩ :=
    boundedFlatComplexProjective A C d hdd n hbdd hfin0 hfin
  have hCoh : ∀ (N : Type u) [AddCommGroup N] [Module A N], Transfer.CohIso K C dK d φ N :=
    fun N _ _ => QuasiIsoModule.rTensor_quasiIso K dK hdKK C d hdd n hKbdd hbdd φ hφ h0inj
      h0surj hinj hsurj N
  obtain ⟨zh, w, -, -, hzh, hφzh, -, -⟩ :=
    Transfer.exists_transfer hφ (hCoh Q) (hCoh Q) (0 : Q →ₗ[A] Q) (0 : C 1 ⊗[A] Q) z
      (by rw [map_zero, LinearMap.lTensor_zero, LinearMap.zero_apply]) hz
  have hKk : InjVanishes K dK zh k := injVanishes_model hφ z zh w hφzh k hk
  -- a finite free presentation of `Q`
  obtain ⟨n₀, p, hp⟩ := Module.Finite.exists_fin' A Q
  obtain ⟨n₁, g', hg'⟩ := Module.Finite.exists_fin' A (LinearMap.ker p)
  let g : (Fin n₁ → A) →ₗ[A] (Fin n₀ → A) := (LinearMap.ker p).subtype ∘ₗ g'
  have hgp : Function.Exact g p := by
    rw [LinearMap.exact_iff, LinearMap.range_comp, LinearMap.range_eq_top.mpr hg',
      Submodule.map_top, Submodule.range_subtype]
  have hpg : p ∘ₗ g = 0 := hgp.linearMap_comp_eq_zero
  obtain ⟨z₀, hz₀⟩ := LinearMap.lTensor_surjective (K 2) hp zh
  have hba := aZ_comp (G₀ := Fin n₀ → A) dK g z₀
  have hexk : Function.Exact ((aZ (G₀ := Fin n₀ → A) dK).baseChange k)
      ((Model.b dK g z₀).baseChange k) :=
    exact_baseChange_of_exact_rTensor _ _ k ((exact_rTensor_iff dK g z₀ k).mpr
      (exact_of_injVanishes dK p g z₀ zh hz₀ hp hgp k hKk))
  obtain ⟨g₀, hg₀, hspread⟩ := ExactSpread.exists_exact_rTensor_spread _ _ hba k hexk
  refine ⟨g₀, hg₀, fun M _ _ hM => ?_⟩
  have hKM := injVanishes_of_exact dK p g z₀ zh hz₀ hp hpg M
    ((exact_rTensor_iff dK g z₀ M).mp (hspread M hM))
  exact injVanishes_of_model z zh w hφzh hzh M (hCoh M) hKM

section Reduction

variable {P : Type u} [CommRing P]

/-- The reduction isomorphism `(A ⊗[P] N) ⊗[A] M ≃ M ⊗[P] N`, `(a ⊗ n) ⊗ m ↦ (a • m) ⊗ n`. -/
def red (A : Type u) [CommRing A] [Algebra P A] (N : Type u) [AddCommGroup N] [Module P N]
    (M : Type u) [AddCommGroup M] [Module A M] [Module P M] [IsScalarTower P A M] :
    (A ⊗[P] N) ⊗[A] M ≃ₗ[A] M ⊗[P] N :=
  TensorProduct.comm A (A ⊗[P] N) M ≪≫ₗ AlgebraTensorModule.cancelBaseChange P A A M N

variable {A : Type u} [CommRing A] [Algebra P A]
  {N N' : Type u} [AddCommGroup N] [Module P N] [AddCommGroup N'] [Module P N']
  {M : Type u} [AddCommGroup M] [Module A M] [Module P M] [IsScalarTower P A M]
  {Q : Type u} [AddCommGroup Q] [Module A Q] [Module P Q] [IsScalarTower P A Q]

lemma red_tmul (a : A) (n : N) (m : M) :
    red A N M ((a ⊗ₜ[P] n) ⊗ₜ[A] m) = (a • m) ⊗ₜ[P] n :=
  rfl

/-- `red` intertwines a base-changed map with the map tensored on the left. -/
lemma red_rTensor_baseChange (v : N →ₗ[P] N') (x : (A ⊗[P] N) ⊗[A] M) :
    red A N' M ((v.baseChange A).rTensor M x) = v.lTensor M (red A N M x) := by
  induction x using TensorProduct.inductionOn with
  | tmul y m =>
    induction y using TensorProduct.inductionOn with
    | tmul a n =>
      rw [LinearMap.rTensor_tmul, LinearMap.baseChange_tmul, red_tmul, red_tmul,
        LinearMap.lTensor_tmul]
    | add y y' hy hy' =>
      rw [TensorProduct.add_tmul, map_add, map_add, hy, hy', map_add, map_add]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]

/-- `red` intertwines a map of coefficients tensored on the left with the same map tensored on
the right. -/
lemma red_lTensor (ψ : Q →ₗ[A] M) (x : (A ⊗[P] N) ⊗[A] Q) :
    red A N M (ψ.lTensor (A ⊗[P] N) x) = (ψ.restrictScalars P).rTensor N (red A N Q x) := by
  induction x using TensorProduct.inductionOn with
  | tmul y q =>
    induction y using TensorProduct.inductionOn with
    | tmul a n =>
      rw [LinearMap.lTensor_tmul, red_tmul, red_tmul, LinearMap.rTensor_tmul,
        LinearMap.restrictScalars_apply, map_smul]
    | add y y' hy hy' =>
      rw [TensorProduct.add_tmul, map_add, map_add, hy, hy', map_add, map_add]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]

variable (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module P (C i)]
  (d : ∀ i, C i →ₗ[P] C (i + 1))

/-- The reduced form of `InjVanishes`, over the base ring `P` with coefficients on the left: for
`zP ∈ Q ⊗[P] C 2`, if `d c + ψ_* zP = 0` with `c ∈ M ⊗[P] C 1` and `ψ : Q → M`, then `ψ = 0`. -/
def InjVanishesRed {Q : Type u} [AddCommGroup Q] [Module P Q] (zP : Q ⊗[P] C 2) (M : Type u)
    [AddCommGroup M] [Module P M] : Prop :=
  ∀ (c : M ⊗[P] C 1) (ψ : Q →ₗ[P] M), (d 1).lTensor M c + ψ.rTensor (C 2) zP = 0 → ψ = 0

/-- The cocycle equation for the base-changed complex, rewritten over `P` with `red`. -/
lemma exists_baseChange_iff (z : (A ⊗[P] C 2) ⊗[A] Q) (ψ : Q →ₗ[A] M) :
    (∃ c : (A ⊗[P] C 1) ⊗[A] M,
        ((d 1).baseChange A).rTensor M c + ψ.lTensor (A ⊗[P] C 2) z = 0) ↔
      ∃ c : M ⊗[P] C 1,
        (d 1).lTensor M c + (ψ.restrictScalars P).rTensor (C 2) (red A (C 2) Q z) = 0 := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨red A (C 1) M c, ?_⟩
    rw [← red_rTensor_baseChange, ← red_lTensor, ← map_add, hc, map_zero]
  · rintro ⟨c, hc⟩
    refine ⟨(red A (C 1) M).symm c, (red A (C 2) M).injective ?_⟩
    rw [map_add, red_rTensor_baseChange, red_lTensor, LinearEquiv.apply_symm_apply, hc,
      map_zero]

/-- For `P → A` surjective, `InjVanishes` for the base change of `C` to `A` is the reduced
condition `InjVanishesRed` for `red z ∈ Q ⊗[P] C 2`; in particular it depends only on `red z`. -/
lemma injVanishes_baseChange_iff (hπ : Function.Surjective (algebraMap P A))
    (z : (A ⊗[P] C 2) ⊗[A] Q) (M : Type u) [AddCommGroup M] [Module A M] [Module P M]
    [IsScalarTower P A M] :
    InjVanishes (fun i => A ⊗[P] C i) (fun i => (d i).baseChange A) z M ↔
      InjVanishesRed C d (red A (C 2) Q z) M := by
  constructor
  · intro h c ψ hc
    let ψA : Q →ₗ[A] M := ψ.extendScalarsOfSurjective hπ
    have hres : ψA.restrictScalars P = ψ := LinearMap.ext fun _ => rfl
    obtain ⟨c₀, hc₀⟩ := (exists_baseChange_iff C d z ψA).mpr ⟨c, by rw [hres]; exact hc⟩
    have h0 : ψA = 0 := h c₀ ψA hc₀
    rw [← hres, h0, LinearMap.restrictScalars_zero]
  · intro h c ψ hc
    obtain ⟨c', hc'⟩ := (exists_baseChange_iff C d z ψ).mp ⟨c, hc⟩
    have h0 : ψ.restrictScalars P = 0 := h c' _ hc'
    ext x
    exact LinearMap.congr_fun h0 x

/-- `red` transfers cocycles between two base changes with the same reduction. -/
lemma rTensor_baseChange_eq_zero_of_red {A₁ : Type u} [CommRing A₁] [Algebra P A₁]
    [Module A₁ Q] [IsScalarTower P A₁ Q] (v : N →ₗ[P] N') (z : (A ⊗[P] N) ⊗[A] Q)
    (z₁ : (A₁ ⊗[P] N) ⊗[A₁] Q) (hred : red A N Q z = red A₁ N Q z₁)
    (hz : (v.baseChange A).rTensor Q z = 0) : (v.baseChange A₁).rTensor Q z₁ = 0 := by
  apply (red A₁ N' Q).injective
  rw [red_rTensor_baseChange, ← hred, ← red_rTensor_baseChange, hz, map_zero, map_zero]

end Reduction

end Langlands.Cohomology.ModuleComplex.ObstructionInjectivity
