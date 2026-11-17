import Langlands.Algebra.MixedChartRing
import Langlands.Algebra.TorusChartExistence

/-! # Existence of a chart for subgroups of multiplicative type around a field point -/

noncomputable section

universe u

open TensorProduct

namespace Langlands.Algebra.MixedChartExistence

open HopfPointExtension HopfPointBridge HopfPointTwist FiniteBialgebraHom MixedChartAlgebra
  HopfPointClosedLocus LatticeConfiguration MixedLatticeConfiguration InvariantPrincipalOpen
  MixedHopfPointRigidity HopfPointWeightWindow HopfPointWeightLocus MixedChartRing
  TorusChartExistence

section Lattice

variable {r : Type*} [Fintype r] [DecidableEq r] {F : Type*} [AddCommGroup F] [Fintype F]

/-- Bounded sums of a box of `ℤ^r × F` lie in a larger box. -/
theorem boundedSums_mbox_subset (n : ℕ) : ∀ N : ℕ,
    boundedSums (mbox r F n : Set ((r → ℤ) × F)) N ⊆ (mbox r F (N * n) : Set ((r → ℤ) × F))
  | 0 => by
    rintro x rfl
    simp [mem_mbox]
  | N + 1 => by
    rintro x (hx | ⟨y, hy, z, hz, rfl⟩)
    · have := boundedSums_mbox_subset n N hx
      simp only [Finset.mem_coe, mem_mbox] at this ⊢
      intro j
      have := this j
      have : (N : ℤ) * n ≤ ((N + 1 : ℕ) : ℤ) * n := by push_cast; nlinarith
      push_cast at *
      linarith
    · have hy' := boundedSums_mbox_subset n N hy
      simp only [Finset.mem_coe, mem_mbox] at hy' hz ⊢
      intro j
      have h1 := hy' j
      have h2 := hz j
      have h3 := abs_add_le (y.1 j) (z.1 j)
      simp only [Prod.fst_add, Pi.add_apply]
      push_cast at *
      nlinarith

omit [AddCommGroup F] in
/-- A finite subset of `ℤ^r × F` lies in some box. -/
theorem exists_mbox (T : Finset ((r → ℤ) × F)) :
    ∃ n : ℕ, (T : Set ((r → ℤ) × F)) ⊆ (mbox r F n : Set _) := by
  classical
  obtain ⟨n, hn⟩ := exists_box (T.image Prod.fst)
  refine ⟨n, fun χ hχ => ?_⟩
  rw [Finset.mem_coe, mem_mbox]
  have : χ.1 ∈ (box r n : Set (r → ℤ)) :=
    hn (Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.fst hχ))
  exact mem_box.mp this

end Lattice

section Window

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [HopfAlgebra R A]
  [Algebra.FinitePresentation R A] (r : Type u) [Fintype r] [DecidableEq r]
  (F : Type u) [AddCommGroup F] [Fintype F] (m : ℕ) [NeZero m]
  {σ' : Type u} (gen : σ' → A) (n : ℕ) (V : Submodule R A) (δ : V →ₗ[R] V ⊗[R] A) (N₀ : ℕ)

/-- A chart datum whose window extension has its weights in the box, with reduction
modulo `m` injective on bounded sums of the box. -/
structure WindowDatum extends Datum R A r F m gen n where
  weights : WeightsIn δ toDatum.α (mbox r F n : Set ((r → ℤ) × F))
  injOn : Set.InjOn (mred r F m) (boundedSums (mbox r F n : Set ((r → ℤ) × F)) N₀)

end Window

section Extension

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [HopfAlgebra R A]
  [Algebra.FinitePresentation R A] {L : Type u} [AddCommGroup L] [Fintype L]

/-- The point of `W` attached to a Hopf point of `D(L)`. -/
theorem exists_point_of_hopfPoint {K : Type u} [CommRing K] [Algebra R K]
    {β : A →ₐ[R] AddMonoidAlgebra K L}
    (hβ : IsHopfPoint β) : ∃ y : W R A L →ₐ[R] K, pointOf R A L y = β := by
  refine ⟨(homEquiv R A (AddMonoidAlgebra R L) K).symm
    ⟨TorusChartRing.ofGroupAlgebra β, TorusChartRing.isHopfPoint_ofGroupAlgebra hβ⟩, ?_⟩
  rw [pointOf, ← univ_point, Equiv.apply_symm_apply, TorusChartRing.toGroupAlgebra_ofGroupAlgebra]

end Extension

section Window2

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [HopfAlgebra R A]
  [Algebra.FinitePresentation R A] {r : Type u} [Fintype r] [DecidableEq r]
  {F : Type u} [AddCommGroup F] [Fintype F] {m : ℕ} [NeZero m]
  {K : Type u} [Field K] [Algebra R K]
  {V : Submodule R A} [Module.Finite R V] {δ : V →ₗ[R] V ⊗[R] A}
  {σ' : Type u} {gen : σ' → A} {N₀ n : ℕ}

local notation "Lb" => (r → ZMod m) × F
local notation "Λ" => (r → ℤ) × F

/-- The window extension around a field point of `W`. -/
theorem exists_window_extension (hδ : IsCoassoc δ)
    (hι : (Coalgebra.comul (R := R) (A := A)) ∘ₗ V.subtype = V.subtype.rTensor A ∘ₗ δ)
    (hgenV : ∀ i, gen i ∈ V) (hP : IsBoundedPresentation (R := R) gen N₀) (hN₀ : 1 ≤ N₀)
    (hinj : Set.InjOn (mred r F m) (boundedSums (mbox r F n : Set Λ) N₀))
    {α₀ : A →ₐ[R] AddMonoidAlgebra K Λ} (hα₀ : IsHopfPoint α₀)
    (hs₀ : Function.Surjective (scalarExt α₀)) (hw₀ : WeightsIn δ α₀ (mbox r F n : Set Λ))
    (y₀ : W R A Lb →ₐ[R] K)
    (hy₀ : pointOf R A Lb y₀ = (AddMonoidAlgebra.mapDomainAlgHom R K (mred r F m)).comp α₀) :
    ∃ (f : W R A Lb) (α : A →ₐ[R] AddMonoidAlgebra (Localization.Away f) Λ)
      (y : Localization.Away f →ₐ[R] K),
      IsHopfPoint α ∧ (∀ i, ↑(α (gen i)).coeff.support ⊆ (mbox r F n : Set Λ)) ∧
      (AddMonoidAlgebra.mapDomainAlgHom R _ (mred r F m)).comp α =
        pointOf R A Lb (IsScalarTower.toAlgHom R (W R A Lb) (Localization.Away f)) ∧
      Function.Surjective (scalarExt α) ∧ WeightsIn δ α (mbox r F n : Set Λ) ∧
      y.comp (IsScalarTower.toAlgHom R (W R A Lb) (Localization.Away f)) = y₀ ∧
      (AddMonoidAlgebra.mapAlgHom Λ y).comp α = α₀ := by
  classical
  -- weights of the universal point at the residue field of `y₀`
  obtain ⟨hP₀, ι₀, hι₀⟩ := exists_residueLift y₀
  have hwβ : WeightsIn δ ((AddMonoidAlgebra.mapDomainAlgHom R K (mred r F m)).comp α₀)
      ((mred r F m) '' (mbox r F n : Set Λ)) := weightsIn_mapDomain δ (mred r F m) hw₀
  have hwW : WeightsIn δ ((AddMonoidAlgebra.mapAlgHom Lb
      (IsScalarTower.toAlgHom R (W R A Lb) (RingHom.ker y₀).ResidueField)).comp
        (univ R A Lb)) ((mred r F m) '' (mbox r F n : Set Λ)) := by
    apply weightsIn_of_mapAlgHom δ ι₀ (rTensor_injective_of_field ι₀)
    rw [← AlgHom.comp_assoc, mapAlgHom_comp_mapAlgHom, hι₀]
    rw [← hy₀] at hwβ
    exact hwβ
  -- the extension over a principal open
  obtain ⟨f₁, hf₁, α₁, ⟨hα₁, hsupp₁, hred₁⟩, -⟩ :=
    HopfPointWindowExtension.exists_away_extension V δ hδ hι hgenV hP hN₀
      (mred r F m) hinj (isHopfPoint_univ R A Lb) (RingHom.ker y₀) hwW
  have hy₀f₁ : y₀ f₁ ≠ 0 := fun h => hf₁ (by simpa [RingHom.mem_ker] using h)
  obtain ⟨y₁, hy₁⟩ := exists_lift_away y₀ hy₀f₁
  -- the extension specializes to `α₀`
  have hα₁K : (AddMonoidAlgebra.mapAlgHom Λ y₁).comp α₁ = α₀ := by
    have hgs : ∀ i,
        ↑(((AddMonoidAlgebra.mapDomainAlgHom R K (mred r F m)).comp α₀) (gen i)).coeff.support
          ⊆ (mred r F m) '' (mbox r F n : Set Λ) := by
      intro i
      exact support_mapDomainAlgHom_subset (R := R) (mred r F m)
        (support_subset_of_weightsIn δ α₀ hw₀ V.subtype hι ⟨gen i, hgenV i⟩)
    obtain ⟨α', -, huniq⟩ := existsUnique_hopfPoint_extension hP hN₀ (mred r F m) hinj
      (hα₀.mapDomain (mred r F m)) hgs
    have h1 := huniq ((AddMonoidAlgebra.mapAlgHom Λ y₁).comp α₁)
      ⟨HopfPointWindowExtension.IsHopfPoint.mapAlgHom y₁ hα₁,
        fun i => (TorusChartRing.support_mapAlgHom_subset y₁ _).trans (hsupp₁ i), by
          rw [← AlgHom.comp_assoc, ← HopfPointWindowExtension.mapAlgHom_comp_mapDomain,
            AlgHom.comp_assoc, hred₁, ← hy₀, ← hy₁]
          exact (pointOf_comp _ _).symm⟩
    have h2 := huniq α₀ ⟨hα₀, fun i => support_subset_of_weightsIn δ α₀ hw₀ V.subtype hι
      ⟨gen i, hgenV i⟩, rfl⟩
    rw [h1, h2]
  have hy₁' : ∀ x, y₁ (algebraMap (W R A Lb) (Localization.Away f₁) x) = y₀ x :=
    fun x => congrArg (fun F => F x) hy₁
  -- weights near the point
  obtain ⟨hP₁, ι₁, hι₁⟩ := exists_residueLift y₁
  have hw₁ : WeightsIn δ ((AddMonoidAlgebra.mapAlgHom Λ
      (IsScalarTower.toAlgHom R (Localization.Away f₁) (RingHom.ker y₁).ResidueField)).comp α₁)
      (mbox r F n : Set Λ) := by
    apply weightsIn_of_mapAlgHom δ ι₁ (rTensor_injective_of_field ι₁)
    rw [← AlgHom.comp_assoc, mapAlgHom_comp_mapAlgHom, hι₁, hα₁K]
    exact hw₀
  obtain ⟨c₂, hc₂, hW₂⟩ := exists_away_weightsIn δ hδ hα₁ (mbox r F n : Set Λ)
    (RingHom.ker y₁) hw₁
  have hy₁c₂ : y₁ c₂ ≠ 0 := fun h => hc₂ (by simpa [RingHom.mem_ker] using h)
  -- the closed-immersion locus near the point
  obtain ⟨c₃, hy₁c₃, hS₃⟩ := exists_away_surjective_of_field hα₁ y₁ (by rw [hα₁K]; exact hs₀)
  -- a single principal open of `W`
  obtain ⟨w, k, hw⟩ := exists_numerator f₁ (c₂ * c₃)
  have hy₀w : y₀ w ≠ 0 := by
    have e := congrArg y₁ hw
    rw [map_mul, map_mul, hy₁', hy₁', map_pow] at e
    rw [← e]
    exact mul_ne_zero (mul_ne_zero hy₁c₂ hy₁c₃) (pow_ne_zero _ hy₀f₁)
  have hy₀f : y₀ (f₁ * w) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero hy₀f₁ hy₀w
  obtain ⟨ρ, hρ⟩ := exists_away_dvd (R := R) f₁ w
  have hρ' : ∀ x, ρ (algebraMap (W R A Lb) (Localization.Away f₁) x) =
      algebraMap (W R A Lb) (Localization.Away (f₁ * w)) x :=
    fun x => congrArg (fun F => F x) hρ
  have hρc : IsUnit (ρ (c₂ * c₃)) := by
    have e := congrArg ρ hw
    rw [map_mul, hρ', hρ'] at e
    have hu : IsUnit (algebraMap (W R A Lb) (Localization.Away (f₁ * w)) w) :=
      isUnit_of_dvd_unit (map_dvd _ (dvd_mul_left w f₁))
        (IsLocalization.Away.algebraMap_isUnit _)
    rw [← e] at hu
    exact isUnit_of_mul_isUnit_left hu
  rw [map_mul] at hρc
  obtain ⟨ρ₂, hρ₂⟩ := exists_factor_away ρ (isUnit_of_mul_isUnit_left hρc)
  obtain ⟨ρ₃, hρ₃⟩ := exists_factor_away ρ (isUnit_of_mul_isUnit_right hρc)
  obtain ⟨y, hy⟩ := exists_lift_away y₀ hy₀f
  have hyρ : y.comp ρ = y₁ := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers f₁)
    ext x
    have := congrArg (fun F => F x) hy
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at this
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom, AlgHom.comp_apply,
      hρ', this, hy₁']
  refine ⟨f₁ * w, (AddMonoidAlgebra.mapAlgHom Λ ρ).comp α₁, y,
    HopfPointWindowExtension.IsHopfPoint.mapAlgHom ρ hα₁,
    fun i => (TorusChartRing.support_mapAlgHom_subset ρ _).trans (hsupp₁ i), ?_, ?_, ?_, hy, ?_⟩
  · rw [← AlgHom.comp_assoc, ← HopfPointWindowExtension.mapAlgHom_comp_mapDomain,
      AlgHom.comp_assoc, hred₁, ← hρ]
    exact (pointOf_comp _ _).symm
  · rw [← hρ₃, ← mapAlgHom_comp_mapAlgHom, AlgHom.comp_assoc]
    exact surjective_scalarExt_mapAlgHom ρ₃ hS₃
  · rw [← hρ₂, ← mapAlgHom_comp_mapAlgHom, AlgHom.comp_assoc]
    exact weightsIn_mapAlgHom δ ρ₂ hW₂
  · rw [← AlgHom.comp_assoc, mapAlgHom_comp_mapAlgHom, hyρ, hα₁K]

end Window2

section Main

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [HopfAlgebra R A]
  [Algebra.FinitePresentation R A] {r : Type u} [Fintype r] [DecidableEq r]
  {F : Type u} [AddCommGroup F] [Fintype F]
  {K : Type u} [Field K] [Algebra R K]
  {V : Submodule R A} [Module.Finite R V] {δ : V →ₗ[R] V ⊗[R] A}
  {σ' : Type u} {gen : σ' → A} {N₀ : ℕ}

/-- Every closed-immersion Hopf point of `D(ℤ^r × F)` over a field lies on a window chart
datum. -/
theorem exists_windowDatum (hδ : IsCoassoc δ)
    (hι : (Coalgebra.comul (R := R) (A := A)) ∘ₗ V.subtype = V.subtype.rTensor A ∘ₗ δ)
    (hgenV : ∀ i, gen i ∈ V) (hgen : Algebra.adjoin R (Set.range gen) = ⊤)
    (hP : IsBoundedPresentation (R := R) gen N₀) (hN₀ : 1 ≤ N₀)
    {α₀ : A →ₐ[R] AddMonoidAlgebra K ((r → ℤ) × F)} (hα₀ : IsHopfPoint α₀)
    (hs₀ : Function.Surjective (scalarExt α₀)) :
    ∃ (n m : ℕ) (_ : NeZero m) (d : WindowDatum R A r F m gen n V δ N₀)
      (y : Localization.Away d.f →ₐ[R] K),
      y (algebraMap (W R A ((r → ZMod m) × F)) (Localization.Away d.f) d.N) ≠ 0 ∧
        (AddMonoidAlgebra.mapAlgHom ((r → ℤ) × F) y).comp d.α = α₀ := by
  classical
  obtain ⟨T₀, hT₀⟩ := exists_finite_weightsIn δ α₀
  obtain ⟨n, hn⟩ := exists_mbox T₀
  have hw₀ : WeightsIn δ α₀ (mbox r F n : Set ((r → ℤ) × F)) :=
    fun l hl => hT₀ l (fun h => hl (hn h))
  set k : ℕ := max (rigidityBound r F n) (2 * (N₀ * n) + 1) with hk
  have hcard : 0 < Fintype.card F := Fintype.card_pos
  set m : ℕ := k * Fintype.card F with hmdef
  have hkm : k ≤ m := Nat.le_mul_of_pos_right k hcard
  have hm : rigidityBound r F n ≤ m := (le_max_left _ _).trans hkm
  have hm2 : 2 * (N₀ * n) < m :=
    lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_right _ _).trans hkm)
  have hm0 : NeZero m := ⟨by omega⟩
  have htors : ∀ x : F, m • x = 0 := by
    intro x
    rw [hmdef, mul_nsmul]
    exact card_nsmul_eq_zero
  have hinj : Set.InjOn (mred r F m) (boundedSums (mbox r F n : Set ((r → ℤ) × F)) N₀) :=
    (injOn_mred_mbox hm2).mono (boundedSums_mbox_subset n N₀)
  obtain ⟨y₀, hy₀⟩ := exists_point_of_hopfPoint (A := A) (L := (r → ZMod m) × F)
    (hα₀.mapDomain (mred r F m))
  obtain ⟨f, α, y, hα, hsupp, hred, hsurj, hw, hy, hspec⟩ :=
    exists_window_extension hδ hι hgenV hP hN₀ hinj hα₀ hs₀ hw₀ y₀ hy₀
  have hy' : ∀ x, y (algebraMap (W R A ((r → ZMod m) × F)) (Localization.Away f) x) = y₀ x :=
    fun x => congrArg (fun F => F x) hy
  have hP₀ : (RingHom.ker y₀).IsPrime := RingHom.ker_isPrime _
  have hf : f ∉ RingHom.ker y₀ := by
    intro h
    rw [RingHom.mem_ker, ← hy'] at h
    exact (IsLocalization.Away.algebraMap_isUnit f).map y |>.ne_zero h
  have := Fintype.ofFinite (Γ ((r → ZMod m) × F))
  obtain ⟨N, hNinv, hNp, hcover⟩ :=
    exists_invariant_cover (act R A ((r → ZMod m) × F)) (RingHom.ker y₀) hf
  let d : WindowDatum R A r F m gen n V δ N₀ :=
    { bound := hm
      torsion := htors
      adjoin_gen := hgen
      f := f
      N := N
      α := α
      isHopfPoint := hα
      support := hsupp
      red_comp := hred
      surjective := hsurj
      invariant := hNinv
      cover := hcover
      weights := hw
      injOn := hinj }
  refine ⟨n, m, hm0, d, y, ?_, hspec⟩
  change y (algebraMap (W R A ((r → ZMod m) × F)) (Localization.Away f) N) ≠ 0
  rw [hy']
  intro h
  exact hNp (by simpa [RingHom.mem_ker] using h)

end Main

end Langlands.Algebra.MixedChartExistence
