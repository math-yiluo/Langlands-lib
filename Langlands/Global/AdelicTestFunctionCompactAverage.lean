import Langlands.Global.AdelicHarishChandraCompactConjugation
import Langlands.Global.AdelicCompactKernelAverage
import Langlands.Global.AdelicMaximalCompactFactors
import Langlands.Global.AdelicParabolicModulus

/-! # Two-sided translates and compact right averages of adelic test functions -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory NumberField Set
open scoped CategoryTheory.MonObj ContDiff Manifold

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open InfiniteAdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]

local notation "A" => AdelicGroupPoints F G
local notation "A∞" => InfiniteAdelicGroupPoints F G
local notation "A_f" => FiniteAdelicGroupPoints F G

/-- Two-sided translates `x ↦ h(g₁ x g₂)` of adelic test functions are adelic test functions. -/
theorem isAdelicTestFunction_comp_mul_mul {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) {h : A → ℂ} (hh : IsAdelicTestFunction F G h)
    (g₁ g₂ : A) : IsAdelicTestFunction F G (fun x => h (g₁ * x * g₂)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let e : A ≃ₜ A := (Homeomorph.mulLeft g₁).trans (Homeomorph.mulRight g₂)
  have he (x : A) : e x = g₁ * x * g₂ := rfl
  obtain ⟨L, hLopen, hL⟩ := hh.1.2.2
  obtain ⟨U, hUopen, hU⟩ := hh.2.2
  set f₁ := finite F G g₁ with hf₁
  set f₂ := finite F G g₂ with hf₂
  have hcont : Continuous (fun x : A => g₁ * x * g₂) := e.continuous
  have hsupp : HasCompactSupport (fun x => h (g₁ * x * g₂)) := by
    simpa only [Function.comp_def, he] using hh.2.1.comp_homeomorph e
  let L' : Subgroup A_f := L.comap (MulAut.conj f₂⁻¹).toMonoidHom
  have hL'open : IsOpen (L' : Set A_f) := by
    have hc : Continuous fun x : A_f => f₂⁻¹ * x * f₂⁻¹⁻¹ :=
      (continuous_const.mul continuous_id).mul continuous_const
    exact hLopen.preimage hc
  let U' : Subgroup A_f := U.comap (MulAut.conj f₁).toMonoidHom
  have hU'open : IsOpen (U' : Set A_f) := by
    have hc : Continuous fun x : A_f => f₁ * x * f₁⁻¹ :=
      (continuous_const.mul continuous_id).mul continuous_const
    exact hUopen.preimage hc
  refine ⟨⟨hh.1.1.comp hcont, ?_, L', hL'open, ?_⟩, hsupp, U', hU'open, ?_⟩
  · intro b
    apply (isPlotSmooth_iff_contMDiff F G hsmooth _).2
    have hslice := (isPlotSmooth_iff_contMDiff F G hsmooth _).1 (hh.1.2.1 (f₁ * b * f₂))
    have hmul : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, smoothModel F d) ∞
        (fun x : A∞ => infinite F G g₁ * x * infinite F G g₂) :=
      (contMDiff_const.mul contMDiff_id).mul contMDiff_const
    apply (hslice.comp hmul).congr
    intro x
    change h (g₁ * pair F G x b * g₂) =
      h (pair F G (infinite F G g₁ * x * infinite F G g₂) (f₁ * b * f₂))
    conv_lhs => rw [← pair_projections F G g₁, ← pair_projections F G g₂]
    rw [pair_mul, pair_mul]
  · intro l hl x
    change h (g₁ * (x * ofFinite F G l) * g₂) = h (g₁ * x * g₂)
    have hl' : f₂⁻¹ * l * f₂ ∈ L := by
      have := hl
      change f₂⁻¹ * l * f₂⁻¹⁻¹ ∈ L at this
      rwa [inv_inv] at this
    have hconj := finite_conjugation F G g₂ l
    have heq : g₁ * (x * ofFinite F G l) * g₂ =
        g₁ * x * g₂ * ofFinite F G (f₂⁻¹ * l * f₂) := by
      rw [← hconj]
      group
    rw [heq, hL _ hl']
  · intro l hl x
    change h (g₁ * (ofFinite F G l * x) * g₂) = h (g₁ * x * g₂)
    have hl' : f₁ * l * f₁⁻¹ ∈ U := hl
    have hconj := finite_conjugation F G g₁⁻¹ l
    rw [map_inv, inv_inv, inv_inv] at hconj
    have heq : g₁ * (ofFinite F G l * x) * g₂ =
        ofFinite F G (f₁ * l * f₁⁻¹) * (g₁ * x * g₂) := by
      rw [← hconj]
      group
    rw [heq, hU _ hl']

/-- Sums of adelic test functions are adelic test functions. -/
theorem isAdelicTestFunction_add {f g : A → ℂ}
    (hf : IsAdelicTestFunction F G f) (hg : IsAdelicTestFunction F G g) :
    IsAdelicTestFunction F G (fun x => f x + g x) := by
  obtain ⟨⟨hfc, hfs, Lf, hLf, hLfi⟩, hfsupp, Uf, hUf, hUfi⟩ := hf
  obtain ⟨⟨hgc, hgs, Lg, hLg, hLgi⟩, hgsupp, Ug, hUg, hUgi⟩ := hg
  refine ⟨⟨hfc.add hgc, fun b => Submodule.add_mem _ (hfs b) (hgs b), Lf ⊓ Lg,
    hLf.inter hLg, fun l hl x => ?_⟩, hfsupp.add hgsupp, Uf ⊓ Ug, hUf.inter hUg,
    fun l hl x => ?_⟩
  · change f _ + g _ = f x + g x
    rw [hLfi l hl.1, hLgi l hl.2]
  · change f _ + g _ = f x + g x
    rw [hUfi l hl.1, hUgi l hl.2]

/-- The zero function is an adelic test function. -/
theorem isAdelicTestFunction_zero :
    IsAdelicTestFunction F G (fun _ : A => (0 : ℂ)) :=
  ⟨⟨continuous_const, fun _ => Submodule.zero_mem _, ⊤, isOpen_univ, fun _ _ _ => rfl⟩,
    HasCompactSupport.zero, ⊤, isOpen_univ, fun _ _ _ => rfl⟩

/-- Finite sums of adelic test functions are adelic test functions. -/
theorem isAdelicTestFunction_finset_sum {Idx : Type*} (s : Finset Idx)
    (f : Idx → A → ℂ) (hf : ∀ j ∈ s, IsAdelicTestFunction F G (f j)) :
    IsAdelicTestFunction F G (fun x => ∑ j ∈ s, f j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isAdelicTestFunction_zero (F := F) (G := G)
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact isAdelicTestFunction_add (hf j (Finset.mem_insert_self j s))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

section MaximalCompactAverage

/-- The right average `z ↦ ∫_K a(k) h(z k) dk` over a compact subgroup `K ≤ G(𝔸)` with weight `a`,
for the Haar probability measure of `K`. -/
def maximalCompactRightAverage (K : Subgroup A) (hK : IsCompact (K : Set A)) (a : K → ℂ)
    (h : A → ℂ) (z : A) : ℂ :=
  ∫ k, a k * h (z * k) ∂compactHaarProbability F G K hK

variable [LocallyOfFiniteType G.X.hom]

/-- Right averages `z ↦ ∫_K a(k) h(z k) dk` over a maximal compact subgroup `K ≤ G(𝔸)`, with a
continuous weight `a` right invariant under an open subgroup of the finite adelic points, are
adelic test functions when `h` is. The average is the finite sum, over the cosets of the finite
factor of `K` modulo an open subgroup fixing `a` and `h`, of averages over the infinite factor
of `K` (`isAdelicTestFunction_rightCompactKernelAverage`) of right translates of `h`. -/
theorem isAdelicTestFunction_maximalCompactRightAverage {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (K : Subgroup A)
    (hK : IsMaximalCompactSubgroup F G K) (a : K → ℂ) (ha : Continuous a)
    (L₀ : Subgroup A_f) (hL₀ : IsOpen (L₀ : Set A_f))
    (haL : ∀ (k : K) (l : A_f), l ∈ L₀ → ∀ hkl : (k : A) * ofFinite F G l ∈ K,
      a ⟨_, hkl⟩ = a k)
    {h : A → ℂ} (hh : IsAdelicTestFunction F G h) :
    IsAdelicTestFunction F G (maximalCompactRightAverage K hK.1 a h) := by
  classical
  unfold maximalCompactRightAverage
  obtain ⟨L₁, hL₁open, hL₁⟩ := hh.1.2.2
  set μK := compactHaarProbability F G K hK.1 with hμK
  set Kf : Subgroup A_f := K.comap (ofFinite F G).toMonoidHom with hKfdef
  set Ki : Subgroup A∞ := K.comap (ofInfinite F G).toMonoidHom with hKidef
  have hKf : IsCompact (Kf : Set A_f) := hK.isMaximalCompact_comap_ofFinite.1
  have hKi : IsCompact (Ki : Set A∞) := hK.isMaximalCompact_comap_ofInfinite.1
  have : CompactSpace Kf := isCompact_iff_compactSpace.mp hKf
  have : CompactSpace Ki := isCompact_iff_compactSpace.mp hKi
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK.1
  set N : Subgroup Kf := (L₀ ⊓ L₁).subgroupOf Kf with hNdef
  have hN : IsOpen (N : Set Kf) := Subgroup.subgroupOf_isOpen Kf (L₀ ⊓ L₁) (hL₀.inter hL₁open)
  have : Finite (Kf ⧸ N) := Subgroup.quotient_finite_of_isOpen N hN
  have : DiscreteTopology (Kf ⧸ N) := QuotientGroup.discreteTopology hN
  let : Fintype (Kf ⧸ N) := Fintype.ofFinite _
  have hfin : ∀ k : K, ofFinite F G (finite F G (k : A)) ∈ K := fun k =>
    ((hK.mem_iff (k : A)).mp k.2).2
  have hinf : ∀ k : K, ofInfinite F G (infinite F G (k : A)) ∈ K := fun k =>
    ((hK.mem_iff (k : A)).mp k.2).1
  let ρf : K → Kf := fun k => ⟨finite F G (k : A), hfin k⟩
  have hρf : Continuous ρf :=
    ((finite F G).continuous.comp continuous_subtype_val).subtype_mk _
  let π : K → Kf ⧸ N := fun k => (ρf k : Kf ⧸ N)
  have hπ : Continuous π := continuous_quotient_mk'.comp hρf
  let τ : K → Ki := fun k => ⟨infinite F G (k : A), hinf k⟩
  have hτ : Continuous τ :=
    ((infinite F G).continuous.comp continuous_subtype_val).subtype_mk _
  let r : Kf ⧸ N → Kf := fun c => Quotient.out c
  have hmemc : ∀ (c : Kf ⧸ N) (t : Ki),
      ofInfinite F G (t : A∞) * ofFinite F G ((r c : Kf) : A_f) ∈ K := fun c t =>
    K.mul_mem t.2 (r c).2
  let w : Kf ⧸ N → C(Ki, ℂ) := fun c =>
    ⟨fun t => a ⟨_, hmemc c t⟩, ha.comp (Continuous.subtype_mk
      (((ofInfinite F G).continuous.comp continuous_subtype_val).mul continuous_const) _)⟩
  let : MeasurableSpace Ki := borel Ki
  have : BorelSpace Ki := ⟨rfl⟩
  let νm : Kf ⧸ N → Measure Ki := fun c => Measure.map τ (μK.restrict (π ⁻¹' {c}))
  let h' : Kf ⧸ N → A → ℂ := fun c y => h (y * ofFinite F G ((r c : Kf) : A_f))
  have hh' : ∀ c, IsAdelicTestFunction F G (h' c) := by
    intro c
    have := isAdelicTestFunction_comp_mul_mul hsmooth hh 1 (ofFinite F G ((r c : Kf) : A_f))
    simpa only [one_mul] using this
  have hsum : (fun z => ∫ k, a k * h (z * k) ∂μK) =
      fun z => ∑ c, rightCompactKernelAverage (νm c) (w c) (h' c) z := by
    funext z
    have hpt : ∀ (c : Kf ⧸ N) (k : K), k ∈ π ⁻¹' {c} →
        a k * h (z * k) = w c (τ k) * h' c (z * ofInfinite F G ((τ k : Ki) : A∞)) := by
      intro c k hk
      have hk' : π k = c := hk
      have hq : ((r c : Kf) : Kf ⧸ N) = π k := by rw [hk']; exact QuotientGroup.out_eq' c
      have hmem : (r c)⁻¹ * ρf k ∈ N := QuotientGroup.eq.mp hq
      have hm : ((r c : Kf) : A_f)⁻¹ * finite F G (k : A) ∈ L₀ ⊓ L₁ := hmem
      set m := ((r c : Kf) : A_f)⁻¹ * finite F G (k : A) with hmdef
      have hk_eq : (k : A) = ofInfinite F G (infinite F G (k : A)) *
          ofFinite F G ((r c : Kf) : A_f) * ofFinite F G m := by
        rw [mul_assoc, ← map_mul, hmdef, mul_inv_cancel_left, ofInfinite_eq_pair,
          ofFinite_eq_pair, pair_mul, mul_one, one_mul, pair_projections]
      have hkl : (⟨_, hmemc c (τ k)⟩ : K).val * ofFinite F G m ∈ K := by
        change ofInfinite F G (infinite F G (k : A)) * ofFinite F G ((r c : Kf) : A_f) *
          ofFinite F G m ∈ K
        rw [← hk_eq]
        exact k.2
      have ha_eq : a k = w c (τ k) := by
        have h1 := haL ⟨_, hmemc c (τ k)⟩ m hm.1 hkl
        have h2 : (⟨_, hkl⟩ : K) = k := Subtype.ext hk_eq.symm
        rw [h2] at h1
        exact h1
      have hh_eq : h (z * k) = h' c (z * ofInfinite F G ((τ k : Ki) : A∞)) := by
        change h (z * k) = h (z * ofInfinite F G (infinite F G (k : A)) *
          ofFinite F G ((r c : Kf) : A_f))
        conv_lhs => rw [hk_eq]
        rw [← mul_assoc, ← mul_assoc, hL₁ m hm.2]
      rw [ha_eq, hh_eq]
    have hF : Continuous fun k : K => a k * h (z * k) :=
      ha.mul (hh.1.1.comp (continuous_const.mul continuous_subtype_val))
    have hint : Integrable (fun k : K => a k * h (z * k)) μK :=
      integrableOn_univ.mp (hF.continuousOn.integrableOn_compact isCompact_univ)
    have hmeas : ∀ c, MeasurableSet (π ⁻¹' {c}) := fun c =>
      ((isOpen_discrete {c}).preimage hπ).measurableSet
    have hdec : (fun k => a k * h (z * k)) =
        fun k => ∑ c, (π ⁻¹' {c}).indicator (fun k => a k * h (z * k)) k := by
      funext k
      rw [Finset.sum_eq_single (π k)]
      · rw [indicator_of_mem (show k ∈ π ⁻¹' {π k} from rfl)]
      · intro c _ hc
        rw [indicator_of_notMem (show k ∉ π ⁻¹' {c} from fun h => hc h.symm)]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
    rw [hdec, integral_finsetSum _ (fun c _ => hint.indicator (hmeas c))]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_indicator (hmeas c)]
    unfold rightCompactKernelAverage
    change ∫ x in π ⁻¹' {c}, a x * h (z * ↑x) ∂μK =
      ∫ t, w c t * h' c (z * ofInfinite F G (t : A∞)) ∂νm c
    have hcont : Continuous fun t : Ki => w c t * h' c (z * ofInfinite F G (t : A∞)) :=
      (w c).continuous.mul ((hh' c).1.1.comp (continuous_const.mul
        ((ofInfinite F G).continuous.comp continuous_subtype_val)))
    rw [integral_map hτ.aemeasurable hcont.aestronglyMeasurable]
    exact setIntegral_congr_fun (hmeas c) fun k hk => hpt c k hk
  rw [hsum]
  exact isAdelicTestFunction_finset_sum _ _ fun c _ =>
    isAdelicTestFunction_rightCompactKernelAverage (νm c) hsmooth (w c) (hh' c)

omit [LocallyOfFiniteType G.X.hom] in
/-- **Right finiteness under a maximal compact subgroup.** A continuous function on `G(𝔸)` whose
right translates by `K_∞ = K ∩ G(F_∞)` span a finite-dimensional space and which is right
invariant under an open subgroup `L` of `G(𝔸_f)` has finitely many right `K`-translates
`z ↦ φ(z k_j)` such that every right translate is `φ(z k) = ∑_j a_j(k) φ(z k_j)` with continuous
coefficients `a_j`, right invariant under `L`. -/
theorem exists_maximalCompact_rightTranslate_decomposition (K : Subgroup A)
    (hK : IsMaximalCompactSubgroup F G K) {φ : A → ℂ} (hφc : Continuous φ)
    (hφK : IsInfiniteSubgroupFiniteFunction F G (K.comap (ofInfinite F G).toMonoidHom) φ)
    (L : Subgroup A_f) (hL : IsOpen (L : Set A_f))
    (hφL : ∀ l ∈ L, ∀ g : A, φ (g * ofFinite F G l) = φ g) :
    ∃ (n : ℕ) (k₀ : Fin n → K) (a : Fin n → K → ℂ), (∀ j, Continuous (a j)) ∧
      (∀ j (k : K) (l : A_f), l ∈ L → ∀ hkl : (k : A) * ofFinite F G l ∈ K,
        a j ⟨_, hkl⟩ = a j k) ∧
      ∀ (k : K) (z : A), φ (z * k) = ∑ j, a j k * φ (z * k₀ j) := by
  classical
  set Kf : Subgroup A_f := K.comap (ofFinite F G).toMonoidHom with hKfdef
  set Ki : Subgroup A∞ := K.comap (ofInfinite F G).toMonoidHom with hKidef
  have hKf : IsCompact (Kf : Set A_f) := hK.isMaximalCompact_comap_ofFinite.1
  have : CompactSpace Kf := isCompact_iff_compactSpace.mp hKf
  set N : Subgroup Kf := L.subgroupOf Kf with hNdef
  have hN : IsOpen (N : Set Kf) := Subgroup.subgroupOf_isOpen Kf L hL
  have : Finite (Kf ⧸ N) := Subgroup.quotient_finite_of_isOpen N hN
  have hfin : ∀ k : K, ofFinite F G (finite F G (k : A)) ∈ K := fun k =>
    ((hK.mem_iff (k : A)).mp k.2).2
  have hinf : ∀ k : K, ofInfinite F G (infinite F G (k : A)) ∈ K := fun k =>
    ((hK.mem_iff (k : A)).mp k.2).1
  let R : K → A → ℂ := fun k z => φ (z * k)
  set V : Submodule ℂ (A → ℂ) := Submodule.span ℂ (Set.range R) with hVdef
  set W : Submodule ℂ (A → ℂ) := Submodule.span ℂ (Set.range fun t : Ki =>
    fun z : A => φ (z * ofInfinite F G (t : A∞))) with hWdef
  have : FiniteDimensional ℂ W := hφK
  let T : Kf ⧸ N → (A → ℂ) →ₗ[ℂ] (A → ℂ) := fun c =>
    LinearMap.funLeft ℂ ℂ (fun z : A => z * ofFinite F G ((Quotient.out c : Kf) : A_f))
  have hVle : V ≤ ⨆ c, W.map (T c) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    set c : Kf ⧸ N := ((⟨finite F G (k : A), hfin k⟩ : Kf) : Kf ⧸ N) with hcdef
    have hq : ((Quotient.out c : Kf) : Kf ⧸ N) = c := QuotientGroup.out_eq' c
    have hmem : (Quotient.out c)⁻¹ * (⟨finite F G (k : A), hfin k⟩ : Kf) ∈ N :=
      QuotientGroup.eq.mp (hq.trans hcdef)
    set m : A_f := ((Quotient.out c : Kf) : A_f)⁻¹ * finite F G (k : A) with hmdef
    have hm : m ∈ L := hmem
    have hk_eq : (k : A) = ofInfinite F G (infinite F G (k : A)) *
        ofFinite F G ((Quotient.out c : Kf) : A_f) * ofFinite F G m := by
      rw [mul_assoc, ← map_mul, hmdef, mul_inv_cancel_left, ofInfinite_eq_pair,
        ofFinite_eq_pair, pair_mul, mul_one, one_mul, pair_projections]
    refine Submodule.mem_iSup_of_mem c ⟨fun z => φ (z * ofInfinite F G (infinite F G (k : A))),
      Submodule.subset_span ⟨⟨_, hinf k⟩, rfl⟩, ?_⟩
    funext z
    change φ (z * ofFinite F G ((Quotient.out c : Kf) : A_f) *
      ofInfinite F G (infinite F G (k : A))) = φ (z * k)
    conv_rhs => rw [hk_eq]
    rw [← mul_assoc, ← mul_assoc, hφL m hm, mul_assoc, mul_assoc,
      (factors_commute F G _ _).eq]
  have : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le hVle
  obtain ⟨b, hbR, hbspan, hbli⟩ := exists_linearIndependent ℂ (Set.range R)
  have hbV : ∀ x ∈ b, x ∈ V := fun x hx => Submodule.subset_span (hbR hx)
  let f : b → V := fun x => ⟨x, hbV x x.2⟩
  have hfli : LinearIndependent ℂ f := by
    apply LinearIndependent.of_comp V.subtype
    exact hbli
  have : Finite b := hfli.finite_of_isNoetherian
  have hfsp : ⊤ ≤ Submodule.span ℂ (Set.range f) := by
    have key : Submodule.map V.subtype (Submodule.span ℂ (Set.range f)) =
        Submodule.span ℂ b := by
      rw [Submodule.map_span]
      congr 1
      ext x
      constructor
      · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
        exact y.2
      · intro hx
        exact ⟨f ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
    intro v _
    have hv : (v : A → ℂ) ∈ Submodule.map V.subtype (Submodule.span ℂ (Set.range f)) := by
      rw [key, hbspan]
      exact v.2
    obtain ⟨w, hw, hwv⟩ := hv
    have hwv' : w = v := Subtype.ext hwv
    rwa [← hwv']
  let bas : Module.Basis b ℂ V := Module.Basis.mk hfli hfsp
  let : Fintype b := Fintype.ofFinite b
  set n : ℕ := Fintype.card b with hn
  let eb : b ≃ Fin n := Fintype.equivFin b
  have hbk : ∀ x : b, ∃ k : K, R k = (x : A → ℂ) := fun x => hbR x.2
  let k₀ : Fin n → K := fun j => Classical.choose (hbk (eb.symm j))
  have hk₀ : ∀ j, R (k₀ j) = ((eb.symm j : b) : A → ℂ) := fun j =>
    Classical.choose_spec (hbk (eb.symm j))
  let vk : K → V := fun k => ⟨R k, Submodule.subset_span ⟨k, rfl⟩⟩
  have hvk : Continuous vk :=
    Continuous.subtype_mk (continuous_pi fun z =>
      hφc.comp (continuous_const.mul continuous_subtype_val)) _
  let a : Fin n → K → ℂ := fun j k => bas.repr (vk k) (eb.symm j)
  refine ⟨n, k₀, a, fun j => ?_, fun j k l hl hkl => ?_, fun k z => ?_⟩
  · exact (bas.coord (eb.symm j)).continuous_of_finiteDimensional.comp hvk
  · have hv : vk ⟨_, hkl⟩ = vk k := by
      apply Subtype.ext
      funext z
      change φ (z * ((k : A) * ofFinite F G l)) = φ (z * k)
      rw [← mul_assoc, hφL l hl]
    change bas.repr (vk ⟨_, hkl⟩) (eb.symm j) = bas.repr (vk k) (eb.symm j)
    rw [hv]
  · have hsum := bas.sum_repr (vk k)
    have hz := congrFun (congrArg (fun v : V => (v : A → ℂ)) hsum) z
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at hz
    refine Eq.trans (show φ (z * k) = ((vk k : V) : A → ℂ) z from rfl) ?_
    rw [← hz, ← eb.symm.sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [Module.Basis.mk_apply]
    change ((eb.symm j : b) : A → ℂ) z = φ (z * k₀ j)
    rw [← hk₀ j]

end MaximalCompactAverage

end Langlands.Global.AdelicGroupPoints
