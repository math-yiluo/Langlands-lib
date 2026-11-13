import Langlands.Analysis.Local.QuotientFactorizationHaar
import Langlands.Representation.Category.Basic

/-! # Abstract inputs for the integral identification of Renard VII.3.4

Three independent abstract facts used by the proof of the integral identification
`F^{<1̄}_{PQ}/F^{≤1̄}_{PQ}(σ) ≃ σ`:

* right invariance of integrals over a complementary subgroup;
* integrals of vector-valued functions read against every linear form;
* a rigidity statement for natural surjections onto a functor isomorphic to the identity.
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ]
  [LocallyCompactSpace Γ]
  (H K : Subgroup Γ) (m : H × K ≃ₜ Γ) (hm : ∀ p : H × K, m p = p.1.val * p.2.val)
  [MeasurableSpace K] [BorelSpace K]
  [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
  (μK : Measure K) [IsHaarMeasure μK] [μK.Regular] [IsMulRightInvariant μK]
  (ν : Measure (LeftQuotient H)) [ν.Regular]

omit [T2Space Γ] in
include hm in
/-- A nonzero regular right-invariant quotient measure pulls back to a nonzero multiple of a
two-sided Haar measure on the complement. -/
theorem exists_ne_zero_map_factorQuotientHomeomorph_symm (hν : ν ≠ 0)
    (hinv : ∀ g : Γ, MeasurePreserving (rightTranslate H g) ν ν) :
    ∃ a : ℝ≥0, a ≠ 0 ∧
      Measure.map (factorQuotientHomeomorph H Subtype.val m hm).symm ν = a • μK := by
  obtain ⟨a, ha⟩ := exists_smul_map_factorQuotientHomeomorph_symm H K m hm μK ν hinv
  refine ⟨a, ?_, ha⟩
  rintro rfl
  apply hν
  let c := factorQuotientHomeomorph H Subtype.val m hm
  have hνc : ν = Measure.map c (Measure.map c.symm ν) := by
    rw [Measure.map_map c.continuous.measurable c.symm.continuous.measurable]
    simp
  rw [hνc]
  change Measure.map c (Measure.map c.symm ν) = 0
  rw [ha, zero_smul, Measure.map_zero]

omit [T2Space Γ] in
include hm in
/-- Let `Γ = H K` with literal product coordinates. If `Γ` carries a nonzero regular
right-invariant measure on `H \ Γ` and `K` a two-sided Haar measure, then integration over `K`
of left `H`-invariant functions is invariant under right translation by every `g ∈ Γ`. -/
theorem integral_mul_right_of_leftInvariant (hν : ν ≠ 0)
    (hinv : ∀ g : Γ, MeasurePreserving (rightTranslate H g) ν ν)
    (φ : Γ → ℂ) (hφ : ∀ h : H, ∀ x, φ (h.val * x) = φ x) (g : Γ) :
    (Integrable (fun k : K => φ (k.val * g)) μK ↔ Integrable (fun k : K => φ k.val) μK) ∧
      ∫ k : K, φ (k.val * g) ∂μK = ∫ k : K, φ k.val ∂μK := by
  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_map_factorQuotientHomeomorph_symm H K m hm μK ν hν hinv
  let c := factorQuotientHomeomorph H Subtype.val m hm
  let ψ : LeftQuotient H → ℂ := descend H φ hφ
  have hψ0 : ∀ k : K, φ k.val = ψ (c k) := fun k => rfl
  have hψ1 : ∀ k : K, φ (k.val * g) = ψ (rightTranslate H g (c k)) := fun k => rfl
  have hcs : ∀ q, c (c.symm q) = q := c.apply_symm_apply
  have hpres := hinv g
  let e := c.symm.toMeasurableEquiv
  have hint : ∀ F : K → ℂ, Integrable F μK ↔ Integrable (fun q => F (c.symm q)) ν := by
    intro F
    rw [← integrable_smul_measure (c := (a : ℝ≥0∞)) (by simpa using ha0) ENNReal.coe_ne_top,
      Measure.coe_nnreal_smul, ← ha]
    exact integrable_map_equiv e F
  have hintegral : ∀ F : K → ℂ, a • ∫ k, F k ∂μK = ∫ q, F (c.symm q) ∂ν := by
    intro F
    rw [← integral_smul_nnreal_measure, ← ha]
    exact integral_map_equiv e F
  have hshift : ∫ q, ψ (rightTranslate H g q) ∂ν = ∫ q, ψ q ∂ν :=
    MeasurePreserving.integral_comp' (f := (rightTranslate H g).toMeasurableEquiv) hpres ψ
  constructor
  · rw [hint, hint]
    simp_rw [hψ0, hψ1, hcs]
    exact hpres.integrable_comp_emb (rightTranslate H g).toMeasurableEquiv.measurableEmbedding
  · have h1 := hintegral (fun k : K => φ (k.val * g))
    have h0 := hintegral (fun k : K => φ k.val)
    simp only [hψ0, hψ1, hcs] at h0 h1
    rw [hshift, ← h0] at h1
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha0
    rw [NNReal.smul_def, NNReal.smul_def] at h1
    exact smul_right_injective ℂ ha' h1

end Langlands.QuotientIntegration

namespace Langlands.DualIntegral

open MeasureTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
  {W : Type*} [AddCommGroup W] [Module ℂ W] {W' : Type*} [AddCommGroup W'] [Module ℂ W']

/-- `w` is the integral of `F : X → W` read against every linear form: each `ℓ ∘ F` is
integrable and `ℓ w = ∫ ℓ ∘ F`. -/
def HasDualIntegral (F : X → W) (w : W) : Prop :=
  ∀ ℓ : Module.Dual ℂ W, Integrable (fun x => ℓ (F x)) μ ∧ ℓ w = ∫ x, ℓ (F x) ∂μ

variable {μ}

/-- Linear forms separate points, so a dual integral is unique. -/
theorem HasDualIntegral.unique {F : X → W} {w₁ w₂ : W} (h₁ : HasDualIntegral μ F w₁)
    (h₂ : HasDualIntegral μ F w₂) : w₁ = w₂ := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ (w₁ - w₂)).mp
  intro ℓ
  rw [map_sub, (h₁ ℓ).2, (h₂ ℓ).2, sub_self]

variable (μ) in
/-- The dual integral of `F`, and `0` when `F` has none. -/
def dualIntegral (F : X → W) : W :=
  open Classical in if h : ∃ w, HasDualIntegral μ F w then h.choose else 0

/-- A dual integral is the chosen one. -/
theorem HasDualIntegral.dualIntegral_eq {F : X → W} {w : W} (h : HasDualIntegral μ F w) :
    dualIntegral μ F = w := by
  unfold dualIntegral
  split_ifs with hex
  · exact hex.choose_spec.unique h
  · exact absurd ⟨w, h⟩ hex

/-- If some dual integral exists, the chosen one is a dual integral. -/
theorem hasDualIntegral_dualIntegral {F : X → W} (h : ∃ w, HasDualIntegral μ F w) :
    HasDualIntegral μ F (dualIntegral μ F) := by
  obtain ⟨w, hw⟩ := h
  rw [hw.dualIntegral_eq]
  exact hw

theorem hasDualIntegral_zero : HasDualIntegral μ (fun _ : X => (0 : W)) 0 := by
  intro ℓ
  simp only [map_zero, integral_zero]
  exact ⟨integrable_zero _ _ _, trivial⟩

theorem HasDualIntegral.add {F G : X → W} {w v : W} (hF : HasDualIntegral μ F w)
    (hG : HasDualIntegral μ G v) : HasDualIntegral μ (fun x => F x + G x) (w + v) := by
  intro ℓ
  simp only [map_add]
  exact ⟨(hF ℓ).1.add (hG ℓ).1, by rw [(hF ℓ).2, (hG ℓ).2, integral_add (hF ℓ).1 (hG ℓ).1]⟩

theorem HasDualIntegral.smul {F : X → W} {w : W} (hF : HasDualIntegral μ F w) (c : ℂ) :
    HasDualIntegral μ (fun x => c • F x) (c • w) := by
  intro ℓ
  simp only [map_smul, smul_eq_mul]
  exact ⟨(hF ℓ).1.const_mul c, by rw [(hF ℓ).2, integral_const_mul]⟩

theorem HasDualIntegral.map {F : X → W} {w : W} (hF : HasDualIntegral μ F w)
    (φ : W →ₗ[ℂ] W') : HasDualIntegral μ (fun x => φ (F x)) (φ w) :=
  fun ℓ => hF (ℓ.comp φ)

theorem HasDualIntegral.congr {F G : X → W} {w : W} (hF : HasDualIntegral μ F w)
    (h : ∀ x, F x = G x) : HasDualIntegral μ G w := by
  have hFG : F = G := funext h
  subst hFG
  exact hF

theorem HasDualIntegral.sum {ι : Type*} (s : Finset ι) {F : ι → X → W} {w : ι → W}
    (h : ∀ i ∈ s, HasDualIntegral μ (F i) (w i)) :
    HasDualIntegral μ (fun x => ∑ i ∈ s, F i x) (∑ i ∈ s, w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (hasDualIntegral_zero (μ := μ) (W := W))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Change of variables along a measurable embedding whose image measure is a multiple of the
target measure. -/
theorem HasDualIntegral.comp_measurableEmbedding {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} {e : X → Y} (he : MeasurableEmbedding e) {a : NNReal}
    (hmap : μ.map e = a • ν) {F : Y → W} {w : W} (hF : HasDualIntegral ν F w) :
    HasDualIntegral μ (fun x => F (e x)) ((a : ℂ) • w) := by
  intro ℓ
  obtain ⟨hi, hw⟩ := hF ℓ
  refine ⟨?_, ?_⟩
  · have h : Integrable (fun y => ℓ (F y)) (μ.map e) := by
      rw [hmap]
      exact hi.smul_measure_nnreal
    exact he.integrable_map_iff.mp h
  · have h := he.integral_map (μ := μ) (fun y => ℓ (F y))
    rw [hmap, integral_smul_nnreal_measure] at h
    rw [← h, map_smul, hw, NNReal.smul_def, Complex.real_smul, smul_eq_mul]

/-- The dual integral of `w` times the indicator of a measurable set of finite measure. -/
theorem hasDualIntegral_indicator {S : Set X} (hS : MeasurableSet S) (hμS : μ S ≠ ∞)
    (w : W) : HasDualIntegral μ (S.indicator fun _ => w) ((μ.real S : ℂ) • w) := by
  intro ℓ
  have hfun : (fun x => ℓ (S.indicator (fun _ => w) x)) = S.indicator (fun _ => ℓ w) := by
    funext x
    by_cases hx : x ∈ S <;> simp [hx]
  rw [hfun, integral_indicator_const _ hS, map_smul, Complex.real_smul, smul_eq_mul]
  exact ⟨(integrableOn_const hμS).integrable_indicator hS, rfl⟩

/-- A locally constant function vanishing off a compact set has a dual integral against any
measure that is finite on compact sets. -/
theorem exists_hasDualIntegral_of_isLocallyConstant [TopologicalSpace X] [OpensMeasurableSpace X]
    [IsFiniteMeasureOnCompacts μ] {F : X → W} (hF : IsLocallyConstant F) {C : Set X}
    (hC : IsCompact C) (hzero : ∀ x ∉ C, F x = 0) : ∃ w, HasDualIntegral μ F w := by
  classical
  have hfin : (F '' C).Finite := by
    have := isCompact_iff_compactSpace.mp hC
    have h := (hF.comp_continuous (continuous_subtype_val : Continuous ((↑) : C → X))).range_finite
    rwa [Set.range_comp, Subtype.range_coe] at h
  let T : Finset W := hfin.toFinset.filter (· ≠ 0)
  have hsub : ∀ w ∈ T, F ⁻¹' {w} ⊆ C := by
    intro w hw x hx
    by_contra hxC
    have hx' : F x = w := hx
    rw [hzero x hxC] at hx'
    exact (Finset.mem_filter.mp hw).2 hx'.symm
  have hint := HasDualIntegral.sum (μ := μ) T
    (F := fun w => (F ⁻¹' {w}).indicator fun _ => w) (w := fun w => (μ.real (F ⁻¹' {w}) : ℂ) • w)
    (fun w hw => hasDualIntegral_indicator (hF.isOpen_fiber w).measurableSet
      (ne_top_of_le_ne_top (hC.measure_lt_top).ne (measure_mono (hsub w hw))) w)
  refine ⟨_, hint.congr fun x => ?_⟩
  by_cases hx : F x = 0
  · rw [hx]
    apply Finset.sum_eq_zero
    intro w hw
    have hw0 : w ≠ 0 := (Finset.mem_filter.mp hw).2
    rw [Set.indicator_of_notMem]
    intro hxw
    exact hw0 ((show F x = w from hxw).symm.trans hx)
  · have hxC : x ∈ C := by
      by_contra hxC
      exact hx (hzero x hxC)
    have hxT : F x ∈ T := Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr ⟨x, hxC, rfl⟩, hx⟩
    rw [Finset.sum_eq_single (F x)]
    · simp
    · intro w _ hw
      rw [Set.indicator_of_notMem]
      exact fun hxw => hw (show F x = w from hxw).symm
    · exact fun h => (h hxT).elim

end Langlands.DualIntegral

namespace Langlands.LinearDescent

variable {A B C : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup C] [Module ℂ C]

/-- A linear map `T : A → C` killing the kernel of a surjection `φ : A → B` descends to `B`. -/
def descend (φ : A →ₗ[ℂ] B) (hφ : Function.Surjective φ) (T : A →ₗ[ℂ] C)
    (h : LinearMap.ker φ ≤ LinearMap.ker T) : B →ₗ[ℂ] C :=
  ((LinearMap.ker φ).liftQ T h).comp (φ.quotKerEquivOfSurjective hφ).symm.toLinearMap

theorem descend_apply (φ : A →ₗ[ℂ] B) (hφ : Function.Surjective φ) (T : A →ₗ[ℂ] C)
    (h : LinearMap.ker φ ≤ LinearMap.ker T) (a : A) : descend φ hφ T h (φ a) = T a := by
  rw [descend, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

/-- A map induced on a quotient, at the class of a multiple. -/
theorem liftQ_mk_smul (S : Submodule ℂ A) (L : A →ₗ[ℂ] C) (h : S ≤ LinearMap.ker L) (c : ℂ)
    (a : A) : S.liftQ L h (Submodule.Quotient.mk (c • a)) = c • L a := by
  rw [Submodule.Quotient.mk_smul, map_smul, Submodule.liftQ_apply]

end Langlands.LinearDescent

namespace Langlands.SmoothRep

universe uG uV uW

variable {M : Type uG} [Group M] [TopologicalSpace M]

/-- The kernel of an equivariant endomorphism of a smooth representation, as a smooth
representation. -/
abbrev kerSmooth (W : SmoothRep.{0, uG, uV} ℂ M)
    (T : W.representation.IntertwiningMap W.representation) : SmoothRep.{0, uG, uV} ℂ M :=
  SmoothRep.of T.ker.toRepresentation (by
    intro x
    obtain ⟨H, hH⟩ := W.isSmooth x.1
    refine ⟨H, ?_⟩
    rw [fixedVectors, Representation.mem_invariants] at hH ⊢
    intro h
    exact Subtype.ext (hH h))

/-- The inclusion of the kernel. -/
abbrev kerSmoothι (W : SmoothRep.{0, uG, uV} ℂ M)
    (T : W.representation.IntertwiningMap W.representation) : kerSmooth W T ⟶ W :=
  SmoothRep.ofHom
    { toLinearMap := T.ker.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }

/-- Rigidity of natural surjections. Let `Q` be a functor-like assignment on smooth
representations of `M`, with an equivariant natural identification `e_W : Q(W) ≃ W`, and let
`I_W : Q(W) → W` be equivariant, natural and surjective for every `W`. Then every `I_W` is
injective. Indeed `T_W = I_W ∘ e_W⁻¹` is a natural surjective endomorphism of the identity;
on the kernel `K` of `T_W`, naturality along `K ↪ W` forces `T_K = 0`, while `T_K` is
surjective, so `K = 0`. -/
theorem injective_of_natural_surjective
    (Q : SmoothRep.{0, uG, uV} ℂ M → Rep.{uW} ℂ M)
    (Qmap : ∀ {W W' : SmoothRep.{0, uG, uV} ℂ M}, (W ⟶ W') → ((Q W) →ₗ[ℂ] (Q W')))
    (e : ∀ W, (Q W).ρ.Equiv W.representation)
    (he : ∀ (W W' : SmoothRep.{0, uG, uV} ℂ M) (f : W ⟶ W') x,
      e W' (Qmap f x) = SmoothRep.hom f (e W x))
    (I : ∀ W, (Q W).ρ.IntertwiningMap W.representation)
    (hI : ∀ (W W' : SmoothRep.{0, uG, uV} ℂ M) (f : W ⟶ W') x,
      I W' (Qmap f x) = SmoothRep.hom f (I W x))
    (hsurj : ∀ W, Function.Surjective (I W)) (W : SmoothRep.{0, uG, uV} ℂ M) :
    Function.Injective (I W) := by
  let T : ∀ W : SmoothRep.{0, uG, uV} ℂ M,
      W.representation.IntertwiningMap W.representation :=
    fun W => (I W).comp (e W).symm.toIntertwiningMap
  have hT : ∀ (W W' : SmoothRep.{0, uG, uV} ℂ M) (f : W ⟶ W') y,
      T W' (SmoothRep.hom f y) = SmoothRep.hom f (T W y) := by
    intro W W' f y
    have h1 : (e W').symm (SmoothRep.hom f y) = Qmap f ((e W).symm y) := by
      apply EquivLike.injective (e W')
      rw [he, Representation.Equiv.apply_symm_apply, Representation.Equiv.apply_symm_apply]
    change I W' ((e W').symm (SmoothRep.hom f y)) = SmoothRep.hom f (I W ((e W).symm y))
    rw [h1, hI]
  have hTsurj : ∀ W, Function.Surjective (T W) := by
    intro W y
    obtain ⟨x, hx⟩ := hsurj W y
    exact ⟨e W x, by simp [T, hx]⟩
  have hTinj : ∀ y, T W y = 0 → y = 0 := by
    intro y hy
    obtain ⟨z, hz⟩ := hTsurj (kerSmooth W (T W)) ⟨y, hy⟩
    have h := hT (kerSmooth W (T W)) W (kerSmoothι W (T W)) z
    have hz0 : T W z.1 = 0 := z.2
    have hy' : y = SmoothRep.hom (kerSmoothι W (T W)) (T (kerSmooth W (T W)) z) := by
      rw [hz]
      rfl
    rw [hy', ← h]
    exact hz0
  have hx : ∀ x, T W (e W x) = I W x := fun x => by
    change I W ((e W).symm (e W x)) = I W x
    rw [Representation.Equiv.symm_apply_apply]
  intro x x' hxx'
  exact EquivLike.injective (e W)
    (sub_eq_zero.mp (hTinj _ (by rw [map_sub, hx, hx, hxx', sub_self])))

/-- **Trivial twisting character.** Let `I_W : Q(W) → W` be surjective linear maps, for all smooth
representations `W`, twisted-equivariant for one function `χ` independent of `W`:
`I_W(m x) = χ(m) W(m)(I_W x)`. If every `Q(W)` is equivariantly isomorphic to `W`, then `χ = 1`:
for the trivial representation on `ℂ`, a preimage `x` of `1` satisfies `m x = x`, so
`1 = χ(m) · 1`. -/
theorem character_eq_one_of_surjective
    (Q : SmoothRep.{0, uG, uV} ℂ M → Rep.{uW} ℂ M)
    (e : ∀ W, (Q W).ρ.Equiv W.representation)
    (I : ∀ W : SmoothRep.{0, uG, uV} ℂ M, (Q W) →ₗ[ℂ] W)
    (hsurj : ∀ W, Function.Surjective (I W)) (χ : M → ℂ)
    (hχ : ∀ (W : SmoothRep.{0, uG, uV} ℂ M) (m : M) (x : Q W),
      I W ((Q W).ρ m x) = χ m • W.representation m (I W x))
    (m : M) : χ m = 1 := by
  let W₀ : SmoothRep.{0, uG, uV} ℂ M :=
    SmoothRep.of (Representation.trivial ℂ M (ULift.{uV} ℂ)) (fun _ => ⟨⊤, fun _ => rfl⟩)
  obtain ⟨x, hx⟩ := hsurj W₀ (ULift.up 1 : ULift.{uV} ℂ)
  have hQ : (Q W₀).ρ m x = x := by
    apply (e W₀).injective
    exact LinearMap.congr_fun ((e W₀).isIntertwining' m) x
  have h := hχ W₀ m x
  rw [hQ, hx] at h
  have h' : (ULift.up 1 : ULift.{uV} ℂ) = χ m • (ULift.up 1 : ULift.{uV} ℂ) := h
  have h'' := congrArg ULift.down h'
  simp only [ULift.smul_down, smul_eq_mul, mul_one] at h''
  exact h''.symm

/-- **Identification by natural twisted-equivariant surjections.** In the setting of
`injective_of_natural_surjective`, if the maps `I_W` are only known to be twisted-equivariant
for a function `χ` independent of `W`, they are equivariant isomorphisms. -/
theorem exists_equiv_of_natural_surjective
    (Q : SmoothRep.{0, uG, uV} ℂ M → Rep.{uW} ℂ M)
    (Qmap : ∀ {W W' : SmoothRep.{0, uG, uV} ℂ M}, (W ⟶ W') → ((Q W) →ₗ[ℂ] (Q W')))
    (e : ∀ W, (Q W).ρ.Equiv W.representation)
    (he : ∀ (W W' : SmoothRep.{0, uG, uV} ℂ M) (f : W ⟶ W') x,
      e W' (Qmap f x) = SmoothRep.hom f (e W x))
    (I : ∀ W : SmoothRep.{0, uG, uV} ℂ M, (Q W) →ₗ[ℂ] W)
    (hI : ∀ (W W' : SmoothRep.{0, uG, uV} ℂ M) (f : W ⟶ W') x,
      I W' (Qmap f x) = SmoothRep.hom f (I W x))
    (hsurj : ∀ W, Function.Surjective (I W)) (χ : M → ℂ)
    (hχ : ∀ (W : SmoothRep.{0, uG, uV} ℂ M) (m : M) (x : Q W),
      I W ((Q W).ρ m x) = χ m • W.representation m (I W x))
    (W : SmoothRep.{0, uG, uV} ℂ M) :
    ∃ E : (Q W).ρ.Equiv W.representation, ∀ x, E x = I W x := by
  have hχ1 := character_eq_one_of_surjective Q e I hsurj χ hχ
  let I' : ∀ W : SmoothRep.{0, uG, uV} ℂ M, (Q W).ρ.IntertwiningMap W.representation :=
    fun W =>
      { toLinearMap := I W
        isIntertwining' := fun m => by
          ext x
          change I W ((Q W).ρ m x) = W.representation m (I W x)
          rw [hχ W m x, hχ1 m, one_smul] }
  have hinj := injective_of_natural_surjective Q Qmap e he I' hI hsurj W
  exact ⟨Representation.IntertwiningMap.ofBijective (I' W) ⟨hinj, hsurj W⟩, fun _ => rfl⟩

end Langlands.SmoothRep
