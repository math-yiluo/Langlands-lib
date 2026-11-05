import Langlands.HarmonicAnalysis.DiscreteFourierUniqueness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralProjection

/-! # Fourier inversion on `A_G` for `p_χ` (Waldspurger, proof of Theorem VIII.1.1)

Waldspurger, VIII.5 (printed p. 332): "Supposons `φ ≠ 0`. Par inversion de Fourier sur le
groupe `A_G`, il existe `χ ∈ Â_G` tel que `p_χ φ ≠ 0`." This module proves that step for
abstract data:

* for an open subgroup `Z₀` of a group `Z` with left invariant measure `μ` and countable
  `Z / Z₀`, the integral of an integrable right `Z₀`-invariant function is
  `μ(Z₀) ∑_{q ∈ Z/Z₀} F(q̇)`;
* if moreover `Z` is commutative, `Z / Z₀` is finitely generated and `0 < μ(Z₀) < ∞`, an
  integrable right `Z₀`-invariant `F` with `∫_Z χ⁻¹(z) F(z) dμ(z) = 0` for every unitary
  continuous character `χ` is zero;
* for `A` a closed central subgroup of `G` such that `A / (A ∩ K)` is finitely generated for
  every compact open subgroup `K`, and `f ∈ C(G)`: if `p_χ f = 0` for every continuous unitary
  character `χ` of `A`, then `f = 0`.
-/

noncomputable section

open MeasureTheory Langlands.HarmonicAnalysis.DiscreteFourier
open scoped ENNReal

namespace Langlands.HarishChandraSchwartz

universe u v

section Coset

variable {Z : Type u} [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z]
  [MeasurableSpace Z] [OpensMeasurableSpace Z] {Z₀ : Subgroup Z}

omit [TopologicalSpace Z] [IsTopologicalGroup Z] [MeasurableSpace Z] [OpensMeasurableSpace Z] in
variable (Z₀) in
/-- The values `q ↦ F(q̇)` of `F : Z → E` at the representatives `q̇ = Quotient.out q` of the
left cosets `q ∈ Z / Z₀`. For right `Z₀`-invariant `F` this is the function induced by `F` on
`Z / Z₀` (`cosetValues_mk`). -/
def cosetValues {E : Type v} (F : Z → E) (q : Z ⧸ Z₀) : E :=
  F q.out

omit [TopologicalSpace Z] [IsTopologicalGroup Z] [MeasurableSpace Z] [OpensMeasurableSpace Z] in
/-- A right `Z₀`-invariant function takes at `z` its value at the representative of `z Z₀`. -/
theorem cosetValues_mk {E : Type v} {F : Z → E} (hF : ∀ z, ∀ b ∈ Z₀, F (z * b) = F z) (z : Z) :
    cosetValues Z₀ F (QuotientGroup.mk z) = F z := by
  have h : (QuotientGroup.mk z : Z ⧸ Z₀).out⁻¹ * z ∈ Z₀ :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk z : Z ⧸ Z₀))
  rw [cosetValues, ← hF _ _ h, mul_inv_cancel_left]

omit [TopologicalSpace Z] [IsTopologicalGroup Z] [MeasurableSpace Z] [OpensMeasurableSpace Z] in
theorem preimage_mk_singleton (q : Z ⧸ Z₀) :
    (QuotientGroup.mk ⁻¹' {q} : Set Z) = (fun h => q.out⁻¹ * h) ⁻¹' (Z₀ : Set Z) := by
  ext z
  simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  rw [eq_comm, QuotientGroup.eq]

/-- **Integration over the cosets of an open subgroup**: for `Z₀` open with `Z / Z₀`
countable, `μ` left invariant and `F` integrable and right `Z₀`-invariant,
`∑_{q ∈ Z/Z₀} μ(Z₀) F(q̇) = ∫_Z F dμ`, where `q̇ = Quotient.out q`. -/
theorem hasSum_integral_quotient [MeasurableMul Z] [Countable (Z ⧸ Z₀)] {μ : Measure Z}
    [μ.IsMulLeftInvariant]
    (hZ₀ : IsOpen (Z₀ : Set Z)) {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {F : Z → E} (hF : ∀ z, ∀ b ∈ Z₀, F (z * b) = F z) (hint : Integrable F μ) :
    HasSum (fun q : Z ⧸ Z₀ => (μ (Z₀ : Set Z)).toReal • cosetValues Z₀ F q) (∫ z, F z ∂μ) := by
  have : DiscreteTopology (Z ⧸ Z₀) := QuotientGroup.discreteTopology hZ₀
  let s : Z ⧸ Z₀ → Set Z := fun q => QuotientGroup.mk ⁻¹' {q}
  have hs : ∀ q, MeasurableSet (s q) := fun q =>
    ((isOpen_discrete {q}).preimage QuotientGroup.continuous_mk).measurableSet
  have hd : Pairwise (Function.onFun Disjoint s) := fun q q' hne =>
    Set.disjoint_left.mpr fun z hz hz' => hne ((Set.mem_singleton_iff.mp hz).symm.trans
      (Set.mem_singleton_iff.mp hz'))
  have hU : (⋃ q, s q) = Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨QuotientGroup.mk z, rfl⟩
  have h := hasSum_integral_iUnion hs hd (by rw [hU]; exact hint.integrableOn)
  rw [hU, Measure.restrict_univ] at h
  refine h.congr_fun fun q => ?_
  have hc : ∫ z in s q, F z ∂μ = ∫ _ in s q, cosetValues Z₀ F q ∂μ := by
    refine setIntegral_congr_fun (hs q) fun z hz => ?_
    have hz' : (QuotientGroup.mk z : Z ⧸ Z₀) = q := hz
    rw [← hz', cosetValues_mk hF]
  rw [hc, setIntegral_const, measureReal_def]
  congr 2
  rw [show s q = QuotientGroup.mk ⁻¹' {q} from rfl, preimage_mk_singleton,
    measure_preimage_mul]

/-- **Fourier inversion on a commutative group with an open subgroup of finitely generated
quotient**: let `Z` be commutative, `Z₀` an open subgroup with `Z / Z₀` finitely generated,
`μ` left invariant with `0 < μ(Z₀) < ∞`, and `F` integrable and right `Z₀`-invariant. If
`∫_Z χ(z)⁻¹ F(z) dμ(z) = 0` for every unitary continuous character `χ`, then `F = 0`. -/
theorem eq_zero_of_integral_inv_character_mul_eq_zero [MeasurableMul Z]
    (hcomm : ∀ a b : Z, a * b = b * a) [Z₀.Normal] [Group.FG (Z ⧸ Z₀)] {μ : Measure Z}
    [μ.IsMulLeftInvariant]
    (hZ₀ : IsOpen (Z₀ : Set Z)) (hpos : 0 < μ (Z₀ : Set Z)) (hfin : μ (Z₀ : Set Z) < ∞)
    {F : Z → ℂ} (hF : ∀ z, ∀ b ∈ Z₀, F (z * b) = F z) (hint : Integrable F μ)
    (h : ∀ χ : Z →* ℂˣ, (∀ z, ‖(χ z : ℂ)‖ = 1) → Continuous (fun z => (χ z : ℂ)) →
      ∫ z, (((χ z)⁻¹ : ℂˣ) : ℂ) * F z ∂μ = 0) :
    F = 0 := by
  let : CommGroup (Z ⧸ Z₀) :=
    { (inferInstance : Group (Z ⧸ Z₀)) with
      mul_comm := fun a b => by
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b => rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm] }
  have : Countable (Z ⧸ Z₀) := countable_of_fg
  have : DiscreteTopology (Z ⧸ Z₀) := QuotientGroup.discreteTopology hZ₀
  have hμ : (μ (Z₀ : Set Z)).toReal ≠ 0 := (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  let f : Z ⧸ Z₀ → ℂ := cosetValues Z₀ F
  have hf : Summable fun q => ‖f q‖ := by
    have hN := hasSum_integral_quotient (μ := μ) hZ₀ (F := fun z => ‖F z‖)
      (fun z b hb => by rw [hF z b hb]) hint.norm
    have := hN.summable.mul_left (μ (Z₀ : Set Z)).toReal⁻¹
    simpa only [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hμ, one_mul, cosetValues, f]
      using this
  have hf0 : f = 0 := by
    refine eq_zero_of_characterSum_eq_zero hf fun ψ hψ => ?_
    let χ : Z →* ℂˣ := ψ⁻¹.comp (QuotientGroup.mk' Z₀)
    have hcont : ∀ g : Z ⧸ Z₀ → ℂ, Continuous fun z : Z => g (QuotientGroup.mk z) := fun g =>
      continuous_of_discreteTopology.comp QuotientGroup.continuous_mk
    have hχinv : ∀ z, (((χ z)⁻¹ : ℂˣ) : ℂ) = ψ (QuotientGroup.mk z) := fun z => by
      simp [χ]
    have hχ1 : ∀ z, ‖(χ z : ℂ)‖ = 1 := fun z => by
      have : (χ z : ℂ) = ((ψ (QuotientGroup.mk z))⁻¹ : ℂˣ) := rfl
      rw [this, Units.val_inv_eq_inv_val, norm_inv, hψ, inv_one]
    have hχc : Continuous fun z => (χ z : ℂ) := by
      have : (fun z => (χ z : ℂ)) = fun z => (((ψ (QuotientGroup.mk z))⁻¹ : ℂˣ) : ℂ) := rfl
      rw [this]
      exact hcont fun q => (((ψ q)⁻¹ : ℂˣ) : ℂ)
    have h0 := h χ hχ1 hχc
    have hG : ∀ z, ∀ b ∈ Z₀, (((χ (z * b))⁻¹ : ℂˣ) : ℂ) * F (z * b) =
        (((χ z)⁻¹ : ℂˣ) : ℂ) * F z := fun z b hb => by
      rw [hχinv, hχinv, hF z b hb, QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff b).mpr hb, mul_one]
    have hGint : Integrable (fun z => (((χ z)⁻¹ : ℂˣ) : ℂ) * F z) μ := by
      refine hint.bdd_mul (c := 1) ?_ (Filter.Eventually.of_forall fun z => ?_)
      · simp only [hχinv]
        exact (hcont fun q => (ψ q : ℂ)).aestronglyMeasurable
      · rw [hχinv, hψ]
    have hS := hasSum_integral_quotient (μ := μ) hZ₀ hG hGint
    rw [h0] at hS
    have hS' : HasSum (fun q => (μ (Z₀ : Set Z)).toReal • ((ψ q : ℂ) * f q)) 0 := by
      refine hS.congr_fun fun q => ?_
      rw [cosetValues, hχinv, QuotientGroup.out_eq']
      rfl
    have := hS'.tsum_eq
    rw [tsum_const_smul'' (μ (Z₀ : Set Z)).toReal] at this
    · exact (smul_eq_zero.mp this).resolve_left hμ
  funext z
  rw [Pi.zero_apply, ← cosetValues_mk hF z]
  exact congrFun hf0 (QuotientGroup.mk z)

end Coset

section Central

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- `A / (A ∩ K)` is finitely generated for every compact open subgroup `K` of `G`: there is a
finite set `s ⊆ A` with `A = ⟨s⟩ (A ∩ K)`. -/
def HasFGCompactOpenQuotients (A : Subgroup G) : Prop :=
  ∀ K : CompactOpenSubgroup G, ∃ s : Set A, s.Finite ∧
    Subgroup.closure s ⊔ K.toSubgroup.subgroupOf A = ⊤

variable [IsTopologicalGroup G] [Nonempty (CompactOpenSubgroup G)] {A : Subgroup G}
  [MeasurableSpace A] [OpensMeasurableSpace A] {μA : Measure A} {Ξ σ : G → ℝ}

/-- **Fourier inversion on `A_G`** (Waldspurger, VIII.5): let `A` be a closed central subgroup
of `G` such that `A / (A ∩ K)` is finitely generated for every compact open subgroup `K`, and
`μ_A` a left invariant measure on `A`, positive on open sets and finite on compacts. If
`f ∈ C(G)` and `p_χ f = 0` for every continuous unitary character `χ` of `A` (Waldspurger's
`χ ∈ Â_G`), then `f = 0`. -/
theorem eq_zero_of_forall_centralProjection_eq_zero [MeasurableMul A] [μA.IsMulLeftInvariant]
    [μA.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μA] (hw : CentralWeights μA Ξ σ)
    (hA : IsClosed (A : Set G)) (hAc : A ≤ Subgroup.center G)
    (hFG : HasFGCompactOpenQuotients A)
    {f : G → ℂ} (hf : f ∈ schwartzSubmodule Ξ σ)
    (h : ∀ χ : A →* ℂˣ, (∀ a, ‖(χ a : ℂ)‖ = 1) → Continuous (fun a => (χ a : ℂ)) →
      centralProjection μA χ f = 0) : f = 0 := by
  obtain ⟨K, hK⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp hf
  set A₀ : Subgroup A := K.toSubgroup.subgroupOf A with hA₀
  have hcomm : ∀ a b : A, a * b = b * a := fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hAc b.2) a)
  have : A₀.Normal := ⟨fun n hn g => by rwa [hcomm g n, mul_inv_cancel_right]⟩
  have : Group.FG (A ⧸ A₀) := by
    obtain ⟨s, hs, hsK⟩ := hFG K
    refine Group.fg_iff.mpr ⟨QuotientGroup.mk '' s, ?_, hs.image _⟩
    have h1 : Subgroup.closure (QuotientGroup.mk '' s : Set (A ⧸ A₀)) =
        (Subgroup.closure s).map (QuotientGroup.mk' A₀) := by
      rw [MonoidHom.map_closure]
      rfl
    rw [h1, eq_top_iff]
    rintro x -
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    have ha : a ∈ Subgroup.closure s ⊔ A₀ := by rw [hsK]; exact Subgroup.mem_top a
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha
    refine ⟨y, hy, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr hz,
      mul_one]
  have hset : (A₀ : Set A) = Subtype.val ⁻¹' (K.toSubgroup : Set G) := by
    rw [hA₀, Subgroup.coe_subgroupOf]
    rfl
  have hopen : IsOpen (A₀ : Set A) := by
    rw [hset]
    exact K.1.isOpen.preimage continuous_subtype_val
  have hpos : 0 < μA (A₀ : Set A) := hopen.measure_pos μA ⟨1, A₀.one_mem⟩
  have hfin : μA (A₀ : Set A) < ∞ := by
    rw [hset]
    exact (hA.isClosedEmbedding_subtypeVal.isCompact_preimage K.2).measure_lt_top
  funext g
  have hF : ∀ a : A, ∀ b ∈ A₀, f (((a * b : A) : G) * g) = f ((a : G) * g) := fun a b hb => by
    rw [hcomm a b, Subgroup.coe_mul, mul_assoc]
    have hbK : (b : G) ∈ K.toSubgroup := hb
    have := hK.1 (b : G) hbK 1 (Subgroup.one_mem _) ((a : G) * g)
    rwa [mul_one] at this
  have hint : Integrable (fun a : A => f ((a : G) * g)) μA := hw.integrable_of_mem_level hK g
  have hzero := eq_zero_of_integral_inv_character_mul_eq_zero hcomm hopen hpos hfin
    (F := fun a : A => f ((a : G) * g)) hF hint fun χ hχ1 hχc => congrFun (h χ hχ1 hχc) g
  simpa using congrFun hzero 1

end Central

end Langlands.HarishChandraSchwartz
