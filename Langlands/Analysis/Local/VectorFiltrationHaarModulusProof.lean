import Langlands.Analysis.Local.VectorFiltrationHaarModulusStatement
import Langlands.Analysis.Local.NormalSubgroupHaarModulus
import Langlands.Analysis.Local.CompactOpenCoverUnimodularityProof
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof
import Langlands.HarmonicAnalysis.HaarConjugacy

/-!
# Proof of Haar moduli along a filtration with vector-space quotients
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal Pointwise

namespace Langlands.HaarModulus.VectorFiltration

universe u v

section General

/-- Two multiples of a measure by factors in `ℝ≥0` agree only for equal factors, given a
set of positive finite measure. -/
theorem smul_measure_cancel {X : Type*} [MeasurableSpace X] (ρ : Measure X)
    {s : Set X} (hs0 : ρ s ≠ 0) (hsT : ρ s ≠ ∞) {a b : ℝ≥0} (h : a • ρ = b • ρ) : a = b := by
  have h' := congrArg (fun m : Measure X => m s) h
  simp only [Measure.smul_apply, nnreal_smul_coe_apply] at h'
  exact_mod_cast (ENNReal.mul_left_inj hs0 hsT).1 h'

/-- Two multiples of a Haar measure agree only for equal factors. -/
theorem haar_smul_cancel {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (ρ : Measure X) [IsHaarMeasure ρ] {a b : ℝ≥0} (h : a • ρ = b • ρ) : a = b := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : X)
  exact smul_measure_cancel ρ (measure_pos_of_mem_nhds ρ hK1).ne' hK.measure_lt_top.ne h

/-- The topological group isomorphism `A.subgroupOf B ≃ₜ* A` for `A ≤ B`. -/
def subgroupOfContinuousMulEquiv {G : Type*} [Group G] [TopologicalSpace G]
    {A B : Subgroup G} (h : A ≤ B) : (A.subgroupOf B) ≃ₜ* A where
  toMulEquiv := Subgroup.subgroupOfEquivOfLe h
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

end General

section Field

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

open Classical in
/-- The Haar scaling character of `kˣ` on `k`, extended by zero. -/
def scalingWithZero : k →*₀ ℝ≥0 where
  toFun a := if h : a = 0 then 0 else distribHaarChar k (Units.mk0 a h)
  map_zero' := by simp
  map_one' := by
    simp only [one_ne_zero, ↓reduceDIte]
    have : Units.mk0 (1 : k) one_ne_zero = 1 := Units.ext rfl
    rw [this, map_one]
  map_mul' a b := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    simp only [mul_ne_zero ha hb, ha, hb, ↓reduceDIte, ← map_mul]
    congr 1
    exact Units.ext rfl

open Classical in
theorem scalingWithZero_of_ne_zero {a : k} (ha : a ≠ 0) :
    scalingWithZero a = distribHaarChar k (Units.mk0 a ha) := by
  change (if h : a = 0 then 0 else distribHaarChar k (Units.mk0 a h)) = _
  simp only [ha, ↓reduceDIte]

/-- Multiplication by a nonzero scalar pushes a regular additive Haar measure on `k`
forward to the inverse scaling factor times itself. -/
theorem map_mul_left_eq_scalingWithZero [MeasurableSpace k] [BorelSpace k]
    (ν : Measure k) [ν.IsAddHaarMeasure] [ν.Regular] (a : k) (ha : a ≠ 0) :
    ν.map (fun x => a * x) = (scalingWithZero a)⁻¹ • ν := by
  ext s hs
  have hm : Measurable (fun x : k => a * x) := (continuous_const.mul continuous_id).measurable
  rw [Measure.map_apply hm hs, Measure.smul_apply, nnreal_smul_coe_apply]
  set w := Units.mk0 a ha
  have hpre : (fun x : k => a * x) ⁻¹' s = w⁻¹ • s := by
    ext x
    rw [Set.mem_inv_smul_set_iff, Set.mem_preimage]
    rfl
  rw [hpre, ← distribHaarChar_mul ν w⁻¹ s, map_inv, scalingWithZero_of_ne_zero ha]

/-- **The Haar modulus on a vector quotient.** If `q` is a continuous open surjective
homomorphism from `H` onto `k^n` with kernel `K`, intertwining `α` with a linear
automorphism `L`, then the Haar modulus of the automorphism of `H ⧸ K` induced by `α` is
`|det L|`. -/
theorem quotient_mulEquivHaarChar_eq
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (K : Subgroup H) [K.Normal] [LocallyCompactSpace (H ⧸ K)]
    [MeasurableSpace (H ⧸ K)] [BorelSpace (H ⧸ K)]
    (α : H ≃ₜ* H) (hα : ∀ x : H, α x ∈ K ↔ x ∈ K) {n : ℕ} (q : H → Fin n → k)
    (hqmul : ∀ x y, q (x * y) = q x + q y) (hqK : ∀ x, q x = 0 ↔ x ∈ K)
    (hqc : Continuous q) (hqo : IsOpenMap q) (hqs : Function.Surjective q)
    (L : (Fin n → k) ≃ₗ[k] (Fin n → k)) (hqL : ∀ x, q (α x) = L (q x)) :
    mulEquivHaarChar (Langlands.QuotientIntegration.quotientGroupAutomorphism K α hα) =
      distribHaarChar k (LinearEquiv.det L) := by
  let : MeasurableSpace k := borel k
  have : BorelSpace k := ⟨rfl⟩
  have : SecondCountableTopology k :=
    Langlands.HarmonicAnalysis.GeneralLocalField.secondCountableTopology k
  have : T2Space k := Langlands.HarmonicAnalysis.GeneralLocalField.t2Space k
  -- `q` as a group homomorphism to `Multiplicative (k^n)`.
  have hq1 : q 1 = 0 := by
    have h := hqmul 1 1
    rw [mul_one] at h
    exact left_eq_add.mp h
  let qh : H →* Multiplicative (Fin n → k) :=
    { toFun := fun x => Multiplicative.ofAdd (q x)
      map_one' := by rw [hq1]; rfl
      map_mul' := fun x y => by rw [hqmul]; rfl }
  have hle : K ≤ qh.ker := fun x hx => by
    rw [MonoidHom.mem_ker]
    change Multiplicative.ofAdd (q x) = 1
    rw [(hqK x).2 hx]; rfl
  let qQ : H ⧸ K → Fin n → k := fun z => Multiplicative.toAdd (QuotientGroup.lift K qh hle z)
  have hqQ_mk : ∀ x : H, qQ (x : H ⧸ K) = q x := fun x => rfl
  have hqQ_mul : ∀ z w, qQ (z * w) = qQ z + qQ w := fun z w => by
    change Multiplicative.toAdd (QuotientGroup.lift K qh hle (z * w)) = _
    rw [map_mul]; rfl
  have hqQc : Continuous qQ := (QuotientGroup.isQuotientMap_mk K).continuous_iff.2 hqc
  have hqQo : IsOpenMap qQ := by
    intro U hU
    rw [← Set.image_preimage_eq U (QuotientGroup.mk_surjective (s := K)), Set.image_image]
    exact hqo _ (hU.preimage QuotientGroup.continuous_mk)
  have hqQi : Function.Injective qQ := by
    intro z w hzw
    induction z using QuotientGroup.induction_on with
    | H x =>
    induction w using QuotientGroup.induction_on with
    | H y =>
    rw [hqQ_mk, hqQ_mk] at hzw
    rw [QuotientGroup.eq]
    apply (hqK _).1
    have hinv : q x⁻¹ = -q x := by
      have h := hqmul x⁻¹ x
      rw [inv_mul_cancel, hq1] at h
      exact eq_neg_of_add_eq_zero_left h.symm
    rw [hqmul, hinv, hzw, neg_add_cancel]
  have hqQs : Function.Surjective qQ := fun v => by
    obtain ⟨x, rfl⟩ := hqs v
    exact ⟨x, rfl⟩
  let e : (H ⧸ K) ≃ₜ (Fin n → k) :=
    (Equiv.ofBijective qQ ⟨hqQi, hqQs⟩).toHomeomorphOfContinuousOpen hqQc hqQo
  have he_apply : ∀ z, e z = qQ z := fun z => rfl
  let αQ := Langlands.QuotientIntegration.quotientGroupAutomorphism K α hα
  have hcomm : (e : H ⧸ K → Fin n → k) ∘ αQ = L ∘ e := by
    funext z
    induction z using QuotientGroup.induction_on with
    | H x => exact hqL x
  -- Transport a Haar measure of the quotient to `k^n`.
  let μQ : Measure (H ⧸ K) := haar
  let ρ : Measure (Fin n → k) := μQ.map e
  have he : Measurable e := e.continuous.measurable
  have hes : Measurable e.symm := e.symm.continuous.measurable
  have hρapply : ∀ s, ρ s = μQ (e ⁻¹' s) := fun s => e.toMeasurableEquiv.map_apply s
  have hρ : ρ.IsAddHaarMeasure :=
    { toIsAddLeftInvariant := ⟨fun v => by
        obtain ⟨w, rfl⟩ := e.surjective v
        have hc : (fun x => e w + x) ∘ e = e ∘ (fun z => w * z) := by
          funext z
          simp only [Function.comp_apply, he_apply, hqQ_mul]
        change Measure.map (fun x => e w + x) (Measure.map e μQ) = Measure.map e μQ
        have hadd : Measurable (fun x : Fin n → k => e w + x) :=
          (by fun_prop : Continuous fun x : Fin n → k => e w + x).measurable
        have hmul : Measurable (fun z : H ⧸ K => w * z) :=
          (by fun_prop : Continuous fun z : H ⧸ K => w * z).measurable
        rw [Measure.map_map hadd he, hc, ← Measure.map_map he hmul, map_mul_left_eq_self]⟩
      toIsFiniteMeasureOnCompacts := ⟨fun C hC => by
        rw [hρapply]
        exact (e.isCompact_preimage.2 hC).measure_lt_top⟩
      toIsOpenPosMeasure := ⟨fun U hU hne => by
        rw [hρapply]
        exact (hU.preimage e.continuous).measure_ne_zero μQ (hne.preimage e.surjective)⟩ }
  -- Determinant scaling on `k^n`.
  let ν : Measure k := addHaar
  set M := LinearMap.toMatrix' (L : (Fin n → k) →ₗ[k] (Fin n → k)) with hMdef
  have hdetM : M.det = (LinearEquiv.det L : k) := by
    rw [hMdef, LinearMap.det_toMatrix', LinearEquiv.coe_det]
  have hM : M.det ≠ 0 := by rw [hdetM]; exact (LinearEquiv.det L).ne_zero
  have hmapL : ρ.map L = (scalingWithZero M.det)⁻¹ • ρ := by
    have h := Langlands.HarmonicAnalysis.haarMeasure_map_matrix ν scalingWithZero
      (fun a ha => map_mul_left_eq_scalingWithZero ν a ha) ρ hM
    rw [hMdef, Matrix.toLin'_toMatrix', LinearEquiv.coe_coe] at h
    rw [← hMdef] at h
    exact h
  have hχ : scalingWithZero M.det = distribHaarChar k (LinearEquiv.det L) := by
    rw [scalingWithZero_of_ne_zero hM]
    congr 1
    exact Units.ext hdetM
  -- Pull the scaling back to the quotient.
  have hLc : Measurable (L : (Fin n → k) → Fin n → k) :=
    (LinearMap.continuous_on_pi (L : (Fin n → k) →ₗ[k] (Fin n → k))).measurable
  have hαQ : Measurable (αQ : H ⧸ K → H ⧸ K) := αQ.continuous.measurable
  have hmapQ : μQ.map αQ = (scalingWithZero M.det)⁻¹ • μQ := by
    have h1 : (μQ.map αQ).map e = (scalingWithZero M.det)⁻¹ • ρ := by
      rw [Measure.map_map he hαQ, hcomm, ← Measure.map_map hLc he, hmapL]
    have hback : ∀ ν' : Measure (H ⧸ K), (ν'.map e).map e.symm = ν' := fun ν' => by
      rw [Measure.map_map hes he]
      have hid : (e.symm ∘ e : H ⧸ K → H ⧸ K) = id := funext fun a => e.symm_apply_apply a
      rw [hid, Measure.map_id]
    have h2 := congrArg (Measure.map e.symm) h1
    rw [hback, Measure.map_smul _ hes.aemeasurable, hback] at h2
    exact h2
  have hscale := mulEquivHaarChar_smul_map μQ αQ
  rw [hmapQ, smul_smul] at hscale
  have hprod : mulEquivHaarChar αQ * (scalingWithZero M.det)⁻¹ = 1 :=
    haar_smul_cancel μQ (by rw [hscale, one_smul])
  have hne : scalingWithZero M.det ≠ 0 := by
    rw [hχ]
    exact ((Group.isUnit (LinearEquiv.det L)).map (distribHaarChar k)).ne_zero
  rw [← hχ]
  rw [mul_inv_eq_one₀ hne] at hprod
  exact hprod

/-- **One step of the dévissage.** -/
theorem step_mulEquivHaarChar
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [LocallyCompactSpace H]
    (hcover : ∀ x : H, ∃ C : OpenSubgroup H, IsCompact (C : Set H) ∧ x ∈ C)
    [MeasurableSpace H] [BorelSpace H]
    (K : Subgroup H) [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (α : H ≃ₜ* H) (hα : ∀ x : H, α x ∈ K ↔ x ∈ K) {n : ℕ} (q : H → Fin n → k)
    (hqmul : ∀ x y, q (x * y) = q x + q y) (hqK : ∀ x, q x = 0 ↔ x ∈ K)
    (hqc : Continuous q) (hqo : IsOpenMap q) (hqs : Function.Surjective q)
    (L : (Fin n → k) ≃ₗ[k] (Fin n → k)) (hqL : ∀ x, q (α x) = L (q x)) :
    mulEquivHaarChar α =
      mulEquivHaarChar (Langlands.QuotientIntegration.subgroupAutomorphism K α hα) *
        distribHaarChar k (LinearEquiv.det L) := by
  have : T2Space k := Langlands.HarmonicAnalysis.GeneralLocalField.t2Space k
  have hq1 : q 1 = 0 := by
    have h := hqmul 1 1
    rw [mul_one] at h
    exact left_eq_add.mp h
  have hqinv : ∀ x, q x⁻¹ = -q x := fun x => by
    have h := hqmul x⁻¹ x
    rw [inv_mul_cancel, hq1] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have : K.Normal := ⟨fun x hx y => by
    rw [← hqK] at hx ⊢
    rw [hqmul, hqmul, hqinv, hx, add_zero, add_neg_cancel]⟩
  have hK : IsClosed (K : Set H) := by
    have hset : (K : Set H) = q ⁻¹' {0} := Set.ext fun x => (hqK x).symm
    rw [hset]
    exact isClosed_singleton.preimage hqc
  obtain ⟨hGu, hHu⟩ := Langlands.Haar.compactOpenCoverUnimodularity hcover
  let : MeasurableSpace (H ⧸ K) := borel _
  have : BorelSpace (H ⧸ K) := ⟨rfl⟩
  let μG : Measure H := haar
  let μH : Measure K := haar
  have := hGu μG
  have := hHu K hK μH
  rw [Langlands.QuotientIntegration.mulEquivHaarChar_eq_mul_quotientGroupAutomorphism K hK μG μH
    α hα, quotient_mulEquivHaarChar_eq K α hα q hqmul hqK hqc hqo hqs L hqL]

end Field

attribute [local instance] Langlands.HaarModulus.subgroupMeasurableSpace
  Langlands.HaarModulus.subgroupBorelSpace

/-- Proof of `VectorFiltrationHaarModulusStatement`. -/
theorem vectorFiltrationHaarModulus : VectorFiltrationHaarModulusStatement.{u, v} := by
  intro k _ _ _ _ G _ _ _ _ _ U hU hcover g N F hF0 hFN hFle _hFg n q hqmul hqker hqc hqo hqs
    L hqL
  have : T2Space k := Langlands.HarmonicAnalysis.GeneralLocalField.t2Space k
  subst hF0
  have hle0 : ∀ r ≤ N, F r ≤ F 0 := by
    intro r hr
    induction r with
    | zero => exact le_rfl
    | succ r ih => exact (hFle r (by omega)).trans (ih (by omega))
  have hclosed : ∀ r ≤ N, IsClosed (F r : Set G) := by
    intro r hr
    induction r with
    | zero => exact hU
    | succ r ih =>
      have hFr := ih (by omega)
      have hset : (F (r + 1) : Set G) = Subtype.val '' (q r ⁻¹' {0}) := by
        ext x
        constructor
        · intro hx
          exact ⟨⟨x, hFle r (by omega) hx⟩, (hqker r (by omega) _).2 hx, rfl⟩
        · rintro ⟨y, hy, rfl⟩
          exact (hqker r (by omega) y).1 hy
      rw [hset]
      exact hFr.isClosedEmbedding_subtypeVal.isClosedMap _
        (isClosed_singleton.preimage (hqc r (by omega)))
  have hcoverF : ∀ r ≤ N, ∀ x : F r, ∃ C : OpenSubgroup (F r),
      IsCompact (C : Set (F r)) ∧ x ∈ C := by
    intro r hr x
    obtain ⟨C, hC, hxC⟩ := hcover ⟨x, hle0 r hr x.2⟩
    let ι : F r →* F 0 := Subgroup.inclusion (hle0 r hr)
    have hι : Continuous ι := continuous_subtype_val.subtype_mk _
    refine ⟨C.comap ι hι, ?_, hxC⟩
    have hset : ((C.comap ι hι : OpenSubgroup (F r)) : Set (F r)) =
        Subtype.val ⁻¹' (Subtype.val '' (C : Set (F 0))) := by
      ext y
      constructor
      · intro hy
        exact ⟨ι y, hy, rfl⟩
      · rintro ⟨z, hz, hzy⟩
        have : ι y = z := Subtype.ext hzy.symm
        change ι y ∈ C
        rw [this]
        exact hz
    rw [hset]
    exact (hclosed r hr).isClosedEmbedding_subtypeVal.isCompact_preimage
      (hC.image continuous_subtype_val)
  have claim : ∀ j r (hrj : r + j = N) (h : (g : G) ∈ Subgroup.normalizer (F r : Set G)),
      (haveI := (hclosed r (by omega)).locallyCompactSpace;
        mulEquivHaarChar (normalizerConj (F r) ⟨g, h⟩)) =
        ∏ s ∈ Finset.Ico r N, MeasureTheory.distribHaarChar k (LinearEquiv.det (L s)) := by
    intro j
    induction j with
    | zero =>
      intro r hrj h
      obtain rfl : r = N := by omega
      have := (hclosed r le_rfl).locallyCompactSpace
      have hbot : ∀ z ∈ F r, z = (1 : G) := fun z hz => by
        rw [hFN, Subgroup.mem_bot] at hz
        exact hz
      have : Subsingleton (F r) :=
        ⟨fun x y => Subtype.ext ((hbot _ x.2).trans (hbot _ y.2).symm)⟩
      rw [mulEquivHaarChar_eq_one_of_compactSpace, Finset.Ico_self, Finset.prod_empty]
    | succ j ih =>
      intro r hrj h
      have hr : r < N := by omega
      have h' : (g : G) ∈ Subgroup.normalizer (F (r + 1) : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          have hxr : x ∈ F r := hFle r hr hx
          have hyr : (g : G) * x * (g : G)⁻¹ ∈ F r :=
            (Subgroup.mem_normalizer_iff.mp h x).mp hxr
          have hL := hqL r hr ⟨x, hxr⟩ ⟨_, hyr⟩ rfl
          exact (hqker r hr ⟨_, hyr⟩).1 (by rw [hL, (hqker r hr ⟨x, hxr⟩).2 hx, map_zero])
        · intro hy
          have hyr : (g : G) * x * (g : G)⁻¹ ∈ F r := hFle r hr hy
          have hxr : x ∈ F r := (Subgroup.mem_normalizer_iff.mp h x).mpr hyr
          have hL := hqL r hr ⟨x, hxr⟩ ⟨_, hyr⟩ rfl
          have h0 : L r (q r ⟨x, hxr⟩) = 0 := by
            rw [← hL]
            exact (hqker r hr ⟨_, hyr⟩).2 hy
          exact (hqker r hr ⟨x, hxr⟩).1 ((L r).map_eq_zero_iff.mp h0)
      have := (hclosed r hr.le).locallyCompactSpace
      have := (hclosed (r + 1) hr).locallyCompactSpace
      let K' : Subgroup (F r) := (F (r + 1)).subgroupOf (F r)
      have : LocallyCompactSpace K' :=
        (IsClosed.preimage continuous_subtype_val (hclosed (r + 1) hr)).locallyCompactSpace
      let α := normalizerConj (F r) ⟨g, h⟩
      have hqK : ∀ x : F r, q r x = 0 ↔ x ∈ K' := fun x => hqker r hr x
      have hqLα : ∀ x : F r, q r (α x) = L r (q r x) := fun x => hqL r hr x (α x) rfl
      have hα : ∀ x : F r, α x ∈ K' ↔ x ∈ K' := fun x => by
        rw [← hqK, ← hqK, hqLα, LinearEquiv.map_eq_zero_iff]
      have hstep := step_mulEquivHaarChar (hcoverF r hr.le) K' α hα (q r) (hqmul r hr) hqK
        (hqc r hr) (hqo r hr) (hqs r hr) (L r) hqLα
      have htrans : mulEquivHaarChar (Langlands.QuotientIntegration.subgroupAutomorphism K' α hα) =
          mulEquivHaarChar (normalizerConj (F (r + 1)) ⟨g, h'⟩) :=
        Langlands.Geometric.haarChar_eq_of_conjugacy
          (subgroupOfContinuousMulEquiv (hFle r hr)) _ _
          (fun x => Subtype.ext rfl)
      rw [Finset.prod_eq_prod_Ico_succ_bot hr, ← ih (r + 1) (by omega) h', ← htrans]
      exact hstep.trans (mul_comm _ _)
  have hfinal := claim N 0 (by omega) g.2
  rw [Finset.range_eq_Ico]
  exact hfinal

end Langlands.HaarModulus.VectorFiltration
