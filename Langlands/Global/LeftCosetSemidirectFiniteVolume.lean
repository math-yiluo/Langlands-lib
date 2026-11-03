import Langlands.Global.LeftCosetHaarMeasure
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import Mathlib.MeasureTheory.Group.Prod

/-!
# Finite covolume for topological semidirect products

Let `H` be a locally compact second-countable group which is a topological semidirect
product of a normal subgroup `i : N → H` (an embedding) and a subgroup `j : M → H` split by
a continuous retraction `p : H → M` with kernel `i(N)`. Let `Γ ≤ H` be discrete and let
`ΓM ≤ M` be a discrete subgroup with `j(ΓM) ⊆ Γ` and finite Haar covolume in `M`. If the
translates of one compact set `K ⊆ N` by `i⁻¹(Γ)` cover `N`, then `Γ` has finite Haar
covolume in `H`.

The proof first shows that `M` is unimodular and that conjugation by `M` preserves the
Haar measure of `N`: the conjugation modulus is trivial on `ΓM` and descends to the finite
quotient `ΓM \ M`, where it would otherwise give a set of positive mass carried strictly
into itself by a measure-preserving right translation. The Haar measure of `H` is then a
positive multiple of the product measure transported along `(n, m) ↦ i n * j m`, and
`Γ` translates of `i(K) * j(E)` cover `H` for compact `K` and a fundamental domain `E`.
-/

noncomputable section

universe u v w

open MeasureTheory Set Topology
open scoped ENNReal NNReal Pointwise

namespace Langlands.Global.LeftCosetSpace

section Unimodular

variable {M : Type v} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
  [SecondCountableTopology M] [LocallyCompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- A discrete subgroup of finite Haar covolume forces unimodularity. -/
theorem isMulRightInvariant_haar_of_isFiniteMeasure (Γ : Subgroup M)
    (hΓ : IsDiscrete (Γ : Set M)) [IsFiniteMeasure (haarQuotientMeasure Γ hΓ)] :
    (Measure.haar : Measure M).IsMulRightInvariant := by
  set E := fundamentalDomain Γ hΓ
  have hE : IsFundamentalDomain Γ E (Measure.haar : Measure M) := isFundamentalDomain Γ hΓ _
  have hmass : haarQuotientMeasure Γ hΓ univ = (Measure.haar : Measure M) E :=
    quotientMeasure_univ Γ _ E
  have hEtop : (Measure.haar : Measure M) E ≠ ∞ := by
    rw [← hmass]; exact measure_ne_top _ _
  have hE0 : (Measure.haar : Measure M) E ≠ 0 := by
    rw [← hmass]
    exact fun h => haarQuotientMeasure_ne_zero Γ hΓ (Measure.measure_univ_eq_zero.mp h)
  have : Countable Γ := countable_of_isDiscrete Γ hΓ
  refine ⟨fun g => ?_⟩
  have hνeq := Measure.isMulLeftInvariant_eq_smul
    (Measure.map (· * g) (Measure.haar : Measure M)) Measure.haar
  have hE' : IsFundamentalDomain Γ ((· * g) ⁻¹' E) (Measure.haar : Measure M) :=
    hE.preimage_of_equiv (quasiMeasurePreserving_mul_right _ g) Function.bijective_id
      (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
  have h1 : Measure.map (· * g) (Measure.haar : Measure M) E = (Measure.haar : Measure M) E := by
    rw [Measure.map_apply (measurable_mul_const g) (measurableSet_fundamentalDomain Γ hΓ)]
    exact hE'.measure_eq hE
  have hc : Measure.haarScalarFactor (Measure.map (· * g) (Measure.haar : Measure M))
      Measure.haar = 1 := by
    have h2 := congrArg (fun μ : Measure M => μ E) hνeq
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
    rw [h1] at h2
    have h3 : (Measure.haar : Measure M) E * 1 = (Measure.haar : Measure M) E *
        (Measure.haarScalarFactor (Measure.map (· * g) (Measure.haar : Measure M))
          Measure.haar : ℝ≥0∞) := by
      rw [mul_one, mul_comm]; exact h2
    have h4 := (ENNReal.mul_right_inj hE0 hEtop).mp h3
    exact_mod_cast h4.symm
  rw [hνeq, hc, one_smul]

end Unimodular

section Automorphism

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

theorem haar_fundamentalDomain_ne_zero (Λ : Subgroup G) (hΛ : IsDiscrete (Λ : Set G)) :
    (Measure.haar : Measure G) (fundamentalDomain Λ hΛ) ≠ 0 := by
  rw [← quotientMeasure_univ Λ _ (fundamentalDomain Λ hΛ)]
  exact fun h => haarQuotientMeasure_ne_zero Λ hΛ (Measure.measure_univ_eq_zero.mp h)

theorem haar_fundamentalDomain_ne_top (Λ : Subgroup G) (hΛ : IsDiscrete (Λ : Set G))
    [IsFiniteMeasure (haarQuotientMeasure Λ hΛ)] :
    (Measure.haar : Measure G) (fundamentalDomain Λ hΛ) ≠ ∞ := by
  rw [← quotientMeasure_univ Λ _ (fundamentalDomain Λ hΛ)]
  exact measure_ne_top (haarQuotientMeasure Λ hΛ) univ

/-- A discrete subgroup whose translates of one compact set cover the group has finite
Haar covolume. -/
theorem isFiniteMeasure_haarQuotientMeasure_of_isCompact (Λ : Subgroup G)
    (hΛ : IsDiscrete (Λ : Set G)) {K : Set G} (hK : IsCompact K)
    (hcover : ∀ g, ∃ γ ∈ Λ, γ * g ∈ K) : IsFiniteMeasure (haarQuotientMeasure Λ hΛ) := by
  have : Countable Λ := countable_of_isDiscrete Λ hΛ
  have hK' : MeasurableSet (toMeasurable (Measure.haar : Measure G) K) :=
    measurableSet_toMeasurable _ _
  have himage : mk Λ '' toMeasurable (Measure.haar : Measure G) K = univ := by
    refine eq_univ_of_forall fun q => ?_
    obtain ⟨g, rfl⟩ := mk_surjective Λ q
    obtain ⟨γ, hγ, hγK⟩ := hcover g
    exact ⟨γ * g, subset_toMeasurable _ _ hγK, mk_subgroup_mul Λ ⟨γ, hγ⟩ g⟩
  have hle := quotientMeasure_image_le Λ (Measure.haar : Measure G)
    (isFundamentalDomain Λ hΛ Measure.haar) hK'
  rw [himage, measure_toMeasurable] at hle
  exact ⟨lt_of_le_of_lt hle hK.measure_lt_top⟩

/-- An automorphism preserving a discrete subgroup of finite Haar covolume preserves Haar
measure. -/
theorem mulEquivHaarChar_eq_one_of_forall_mem_iff (Λ : Subgroup G)
    (hΛ : IsDiscrete (Λ : Set G)) [IsFiniteMeasure (haarQuotientMeasure Λ hΛ)]
    (φ : G ≃ₜ* G) (hφ : ∀ g, φ g ∈ Λ ↔ g ∈ Λ) : mulEquivHaarChar φ = 1 := by
  have : Countable Λ := countable_of_isDiscrete Λ hΛ
  set E := fundamentalDomain Λ hΛ
  have hE : IsFundamentalDomain Λ E (Measure.haar : Measure G) := isFundamentalDomain Λ hΛ _
  have : ((Measure.haar : Measure G).map φ).IsHaarMeasure := φ.isHaarMeasure_map _
  have hqmp : Measure.QuasiMeasurePreserving φ (Measure.haar : Measure G) Measure.haar :=
    ⟨φ.continuous.measurable, Measure.absolutelyContinuous_isHaarMeasure _ _⟩
  let e : Λ → Λ := fun g => ⟨φ.symm g, (hφ _).mp (by simp)⟩
  have he : Function.Bijective e := by
    refine ⟨fun a b hab => ?_, fun b => ⟨⟨φ b, (hφ b).mpr b.2⟩, ?_⟩⟩
    · have h := congrArg (fun x : Λ => φ x) hab
      simpa [e] using h
    · ext; simp [e]
  have hef : ∀ g : Λ, Function.Semiconj φ (e g • ·) (g • ·) := by
    intro g x
    simp [e, Subgroup.smul_def]
  have hE' : IsFundamentalDomain Λ (φ ⁻¹' E) (Measure.haar : Measure G) :=
    hE.preimage_of_equiv hqmp he hef
  have h2 := mulEquivHaarChar_smul_preimage (Measure.haar : Measure G) (X := E) φ
  rw [hE'.measure_eq hE, ENNReal.smul_def, smul_eq_mul] at h2
  have h3 : (Measure.haar : Measure G) E * (mulEquivHaarChar φ : ℝ≥0∞) =
      (Measure.haar : Measure G) E * 1 := by
    rw [mul_one, mul_comm]; exact h2
  exact_mod_cast (ENNReal.mul_right_inj (haar_fundamentalDomain_ne_zero Λ hΛ)
    (haar_fundamentalDomain_ne_top Λ hΛ)).mp h3

/-- A measurable positive character trivial on a discrete subgroup of finite covolume is
trivial. -/
theorem eq_one_of_measurable_of_isFiniteMeasure (Λ : Subgroup G)
    (hΛ : IsDiscrete (Λ : Set G)) [IsFiniteMeasure (haarQuotientMeasure Λ hΛ)]
    (δ : G → ℝ≥0) (hδm : Measurable δ) (hδmul : ∀ g g', δ (g * g') = δ g * δ g')
    (hδpos : ∀ g, δ g ≠ 0) (hδΛ : ∀ γ ∈ Λ, δ γ = 1) (g0 : G) : δ g0 = 1 := by
  have : Countable Λ := countable_of_isDiscrete Λ hΛ
  have := isMulRightInvariant_haar_of_isFiniteMeasure Λ hΛ
  have hδ1 : δ 1 = 1 := hδΛ 1 Λ.one_mem
  have hinv : ∀ g, δ g⁻¹ = (δ g)⁻¹ := fun g =>
    eq_inv_of_mul_eq_one_left (by rw [← hδmul, inv_mul_cancel, hδ1])
  by_contra hne
  obtain ⟨g1, hg1⟩ : ∃ g1, 1 < δ g1 := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨g0⁻¹, by rw [hinv]; exact one_lt_inv₀ (pos_iff_ne_zero.mpr (hδpos g0)) |>.mpr h⟩
    · exact ⟨g0, h⟩
  set s := δ g1
  set E := fundamentalDomain Λ hΛ
  have hE : IsFundamentalDomain Λ E (Measure.haar : Measure G) := isFundamentalDomain Λ hΛ _
  have hE' : IsFundamentalDomain Λ ((· * g1⁻¹) ⁻¹' E) (Measure.haar : Measure G) :=
    hE.preimage_of_equiv (measurePreserving_mul_right _ g1⁻¹).quasiMeasurePreserving
      Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
  have hEtop := haar_fundamentalDomain_ne_top Λ hΛ
  have hnull : ∀ t : ℝ≥0, (Measure.haar : Measure G)
      (({g | δ g < t} \ {g | δ g * s < t}) ∩ E) = 0 := by
    intro t
    have hA : MeasurableSet {g | δ g < t} := hδm measurableSet_Iio
    have hB : MeasurableSet {g | δ g * s < t} := (hδm.mul_const s) measurableSet_Iio
    have hAinv : ∀ γ : Λ, (fun x => γ • x) ⁻¹' {g | δ g < t} = {g | δ g < t} := by
      intro γ
      ext x
      simp [Subgroup.smul_def, hδmul, hδΛ γ γ.2]
    have hBeq : {g | δ g * s < t} ∩ E =
        (· * g1) ⁻¹' ({g | δ g < t} ∩ (· * g1⁻¹) ⁻¹' E) := by
      ext x
      simp [hδmul, s]
    have hkey : (Measure.haar : Measure G) ({g | δ g * s < t} ∩ E) =
        (Measure.haar : Measure G) ({g | δ g < t} ∩ E) := by
      rw [hBeq, measure_preimage_mul_right, hE'.measure_set_eq hE hA hAinv]
    have hsub : {g | δ g * s < t} ∩ E ⊆ {g | δ g < t} ∩ E := by
      rintro x ⟨hx, hxE⟩
      exact ⟨lt_of_le_of_lt (le_mul_of_one_le_right (by positivity) hg1.le) hx, hxE⟩
    have hdiff : ({g | δ g < t} \ {g | δ g * s < t}) ∩ E =
        ({g | δ g < t} ∩ E) \ ({g | δ g * s < t} ∩ E) := by
      ext x; simp only [mem_inter_iff, mem_sdiff]; tauto
    rw [hdiff, measure_sdiff hsub (hB.inter
      (measurableSet_fundamentalDomain Λ hΛ)).nullMeasurableSet
      (ne_top_of_le_ne_top hEtop (measure_mono inter_subset_right)), hkey, tsub_self]
  apply haar_fundamentalDomain_ne_zero Λ hΛ
  refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null fun k : ℤ => hnull (s ^ (k + 1)))
  obtain ⟨k, hk1, hk2⟩ := NNReal.exists_mem_Ico_zpow (hδpos x) hg1
  refine mem_iUnion.mpr ⟨k, ⟨hk2, ?_⟩, hx⟩
  show ¬ (δ x * s < s ^ (k + 1))
  rw [not_lt, zpow_add_one₀ (pos_iff_ne_zero.mp (zero_lt_one.trans hg1))]
  gcongr

end Automorphism

section Semidirect

variable {N : Type u} {M : Type v} {H : Type w} [Group N] [Group M] [Group H]
  (i : N →* H) (j : M →* H) (p : H →* M)
  (hpj : ∀ m, p (j m) = m) (hker : ∀ h, p h = 1 → ∃ n, i n = h)

namespace Semidirect

include hpj in
theorem p_mul_inv_j_p (h : H) : p (h * (j (p h))⁻¹) = 1 := by
  simp [hpj]

/-- The `N`-component of an element of `H`. -/
def normalPart (h : H) : N :=
  (hker (h * (j (p h))⁻¹) (p_mul_inv_j_p j p hpj h)).choose

theorem i_normalPart (h : H) : i (normalPart i j p hpj hker h) = h * (j (p h))⁻¹ :=
  (hker (h * (j (p h))⁻¹) (p_mul_inv_j_p j p hpj h)).choose_spec

theorem i_normalPart_mul_j_p (h : H) : i (normalPart i j p hpj hker h) * j (p h) = h := by
  rw [i_normalPart]; group

variable (hpi : ∀ n, p (i n) = 1)

variable {i} in
include hpi in
theorem normalPart_mul (hi : Function.Injective i) (n : N) (m : M) :
    normalPart i j p hpj hker (i n * j m) = n := by
  apply hi
  rw [i_normalPart]
  simp [hpi, hpj]

include hpj hpi in
theorem p_i_mul_j (n : N) (m : M) : p (i n * j m) = m := by
  simp [hpi, hpj]

/-- Conjugation by `j m` on `N`, as a function. -/
def conjFun (m : M) (n : N) : N :=
  normalPart i j p hpj hker (j m * i n * (j m)⁻¹)

include hpi in
theorem i_conjFun (m : M) (n : N) : i (conjFun i j p hpj hker m n) = j m * i n * (j m)⁻¹ := by
  rw [conjFun, i_normalPart]
  simp [hpi, hpj]

variable [TopologicalSpace N] [TopologicalSpace M] [TopologicalSpace H] [IsTopologicalGroup H]

variable {i j p} in
theorem continuous_normalPart (hi : IsEmbedding i) (hj : Continuous j) (hp : Continuous p) :
    Continuous (normalPart i j p hpj hker) := by
  rw [hi.continuous_iff]
  have : (i ∘ normalPart i j p hpj hker) = fun h => h * (j (p h))⁻¹ :=
    funext (i_normalPart i j p hpj hker)
  rw [this]
  exact continuous_id.mul ((hj.comp hp).inv)

/-- The topological parametrization `(n, m) ↦ i n * j m` of `H`. -/
def prodHomeomorph (hi : IsEmbedding i) (hj : Continuous j) (hp : Continuous p) :
    N × M ≃ₜ H where
  toFun x := i x.1 * j x.2
  invFun h := (normalPart i j p hpj hker h, p h)
  left_inv x := by
    obtain ⟨n, m⟩ := x
    ext
    · exact normalPart_mul j p hpj hker hpi hi.injective n m
    · exact p_i_mul_j i j p hpj hpi n m
  right_inv h := i_normalPart_mul_j_p i j p hpj hker h
  continuous_toFun :=
    (hi.continuous.comp continuous_fst).mul (hj.comp continuous_snd)
  continuous_invFun := (continuous_normalPart hpj hker hi hj hp).prodMk hp

theorem prodHomeomorph_apply (hi : IsEmbedding i) (hj : Continuous j) (hp : Continuous p)
    (x : N × M) : prodHomeomorph i j p hpj hker hpi hi hj hp x = i x.1 * j x.2 := rfl

variable {i} in
include hpi in
theorem continuous_conjFun (hi : IsEmbedding i) (hj : Continuous j) :
    Continuous (fun x : M × N => conjFun i j p hpj hker x.1 x.2) := by
  rw [hi.continuous_iff]
  have : (i ∘ fun x : M × N => conjFun i j p hpj hker x.1 x.2) =
      fun x => j x.1 * i x.2 * (j x.1)⁻¹ :=
    funext fun x => i_conjFun i j p hpj hker hpi x.1 x.2
  rw [this]
  exact ((hj.comp continuous_fst).mul (hi.continuous.comp continuous_snd)).mul
    (hj.comp continuous_fst).inv

/-- Conjugation by `j m` on `N`, as a topological group automorphism. -/
def conj (hi : IsEmbedding i) (hj : Continuous j) (m : M) : N ≃ₜ* N where
  toFun := conjFun i j p hpj hker m
  invFun := conjFun i j p hpj hker m⁻¹
  left_inv n := hi.injective (by simp only [i_conjFun i j p hpj hker hpi, map_inv]; group)
  right_inv n := hi.injective (by simp only [i_conjFun i j p hpj hker hpi, map_inv]; group)
  map_mul' a b := hi.injective (by simp only [i_conjFun i j p hpj hker hpi, map_mul]; group)
  continuous_toFun :=
    (continuous_conjFun j p hpj hker hpi hi hj).comp (Continuous.prodMk_right m)
  continuous_invFun :=
    (continuous_conjFun j p hpj hker hpi hi hj).comp (Continuous.prodMk_right m⁻¹)

theorem conj_apply (hi : IsEmbedding i) (hj : Continuous j) (m : M) (n : N) :
    conj i j p hpj hker hpi hi hj m n = conjFun i j p hpj hker m n := rfl

theorem i_conj (hi : IsEmbedding i) (hj : Continuous j) (m : M) (n : N) :
    i (conj i j p hpj hker hpi hi hj m n) = j m * i n * (j m)⁻¹ :=
  i_conjFun i j p hpj hker hpi m n

theorem conj_mul (hi : IsEmbedding i) (hj : Continuous j) (m m' : M) :
    conj i j p hpj hker hpi hi hj (m * m') =
      (conj i j p hpj hker hpi hi hj m').trans (conj i j p hpj hker hpi hi hj m) := by
  ext n
  apply hi.injective
  simp only [ContinuousMulEquiv.coe_trans, Function.comp_apply, i_conj, map_mul]
  group

theorem i_mul_j_mul_i_mul_j (hi : IsEmbedding i) (hj : Continuous j) (n n' : N) (m m' : M) :
    i n' * j m' * (i n * j m) =
      i (n' * conj i j p hpj hker hpi hi hj m' n) * j (m' * m) := by
  simp only [map_mul, i_conj]
  group

variable [IsTopologicalGroup N] [IsTopologicalGroup M]
  [LocallyCompactSpace N] [LocallyCompactSpace M] [LocallyCompactSpace H]
  [SecondCountableTopology N] [SecondCountableTopology M] [SecondCountableTopology H]
  [MeasurableSpace N] [MeasurableSpace M] [MeasurableSpace H]
  [BorelSpace N] [BorelSpace M] [BorelSpace H]

variable {i j p}

omit [IsTopologicalGroup M] [LocallyCompactSpace M] [LocallyCompactSpace H]
  [SecondCountableTopology N] [SecondCountableTopology M] [SecondCountableTopology H]
  [MeasurableSpace M] [MeasurableSpace H] [BorelSpace M] [BorelSpace H] in
theorem mulEquivHaarChar_conj_mul (hi : IsEmbedding i) (hj : Continuous j) (m m' : M) :
    mulEquivHaarChar (conj i j p hpj hker hpi hi hj (m * m')) =
      mulEquivHaarChar (conj i j p hpj hker hpi hi hj m) *
        mulEquivHaarChar (conj i j p hpj hker hpi hi hj m') := by
  rw [conj_mul, mulEquivHaarChar_trans, mul_comm]

omit [IsTopologicalGroup M] [LocallyCompactSpace M] [LocallyCompactSpace H]
  [SecondCountableTopology M] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] in
/-- The conjugation modulus is measurable. -/
theorem measurable_mulEquivHaarChar_conj (hi : IsEmbedding i) (hj : Continuous j) :
    Measurable fun m => mulEquivHaarChar (conj i j p hpj hker hpi hi hj m) := by
  obtain ⟨K0, hK0, hK0mem⟩ := exists_compact_mem_nhds (1 : N)
  have hU : IsOpen (interior K0) := isOpen_interior
  have hU1 : (1 : N) ∈ interior K0 := mem_interior_iff_mem_nhds.mpr hK0mem
  set W : Set (M × N) := (fun x : M × N => conjFun i j p hpj hker x.1 x.2) ⁻¹' interior K0
  have hW : MeasurableSet W :=
    (hU.preimage (continuous_conjFun j p hpj hker hpi hi hj)).measurableSet
  have hmeas : Measurable fun m : M => (Measure.haar : Measure N) (Prod.mk m ⁻¹' W) :=
    measurable_measure_prodMk_left hW
  have heq : ∀ m, (mulEquivHaarChar (conj i j p hpj hker hpi hi hj m) : ℝ≥0∞) =
      (Measure.haar : Measure N) (interior K0) /
        (Measure.haar : Measure N) (Prod.mk m ⁻¹' W) := by
    intro m
    set φ := conj i j p hpj hker hpi hi hj m
    have hpre : Prod.mk m ⁻¹' W = φ ⁻¹' interior K0 := rfl
    have h0 : (Measure.haar : Measure N) (φ ⁻¹' interior K0) ≠ 0 :=
      (hU.preimage φ.continuous).measure_ne_zero _ ⟨1, by simpa using hU1⟩
    have htop : (Measure.haar : Measure N) (φ ⁻¹' interior K0) ≠ ∞ := by
      have hc : IsCompact (φ ⁻¹' K0) := φ.toHomeomorph.isCompact_preimage.mpr hK0
      exact ne_top_of_le_ne_top hc.measure_lt_top.ne
        (measure_mono (preimage_mono interior_subset))
    have h2 := mulEquivHaarChar_smul_preimage (Measure.haar : Measure N) (X := interior K0) φ
    rw [ENNReal.smul_def, smul_eq_mul] at h2
    rw [hpre, ENNReal.eq_div_iff h0 htop, mul_comm]
    exact h2
  have : Measurable fun m => (mulEquivHaarChar (conj i j p hpj hker hpi hi hj m) : ℝ≥0∞) := by
    simp_rw [heq]
    exact measurable_const.mul hmeas.inv
  exact measurable_coe_nnreal_ennreal_iff.mp this

omit [IsTopologicalGroup M] [LocallyCompactSpace M] [LocallyCompactSpace H]
  [SecondCountableTopology M] [SecondCountableTopology H] [MeasurableSpace M] [MeasurableSpace H]
  [BorelSpace M] [BorelSpace H] in
/-- Conjugation by an element whose image lies in `Γ` preserves Haar measure on `N`. -/
theorem mulEquivHaarChar_conj_eq_one_of_mem (hi : IsEmbedding i) (hj : Continuous j)
    (Γ : Subgroup H) (hΓ : IsDiscrete (Γ : Set H))
    {K : Set N} (hK : IsCompact K) (hKcover : ∀ n, ∃ γ, i γ ∈ Γ ∧ γ * n ∈ K)
    {m : M} (hm : j m ∈ Γ) : mulEquivHaarChar (conj i j p hpj hker hpi hi hj m) = 1 := by
  have hΓN : IsDiscrete ((Γ.comap i : Subgroup N) : Set N) :=
    IsDiscrete.preimage (f := ⇑i) hΓ hi.continuous.continuousOn hi.injective
  have := isFiniteMeasure_haarQuotientMeasure_of_isCompact (Γ.comap i) hΓN hK
    (fun n => (hKcover n).imp fun γ h => h)
  refine mulEquivHaarChar_eq_one_of_forall_mem_iff (Γ.comap i) hΓN _ fun n => ?_
  simp only [Subgroup.mem_comap, i_conj]
  constructor
  · intro h
    have h' := Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hm) h) hm
    have : (j m)⁻¹ * (j m * i n * (j m)⁻¹) * j m = i n := by group
    rwa [this] at h'
  · intro h
    exact Γ.mul_mem (Γ.mul_mem hm h) (Γ.inv_mem hm)

/-- Once conjugation preserves Haar measure on `N`, the Haar measure of `H` is a multiple of
the product measure transported along `(n, m) ↦ i n * j m`. -/
theorem exists_haar_eq_smul_map_prod (hi : IsEmbedding i) (hj : Continuous j)
    (hp : Continuous p) (hδ : ∀ m, mulEquivHaarChar (conj i j p hpj hker hpi hi hj m) = 1) :
    ∃ c : ℝ≥0, (Measure.haar : Measure H) = c • ((Measure.haar : Measure N).prod
      (Measure.haar : Measure M)).map (prodHomeomorph i j p hpj hker hpi hi hj hp) := by
  set Φ := prodHomeomorph i j p hpj hker hpi hi hj hp
  set ν := (Measure.haar : Measure N).prod (Measure.haar : Measure M)
  have hΦm : Measurable Φ := Φ.continuous.measurable
  have hconj : ∀ m, MeasurePreserving (conj i j p hpj hker hpi hi hj m)
      (Measure.haar : Measure N) Measure.haar := by
    intro m
    refine ⟨(conj i j p hpj hker hpi hi hj m).continuous.measurable, ?_⟩
    have h := mulEquivHaarChar_smul_map (Measure.haar : Measure N)
      (conj i j p hpj hker hpi hi hj m)
    rwa [hδ m, one_smul] at h
  have hinv : (ν.map Φ).IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    obtain ⟨⟨n', m'⟩, rfl⟩ := Φ.surjective g
    have hT : MeasurePreserving
        (Prod.map (fun n => n' * conj i j p hpj hker hpi hi hj m' n) (fun m => m' * m)) ν ν :=
      ((measurePreserving_mul_left _ n').comp (hconj m')).prod (measurePreserving_mul_left _ m')
    have hcomp : (fun x => Φ (n', m') * x) ∘ Φ =
        Φ ∘ Prod.map (fun n => n' * conj i j p hpj hker hpi hi hj m' n) (fun m => m' * m) := by
      funext x
      exact i_mul_j_mul_i_mul_j i j p hpj hker hpi hi hj x.1 n' x.2 m'
    rw [Measure.map_map (measurable_const_mul _) hΦm, hcomp,
      ← Measure.map_map hΦm hT.measurable, hT.map_eq]
  have hfin : IsFiniteMeasureOnCompacts (ν.map Φ) := ⟨fun C hC => by
    rw [show ν.map Φ = ν.map Φ.toMeasurableEquiv from rfl, MeasurableEquiv.map_apply]
    exact (Φ.isCompact_preimage.mpr hC).measure_lt_top⟩
  have hpos : (ν.map Φ).IsOpenPosMeasure := Φ.continuous.isOpenPosMeasure_map Φ.surjective
  have : (ν.map Φ).IsHaarMeasure := {}
  exact ⟨_, Measure.isMulLeftInvariant_eq_smul (Measure.haar : Measure H) (ν.map Φ)⟩

include hpj hker hpi in
/-- **Finite covolume for semidirect products.** -/
theorem isFiniteMeasure_haarQuotientMeasure (hi : IsEmbedding i) (hj : Continuous j)
    (hp : Continuous p) (Γ : Subgroup H) (hΓ : IsDiscrete (Γ : Set H))
    {K : Set N} (hK : IsCompact K) (hKcover : ∀ n, ∃ γ, i γ ∈ Γ ∧ γ * n ∈ K)
    (ΓM : Subgroup M) (hΓM : IsDiscrete (ΓM : Set M)) (hjΓM : ∀ γ ∈ ΓM, j γ ∈ Γ)
    [IsFiniteMeasure (haarQuotientMeasure ΓM hΓM)] :
    IsFiniteMeasure (haarQuotientMeasure Γ hΓ) := by
  have hδ : ∀ m, mulEquivHaarChar (conj i j p hpj hker hpi hi hj m) = 1 :=
    eq_one_of_measurable_of_isFiniteMeasure ΓM hΓM _
      (measurable_mulEquivHaarChar_conj hpj hker hpi hi hj)
      (mulEquivHaarChar_conj_mul hpj hker hpi hi hj)
      (fun m => (mulEquivHaarChar_pos _).ne')
      (fun γ hγ => mulEquivHaarChar_conj_eq_one_of_mem hpj hker hpi hi hj Γ hΓ hK hKcover
        (hjΓM γ hγ))
  obtain ⟨c, hc⟩ := exists_haar_eq_smul_map_prod hpj hker hpi hi hj hp hδ
  set Φ := prodHomeomorph i j p hpj hker hpi hi hj hp
  set E := fundamentalDomain ΓM hΓM
  set K' := toMeasurable (Measure.haar : Measure N) K
  have hKE : MeasurableSet (K' ×ˢ E) :=
    (measurableSet_toMeasurable _ _).prod (measurableSet_fundamentalDomain ΓM hΓM)
  have hS : MeasurableSet (Φ '' (K' ×ˢ E)) := by
    rw [Φ.image_eq_preimage_symm]
    exact Φ.symm.continuous.measurable hKE
  have hSfin : (Measure.haar : Measure H) (Φ '' (K' ×ˢ E)) < ∞ := by
    rw [hc, Measure.smul_apply, Measure.map_apply Φ.continuous.measurable hS,
      Φ.preimage_image, Measure.prod_prod, measure_toMeasurable, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top
      (ENNReal.mul_lt_top hK.measure_lt_top (haar_fundamentalDomain_ne_top ΓM hΓM).lt_top)
  have hcover : ∀ h : H, ∃ γ ∈ Γ, γ * h ∈ Φ '' (K' ×ˢ E) := by
    intro h
    obtain ⟨⟨n, m⟩, rfl⟩ := Φ.surjective h
    obtain ⟨γM, hγM, -⟩ := fundamentalDomain_unique ΓM hΓM m
    obtain ⟨γN, hγNΓ, hγNK⟩ := hKcover (conj i j p hpj hker hpi hi hj γM n)
    refine ⟨i γN * j γM, Γ.mul_mem hγNΓ (hjΓM _ γM.2), ?_⟩
    refine ⟨(γN * conj i j p hpj hker hpi hi hj γM n, γM * m),
      ⟨subset_toMeasurable _ _ hγNK, hγM⟩, ?_⟩
    exact (i_mul_j_mul_i_mul_j i j p hpj hker hpi hi hj n γN m γM).symm
  have : Countable Γ := countable_of_isDiscrete Γ hΓ
  have himage : mk Γ '' (Φ '' (K' ×ˢ E)) = univ := by
    refine eq_univ_of_forall fun q => ?_
    obtain ⟨h, rfl⟩ := mk_surjective Γ q
    obtain ⟨γ, hγ, hγS⟩ := hcover h
    exact ⟨γ * h, hγS, mk_subgroup_mul Γ ⟨γ, hγ⟩ h⟩
  have hle := quotientMeasure_image_le Γ (Measure.haar : Measure H)
    (isFundamentalDomain Γ hΓ Measure.haar) hS
  rw [himage] at hle
  exact ⟨lt_of_le_of_lt hle hSfin⟩

end Semidirect

end Semidirect

end Langlands.Global.LeftCosetSpace
