import Langlands.BaseChange.EllipticTorusWindowVolume
import Langlands.BaseChange.EllipticWeylIntegrationStatement
import Langlands.BaseChange.OrdinaryWeylHaarLocalPushforwards
import Langlands.BaseChange.OrdinaryWeylMeasureDecomposition
import Langlands.BaseChange.RegularSetOpenConull
import Langlands.BaseChange.OrdinaryWeylDifferential
import Langlands.BaseChange.GeneralLinearFiniteAlgebra
import Langlands.BaseChange.EllipticCharacterCentralProduct
import Langlands.BaseChange.RegularEllipticOpen
import Langlands.BaseChange.CentralQuotientFormalDegree
import Langlands.Analysis.Local.QuotientMeasureExistence
import Mathlib.MeasureTheory.Integral.Prod

/-! # Weyl integration on the regular elliptic set of `GL_n` modulo the center -/

noncomputable section

namespace Langlands.BaseChange

open JacquetLanglands MeasureTheory Set QuotientIntegration _root_.Topology
open scoped ENNReal NNReal

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u

section Fubini

variable {Q X V : Type*} [MeasurableSpace Q] [MeasurableSpace X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Fubini through a product parametrization.** If the restriction of `μ` to `E` is the image
of `μ × ν` under a measurable map `m`, then every function integrable on `E` composed with `m`
is integrable in the first variable for almost every second variable, its partial integrals
are `ν`-integrable, and they integrate to the integral over `E`. -/
theorem integral_fubini_of_restrict_eq_map {μ : Measure Q} {ν : Measure X} [SFinite μ]
    [SFinite ν] {E : Set Q} {m : Q × X → Q} (hm : Measurable m)
    (h : μ.restrict E = (μ.prod ν).map m) {Φ : Q → V} (hΦ : IntegrableOn Φ E μ) :
    (∀ᵐ x ∂ν, Integrable (fun g => Φ (m (g, x))) μ) ∧
      Integrable (fun x => ∫ g, Φ (m (g, x)) ∂μ) ν ∧
      ∫ q in E, Φ q ∂μ = ∫ x, ∫ g, Φ (m (g, x)) ∂μ ∂ν := by
  have hint : Integrable Φ ((μ.prod ν).map m) := by
    rw [← h]
    exact hΦ
  have hcomp : Integrable (Φ ∘ m) (μ.prod ν) := hint.comp_aemeasurable hm.aemeasurable
  refine ⟨hcomp.prod_left_ae, hcomp.integral_prod_right, ?_⟩
  rw [h, integral_map hm.aemeasurable hint.aestronglyMeasurable]
  exact integral_prod_symm _ hcomp

end Fubini

section Conjugation

variable {F : Type u} [Field F] {n : ℕ}

/-- Conjugate matrices have the same characteristic polynomial. -/
theorem charpoly_inv_mul_mul (x g : GeneralLinear n F) :
    ((x⁻¹ * g * x : GeneralLinear n F) : Matrix (Fin n) (Fin n) F).charpoly =
      (g : Matrix (Fin n) (Fin n) F).charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']

/-- Regular ellipticity is invariant under conjugation. -/
theorem isRegularElliptic_inv_mul_mul_iff (x g : GeneralLinear n F) :
    IsRegularElliptic (x⁻¹ * g * x) ↔ IsRegularElliptic g := by
  unfold IsRegularElliptic IsRegularSemisimple
  rw [charpoly_inv_mul_mul]

/-- Rational conjugacy of tori is an equivalence relation. -/
theorem WeylTorus.isConjugate_equivalence :
    Equivalence (WeylTorus.IsConjugate (F := F) (n := n)) := by
  refine ⟨fun T => ⟨1, ?_⟩, fun {T U} h => ?_, fun {T U V} h h' => ?_⟩
  · ext x
    simp [Subgroup.mem_map]
  · obtain ⟨g, hg⟩ := h
    refine ⟨g⁻¹, ?_⟩
    rw [← hg, Subgroup.map_map]
    ext x
    simp only [Subgroup.mem_map, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨x, hx, by group⟩
  · obtain ⟨g, hg⟩ := h
    obtain ⟨g', hg'⟩ := h'
    refine ⟨g' * g, ?_⟩
    rw [← hg', ← hg, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]

/-- Every rank has a set of representatives of the rational conjugacy classes of tori. -/
theorem WeylTorus.exists_representativeSet (F : Type u) [Field F] (n : ℕ) :
    ∃ S : Set (WeylTorus F n), WeylTorus.IsRepresentativeSet S := by
  let s : Setoid (WeylTorus F n) := ⟨_, WeylTorus.isConjugate_equivalence⟩
  refine ⟨range (fun c : Quotient s => c.out), fun T => ?_⟩
  refine ⟨(Quotient.mk s T).out, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
  · exact Setoid.symm (Quotient.mk_out (s := s) T)
  · rintro U ⟨⟨c, rfl⟩, hU⟩
    have hc : c = Quotient.mk s T := by
      rw [← Quotient.out_eq c]
      exact Quotient.sound (Setoid.symm hU)
    rw [hc]

/-- The center of `GL_n(F)` lies in the rational points of every torus. -/
theorem WeylTorus.center_le (T : WeylTorus F n) : Subgroup.center (GeneralLinear n F) ≤ T.val := by
  obtain ⟨γ, -, hT⟩ := T.property
  rw [← hT, glCentralizer_eq_centralizer]
  exact Subgroup.center_le_centralizer _

/-- The rational points of a torus form a closed subgroup. -/
theorem WeylTorus.isClosed_subgroup [TopologicalSpace F] [IsTopologicalRing F]
    [T2Space (GeneralLinear n F)] (T : WeylTorus F n) :
    IsClosed (T.val : Set (GeneralLinear n F)) := by
  obtain ⟨γ, -, hT⟩ := T.property
  rw [← hT, glCentralizer_eq_centralizer]
  exact Set.isClosed_centralizer _

end Conjugation

section Torus

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

/-- The determinant order is invariant under conjugation. -/
theorem determinantOrder_inv_mul_mul (x g : GeneralLinear n F) :
    determinantOrder F n (x⁻¹ * g * x) = determinantOrder F n g := by
  rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]

/-- The determinant windows are invariant under conjugation. -/
theorem inv_mul_mul_mem_degreeWindow_iff (x g : GeneralLinear n F) (c : ℤ) :
    x⁻¹ * g * x ∈ degreeWindow (determinantOrder F n) n c ↔
      g ∈ degreeWindow (determinantOrder F n) n c := by
  simp only [degreeWindow, mem_ofPred_eq, determinantOrder_inv_mul_mul]

namespace WeylTorus

/-- The regular points of a torus that are regular elliptic and lie in the determinant window
`0 ≤ ord(det t) < n`. -/
def ellipticWindowPoints (T : WeylTorus F n) : Set T.regularPoints :=
  {t | IsRegularElliptic t.val.val ∧ t.val.val ∈ degreeWindow (determinantOrder F n) n 0}

variable [MeasurableSpace (GeneralLinear n F)]

/-- The contribution of one torus to the elliptic Weyl measure on `G / Z`: the image of the
restriction of `μT` to the regular elliptic window points, with density the absolute Weyl
discriminant, multiplied by the inverses in `ℝ≥0∞` of the order of the rational Weyl group and
of the window volume `κ_T` of the torus (so the term is zero if `κ_T = ∞`). -/
def ellipticOrbitMeasure [MeasurableSpace (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F))]
    (T : WeylTorus F n) (μT : Measure T.val) :
    Measure (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F)) :=
  ((Nat.card T.RationalWeylGroup : ℝ≥0∞)⁻¹ * (subgroupWindowVolume T.val μT)⁻¹) •
    ((((μT.comap Subtype.val).restrict T.ellipticWindowPoints).withDensity
      fun t => (T.discriminantWeight t : ℝ≥0∞)).map
        fun t => (QuotientGroup.mk t.val.val : GeneralLinear n F ⧸ Subgroup.center _))

variable [BorelSpace (GeneralLinear n F)]

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [BorelSpace (GeneralLinear n F)] in
/-- A left Haar measure on the commutative group of rational torus points is right
invariant. -/
theorem haar_isMulRightInvariant (T : WeylTorus F n) (μT : Measure T.val)
    [μT.IsHaarMeasure] : μT.IsMulRightInvariant := by
  obtain ⟨_, γ, hγ, rfl⟩ := T
  exact ⟨fun t => by
    have heq : (· * t) = (t * ·) := funext fun s => glCentralizer_mul_comm hγ s t
    rw [heq, map_mul_left_eq_self]⟩

/-- Weil's theorem for a closed subgroup of a second countable group, with right Haar
measures. -/
private theorem compatibleMeasureExists_of_isClosed {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μG : Measure G) (μH : Measure H)
    [μG.IsHaarMeasure] [μG.IsMulRightInvariant]
    [μH.IsHaarMeasure] [μH.IsMulRightInvariant] : CompatibleMeasureExists H μG μH := by
  let _ : LocallyCompactSpace H := hH.locallyCompactSpace
  let _ : SecondCountableTopology H := inferInstanceAs (SecondCountableTopology ↥(H : Set G))
  have : μG.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μG
  have : μH.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μH
  exact compatibleMeasureExists H hH μG μH

/-- Every torus carries a Haar measure with a quotient measure compatible with a given Haar
measure on `GL_n(F)`. -/
theorem exists_haar_compatible (T : WeylTorus F n)
    (μG : Measure (GeneralLinear n F)) [μG.IsHaarMeasure] :
    ∃ (μT : Measure T.val) (_ : μT.IsHaarMeasure) (_ : μT.IsMulRightInvariant)
      (ν : Measure (LeftQuotient T.val)), IsCompatible T.val μG μT ν := by
  let _ := LocalFieldTopology.generalLinear_t2Space F n
  let _ := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let _ := LocalFieldTopology.generalLinear_secondCountableTopology F n
  have hclosed := T.isClosed_subgroup
  let _ : LocallyCompactSpace T.val := hclosed.locallyCompactSpace
  have : μG.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μG
  have : μG.IsMulRightInvariant := generalLinear_haar_rightInvariant F n μG
  let μT : Measure T.val := Measure.haar
  have hright : μT.IsMulRightInvariant := T.haar_isMulRightInvariant μT
  obtain ⟨ν, hν⟩ := compatibleMeasureExists_of_isClosed T.val hclosed μG μT
  exact ⟨μT, inferInstance, hright, ν, hν⟩

/-- The restriction of a torus Haar measure to the regular points is s-finite. -/
theorem sFinite_comap_regularPoints (T : WeylTorus F n) (μT : Measure T.val)
    [μT.IsHaarMeasure] : SFinite (μT.comap (Subtype.val : T.regularPoints → T.val)) := by
  let _ := LocalFieldTopology.generalLinear_t2Space F n
  let _ := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let _ := LocalFieldTopology.generalLinear_secondCountableTopology F n
  let _ : LocallyCompactSpace T.val := T.isClosed_subgroup.locallyCompactSpace
  let _ : SecondCountableTopology T.val :=
    inferInstanceAs (SecondCountableTopology ↥(T.val : Set (GeneralLinear n F)))
  have hreg : MeasurableSet T.regularPoints :=
    (((regularSemisimpleOpenConull F n).1).preimage continuous_subtype_val).measurableSet
  have : SigmaFinite (μT.comap (Subtype.val : T.regularPoints → T.val)) :=
    SigmaFinite.of_map _ measurable_subtype_coe.aemeasurable
      (by rw [map_comap_subtype_coe hreg]; infer_instance)
  infer_instance

/-- The absolute Weyl discriminant is measurable on the regular points of a torus. -/
theorem measurable_discriminantWeight (T : WeylTorus F n) :
    Measurable fun t : T.regularPoints => (T.discriminantWeight t : ℝ≥0∞) := by
  have hne (t : T.regularPoints) : weylDiscriminant t.val.val ≠ 0 := by
    obtain ⟨hunit, hdet⟩ := det_ordinaryWeylDifferential t.val.val t.property
    exact hdet ▸ hunit.ne_zero
  exact (T.isLocallyConstant_discriminantWeight hne).continuous.measurable.coe_nnreal_ennreal

variable [CharZero F]

/-- The regular elliptic window points form a measurable set. -/
theorem measurableSet_ellipticWindowPoints (T : WeylTorus F n) :
    MeasurableSet T.ellipticWindowPoints := by
  have hopen : IsOpen {g : GeneralLinear n F |
      IsRegularElliptic g ∧ g ∈ degreeWindow (determinantOrder F n) n 0} :=
    (regularEllipticOpen F n).inter (isOpen_degreeWindow_determinantOrder F n 0)
  exact (hopen.preimage (continuous_subtype_val.comp continuous_subtype_val)).measurableSet

variable [MeasurableSpace (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F))]
  [BorelSpace (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F))]

omit [CharZero F] [BorelSpace (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F))] in
/-- Each torus contribution is s-finite. -/
theorem sFinite_ellipticOrbitMeasure (T : WeylTorus F n) (μT : Measure T.val)
    [μT.IsHaarMeasure] : SFinite (T.ellipticOrbitMeasure μT) := by
  have := T.sFinite_comap_regularPoints μT
  unfold ellipticOrbitMeasure
  infer_instance

/-- Each torus contribution is carried by the image of the regular elliptic set. -/
theorem ellipticOrbitMeasure_compl (T : WeylTorus F n) (μT : Measure T.val) :
    T.ellipticOrbitMeasure μT
      (QuotientGroup.mk '' {g : GeneralLinear n F | IsRegularElliptic g})ᶜ = 0 := by
  have hE : IsOpen (QuotientGroup.mk '' {g : GeneralLinear n F | IsRegularElliptic g} :
      Set (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F))) :=
    QuotientGroup.isOpenMap_coe _ (regularEllipticOpen F n)
  have hmk : Measurable fun t : T.regularPoints =>
      (QuotientGroup.mk t.val.val : GeneralLinear n F ⧸ Subgroup.center _) :=
    (QuotientGroup.continuous_mk.comp
      (continuous_subtype_val.comp continuous_subtype_val)).measurable
  have hEc := hE.isClosed_compl.measurableSet
  rw [ellipticOrbitMeasure, Measure.smul_apply, Measure.map_apply hmk hEc, smul_eq_mul]
  refine mul_eq_zero_of_right _ (withDensity_absolutelyContinuous _ _ ?_)
  rw [Measure.restrict_apply (hmk hEc)]
  convert measure_empty (μ := μT.comap (Subtype.val : T.regularPoints → T.val))
  refine eq_empty_of_forall_notMem fun t ht => ht.1 ?_
  exact ⟨t.val.val, ht.2.1, rfl⟩

end WeylTorus

end Torus

section Lintegral

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Integration against the image of a restricted measure with a density. -/
theorem lintegral_smul_map_withDensity_restrict (c : ℝ≥0∞) (τ : Measure α) {s : Set α}
    (hs : MeasurableSet s) {w : α → ℝ≥0∞} (hw : Measurable w) {π : α → β}
    (hπ : Measurable π) {f : β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(c • ((τ.restrict s).withDensity w).map π) =
      c * ∫⁻ t, s.indicator (fun t => w t * f (π t)) t ∂τ := by
  have h := lintegral_withDensity_eq_lintegral_mul (τ.restrict s) hw (hf.comp hπ)
  simp only [Function.comp_apply, Pi.mul_apply] at h
  rw [lintegral_smul_measure, lintegral_map hf hπ, smul_eq_mul, h, lintegral_indicator hs]

/-- A product measure with a density in the second variable, evaluated on a measurable set
as an iterated integral, the inner integral over the first factor. -/
theorem prod_withDensity_snd_apply (ν : Measure α) (τ : Measure β) [SFinite ν] [SFinite τ]
    {w : β → ℝ≥0∞} (hw : Measurable w) {s : Set (α × β)} (hs : MeasurableSet s) :
    (ν.prod τ).withDensity (fun z => w z.2) s =
      ∫⁻ t, ∫⁻ q, s.indicator (fun z => w z.2) (q, t) ∂ν ∂τ := by
  rw [withDensity_apply _ hs, ← lintegral_indicator hs,
    lintegral_prod_symm (s.indicator fun a => w a.2)
      ((hw.comp measurable_snd).indicator hs).aemeasurable]

end Lintegral

section Slice

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}
  [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
  [MeasurableSpace (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F))]
  [BorelSpace (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F))]

local notation "Q" => GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F)

omit [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)] in
/-- Conjugation `(g, x) ↦ g x g⁻¹` on `G / Z` is measurable. -/
theorem measurable_centralQuotientConj :
    Measurable fun p : Q × Q => p.1 * p.2 * p.1⁻¹ := by
  have := LocalFieldTopology.generalLinear_secondCountableTopology F n
  exact ((continuous_fst.mul continuous_snd).mul continuous_fst.inv).measurable

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
  [MeasurableSpace (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F))]
  [BorelSpace (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F))] in
/-- The regular elliptic set is a union of cosets of the center. -/
theorem mk_preimage_image_regularElliptic [CharZero F] :
    (QuotientGroup.mk : GeneralLinear n F → Q) ⁻¹'
        (QuotientGroup.mk '' {g : GeneralLinear n F | IsRegularElliptic g}) =
      {g | IsRegularElliptic g} := by
  ext g
  constructor
  · rintro ⟨h, hh, hhg⟩
    have hz : h⁻¹ * g ∈ Subgroup.center (GeneralLinear n F) := QuotientGroup.eq.mp hhg
    have hg : g = (⟨h⁻¹ * g, hz⟩ : Subgroup.center (GeneralLinear n F)).val * h := by
      change g = h⁻¹ * g * h
      rw [← Subgroup.mem_center_iff.mp hz h, mul_inv_cancel_left]
    rw [mem_ofPred_eq, hg]
    exact isRegularElliptic_center_mul hh _
  · intro hg
    exact ⟨g, hg, rfl⟩

namespace WeylTorus

/-- **The window slice.** For a regular point `t` of a torus `T`, let `C_t` be the set of cosets
`T x` in `T \ G` with `x⁻¹ t x ∈ A` modulo the center. Then the window volume `κ_T` of `T` times
the compatible quotient measure of `C_t` is the window measure of `{g | g t g⁻¹ ∈ A}` on `G / Z`.
One may divide by `κ_T` when it is positive and finite, as when `t` is regular elliptic; in
general `κ_T` can be infinite (for instance for the diagonal torus of `GL_2`). -/
theorem windowVolume_mul_measure_slice (hn : 0 < n) (T : WeylTorus F n)
    (μG : Measure (GeneralLinear n F)) [IsFiniteMeasureOnCompacts μG]
    [(windowMeasure F n μG).IsInvInvariant]
    (μT : Measure T.val) [μT.IsMulLeftInvariant] [μT.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μT] (νT : Measure (LeftQuotient T.val))
    (hνT : IsCompatible T.val μG μT νT) {A : Set Q} (hA : MeasurableSet A)
    (t : T.regularPoints) :
    subgroupWindowVolume T.val μT *
        νT {q | (QuotientGroup.mk (T.ordinaryOrbitMap (q, t)) : Q) ∈ A} =
      windowMeasure F n μG ((fun g : Q => (g, (QuotientGroup.mk t.val.val : Q))) ⁻¹'
        ((fun p : Q × Q => p.1 * p.2 * p.1⁻¹) ⁻¹' A)) := by
  have := LocalFieldTopology.generalLinear_t2Space F n
  have hC : MeasurableSet {q | (QuotientGroup.mk (T.ordinaryOrbitMap (q, t)) : Q) ∈ A} :=
    (QuotientGroup.continuous_mk.comp (T.continuous_ordinaryOrbitMap.comp
      (continuous_id.prodMk continuous_const))).measurable hA
  have hB : MeasurableSet {y : Q | y⁻¹ * (QuotientGroup.mk t.val.val : Q) * y ∈ A} :=
    ((continuous_inv.mul continuous_const).mul continuous_id).measurable hA
  have hslice : (fun g : Q => (g, (QuotientGroup.mk t.val.val : Q))) ⁻¹'
      ((fun p : Q × Q => p.1 * p.2 * p.1⁻¹) ⁻¹' A) =
        Inv.inv ⁻¹' {y : Q | y⁻¹ * (QuotientGroup.mk t.val.val : Q) * y ∈ A} := by
    ext y
    simp only [mem_preimage, mem_ofPred_eq, inv_inv]
  rw [← measure_preimage_inter_window_eq hn T.val T.isClosed_subgroup T.center_le μG μT νT hνT hC,
    hslice, Measure.measure_preimage_inv, windowMeasure_apply F n μG hB]
  rfl

variable [CharZero F]

/-- **One torus.** The part of the ordinary Weyl measure of `T` lying over the regular elliptic
window points that conjugate into `A` modulo the center, divided by the order of the rational
Weyl group, is the integral of the window measure of the conjugation slices
`{g | g x g⁻¹ ∈ A}` against the elliptic orbit measure of `T`. -/
theorem lintegral_ellipticOrbitMeasure (hn : 0 < n) (T : WeylTorus F n)
    (μG : Measure (GeneralLinear n F)) [μG.IsHaarMeasure]
    [(windowMeasure F n μG).IsInvInvariant]
    (μT : Measure T.val) [μT.IsHaarMeasure] [μT.IsMulRightInvariant]
    (νT : Measure (LeftQuotient T.val)) (hνT : IsCompatible T.val μG μT νT)
    {A : Set Q} (hA : MeasurableSet A) :
    (Nat.card T.RationalWeylGroup : ℝ≥0∞)⁻¹ *
        T.weightedOrdinaryOrbitMeasure νT (μT.comap Subtype.val) T.discriminantWeight
          (T.ordinaryOrbitMap ⁻¹' (QuotientGroup.mk ⁻¹' A ∩
            {g : GeneralLinear n F | IsRegularElliptic g} ∩
              degreeWindow (determinantOrder F n) n 0)) =
      ∫⁻ x, windowMeasure F n μG ((fun g : Q => (g, x)) ⁻¹'
        ((fun p : Q × Q => p.1 * p.2 * p.1⁻¹) ⁻¹' A)) ∂(T.ellipticOrbitMeasure μT) := by
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_secondCountableTopology F n
  let _ : SecondCountableTopology (LeftQuotient T.val) :=
    (leftQuotient_isOpenQuotientMap T.val).secondCountableTopology
  let _ : SecondCountableTopology T.val := IsInducing.subtypeVal.secondCountableTopology
  let _ : SecondCountableTopology T.regularPoints :=
    IsInducing.subtypeVal.secondCountableTopology
  let _ := leftQuotient_locallyCompactSpace T.val
  have : SFinite νT := by
    have := hνT.regular
    infer_instance
  have := T.sFinite_comap_regularPoints μT
  have : SFinite (windowMeasure F n μG) := by
    unfold windowMeasure
    infer_instance
  let _ : LocallyCompactSpace T.val := T.isClosed_subgroup.locallyCompactSpace
  have hW : (Nat.card T.RationalWeylGroup : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast T.natCard_rationalWeylGroup_pos.ne'
  have hW' : (Nat.card T.RationalWeylGroup : ℝ≥0∞)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hW
  have hκ0 : subgroupWindowVolume T.val μT ≠ 0 := (subgroupWindowVolume_pos hn T.val μT).ne'
  have hc : (Nat.card T.RationalWeylGroup : ℝ≥0∞)⁻¹ * (subgroupWindowVolume T.val μT)⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top hW' (ENNReal.inv_ne_top.mpr hκ0)
  have hw := T.measurable_discriminantWeight
  have hπ : Measurable fun t : T.regularPoints => (QuotientGroup.mk t.val.val : Q) :=
    (QuotientGroup.continuous_mk.comp
      (continuous_subtype_val.comp continuous_subtype_val)).measurable
  have hf : Measurable fun x : Q => windowMeasure F n μG ((fun g : Q => (g, x)) ⁻¹'
      ((fun p : Q × Q => p.1 * p.2 * p.1⁻¹) ⁻¹' A)) :=
    measurable_measure_prodMk_right (measurable_centralQuotientConj hA)
  have hY : MeasurableSet (QuotientGroup.mk ⁻¹' A ∩
      {g : GeneralLinear n F | IsRegularElliptic g} ∩ degreeWindow (determinantOrder F n) n 0) :=
    ((QuotientGroup.continuous_mk.measurable hA).inter
      (regularEllipticOpen F n).measurableSet).inter
        (isOpen_degreeWindow_determinantOrder F n 0).measurableSet
  have horb : Measurable T.ordinaryOrbitMap := T.continuous_ordinaryOrbitMap.measurable
  have hC (t : T.regularPoints) :
      MeasurableSet {q | (QuotientGroup.mk (T.ordinaryOrbitMap (q, t)) : Q) ∈ A} :=
    (QuotientGroup.continuous_mk.comp (T.continuous_ordinaryOrbitMap.comp
      (continuous_id.prodMk continuous_const))).measurable hA
  have hmem (q : LeftQuotient T.val) (t : T.regularPoints) :
      (q, t) ∈ T.ordinaryOrbitMap ⁻¹' (QuotientGroup.mk ⁻¹' A ∩
        {g : GeneralLinear n F | IsRegularElliptic g} ∩
          degreeWindow (determinantOrder F n) n 0) ↔
        t ∈ T.ellipticWindowPoints ∧
          q ∈ {q | (QuotientGroup.mk (T.ordinaryOrbitMap (q, t)) : Q) ∈ A} := by
    induction q using Quotient.inductionOn with
    | h x =>
    show ((QuotientGroup.mk (x⁻¹ * t.val.val * x) : Q) ∈ A ∧
        IsRegularElliptic (x⁻¹ * t.val.val * x)) ∧
          x⁻¹ * t.val.val * x ∈ degreeWindow (determinantOrder F n) n 0 ↔
      (IsRegularElliptic t.val.val ∧ t.val.val ∈ degreeWindow (determinantOrder F n) n 0) ∧
        (QuotientGroup.mk (x⁻¹ * t.val.val * x) : Q) ∈ A
    rw [isRegularElliptic_inv_mul_mul_iff, inv_mul_mul_mem_degreeWindow_iff]
    tauto
  rw [weightedOrdinaryOrbitMeasure, prod_withDensity_snd_apply _ _ hw (horb hY),
    ellipticOrbitMeasure, lintegral_smul_map_withDensity_restrict _ _
      T.measurableSet_ellipticWindowPoints hw hπ hf,
    ← lintegral_const_mul' _ _ hc, ← lintegral_const_mul' _ _ hW']
  refine lintegral_congr fun t => ?_
  rw [mul_assoc]
  congr 1
  by_cases ht : t ∈ T.ellipticWindowPoints
  · have hκ : subgroupWindowVolume T.val μT ≠ ∞ :=
      (subgroupWindowVolume_lt_top hn t.val.val ht.1 T.val
        (T.glCentralizer_eq_of_regularPoint t) μT).ne
    have hfun : (fun q => (T.ordinaryOrbitMap ⁻¹' (QuotientGroup.mk ⁻¹' A ∩
        {g : GeneralLinear n F | IsRegularElliptic g} ∩
          degreeWindow (determinantOrder F n) n 0)).indicator
            (fun z => (T.discriminantWeight z.2 : ℝ≥0∞)) (q, t)) =
        {q | (QuotientGroup.mk (T.ordinaryOrbitMap (q, t)) : Q) ∈ A}.indicator
          fun _ => (T.discriminantWeight t : ℝ≥0∞) := by
      funext q
      by_cases hq : q ∈ {q | (QuotientGroup.mk (T.ordinaryOrbitMap (q, t)) : Q) ∈ A}
      · rw [indicator_of_mem ((hmem q t).mpr ⟨ht, hq⟩), indicator_of_mem hq]
      · rw [indicator_of_notMem (fun h => hq ((hmem q t).mp h).2), indicator_of_notMem hq]
    rw [hfun, lintegral_indicator_const (hC t), indicator_of_mem ht,
      ← windowVolume_mul_measure_slice hn T μG μT νT hνT hA t, mul_left_comm]
    congr 1
    rw [← mul_assoc, ENNReal.inv_mul_cancel hκ0 hκ, one_mul]
  · rw [indicator_of_notMem ht, mul_zero]
    exact (lintegral_congr fun q =>
      indicator_of_notMem (fun h => ht ((hmem q t).mp h).1) _).trans lintegral_zero

end WeylTorus

end Slice

section Main

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}
  [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]

/-- The ordinary Weyl map of a torus is measurable. -/
theorem WeylTorus.measurable_ordinaryOrbitMap (T : WeylTorus F n) :
    Measurable T.ordinaryOrbitMap := by
  have := LocalFieldTopology.generalLinear_secondCountableTopology F n
  let _ : SecondCountableTopology (LeftQuotient T.val) :=
    (leftQuotient_isOpenQuotientMap T.val).secondCountableTopology
  let _ : SecondCountableTopology T.val := IsInducing.subtypeVal.secondCountableTopology
  let _ : SecondCountableTopology T.regularPoints :=
    IsInducing.subtypeVal.secondCountableTopology
  exact T.continuous_ordinaryOrbitMap.measurable

variable [CharZero F]
  [MeasurableSpace (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F))]
  [BorelSpace (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F))]

local notation "Q" => GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F)

/-- **Weyl integration on the regular elliptic set, measure form.** Let `μG` be a Haar measure
on `G = GL_n(F)`, `S` a set of representatives of the conjugacy classes of tori, and for each
torus `T` let `μT` be a Haar measure on `T` with a compatible quotient measure on `T \ G`. Then
`S` is countable, and the restriction of the window measure of `μG` to the image `E` of the
regular elliptic set in `G / Z` is the image of the product of the window measure with
`∑_{T ∈ S} ellipticOrbitMeasure T` under conjugation `(g, x) ↦ g x g⁻¹`. -/
theorem windowMeasure_restrict_regularElliptic_eq_map (hn : 0 < n)
    (μG : Measure (GeneralLinear n F)) [μG.IsHaarMeasure]
    [(windowMeasure F n μG).IsInvInvariant]
    {S : Set (WeylTorus F n)} (hS : WeylTorus.IsRepresentativeSet S)
    (μT : ∀ T : WeylTorus F n, Measure T.val) (hμT : ∀ T, (μT T).IsHaarMeasure)
    (hμTR : ∀ T, (μT T).IsMulRightInvariant)
    (νT : ∀ T : WeylTorus F n, Measure (LeftQuotient T.val))
    (hνT : ∀ T, IsCompatible T.val μG (μT T) (νT T)) :
    Countable S ∧
      (windowMeasure F n μG).restrict
          (QuotientGroup.mk '' {g : GeneralLinear n F | IsRegularElliptic g}) =
        ((windowMeasure F n μG).prod
          (Measure.sum fun T : S => T.val.ellipticOrbitMeasure (μT T.val))).map
            fun p : Q × Q => p.1 * p.2 * p.1⁻¹ := by
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_secondCountableTopology F n
  have hloc (T : S) : T.val.HasOrdinaryLocalPushforwards μG
      (T.val.weightedOrdinaryOrbitMeasure (νT T.val) ((μT T.val).comap Subtype.val)
        T.val.discriminantWeight) := by
    have := hμT T.val
    have := hμTR T.val
    exact ordinaryWeylHaarLocalPushforwards F n μG T.val (μT T.val) (νT T.val) (hνT T.val)
  obtain ⟨hcount, hdecomp⟩ := ordinaryWeylMeasureDecomposition F n μG S hS _ hloc
  refine ⟨hcount, ?_⟩
  have : SFinite (windowMeasure F n μG) := by
    unfold windowMeasure
    infer_instance
  have (T : S) : SFinite (T.val.ellipticOrbitMeasure (μT T.val)) := by
    have := hμT T.val
    exact T.val.sFinite_ellipticOrbitMeasure _
  have hE : IsOpen (QuotientGroup.mk '' {g : GeneralLinear n F | IsRegularElliptic g} : Set Q) :=
    QuotientGroup.isOpenMap_coe _ (regularEllipticOpen F n)
  ext A hA
  have hY : MeasurableSet (QuotientGroup.mk ⁻¹' A ∩
      {g : GeneralLinear n F | IsRegularElliptic g} ∩ degreeWindow (determinantOrder F n) n 0) :=
    ((QuotientGroup.continuous_mk.measurable hA).inter
      (regularEllipticOpen F n).measurableSet).inter
        (isOpen_degreeWindow_determinantOrder F n 0).measurableSet
  have hYsub : QuotientGroup.mk ⁻¹' A ∩ {g : GeneralLinear n F | IsRegularElliptic g} ∩
      degreeWindow (determinantOrder F n) n 0 ⊆ {g | IsRegularSemisimple g} :=
    fun g hg => hg.1.2.isRegularSemisimple
  rw [Measure.restrict_apply hA, windowMeasure_apply F n μG (hA.inter hE.measurableSet),
    preimage_inter, mk_preimage_image_regularElliptic, ← Measure.restrict_eq_self μG hYsub,
    hdecomp, Measure.sum_apply _ hY, Measure.map_apply measurable_centralQuotientConj hA,
    Measure.prod_apply_symm (measurable_centralQuotientConj hA), lintegral_sum_measure]
  refine tsum_congr fun T => ?_
  have := hμT T.val
  have := hμTR T.val
  rw [Measure.smul_apply, Measure.map_apply T.val.measurable_ordinaryOrbitMap hY, smul_eq_mul]
  exact T.val.lintegral_ellipticOrbitMeasure hn μG (μT T.val) (νT T.val) (hνT T.val) hA

end Main

/-- **Weyl integration on the regular elliptic set of `GL_n` modulo the center.** For a
characteristic-zero nonarchimedean local field `F` and `n > 0`, the measure
`ν = ∑_{T} ellipticOrbitMeasure T` on `G / Z`, summed over representatives of the conjugacy
classes of tori, is carried by the image `E` of the regular elliptic set, and for every Haar
measure `μ` on `G / Z` and every `Φ` integrable on `E` the orbital integrals of `Φ` are defined
`ν`-almost everywhere, are `ν`-integrable, and integrate to `∫_E Φ dμ`. -/
theorem ellipticWeylIntegration : EllipticWeylIntegrationStatement.{u} := by
  intro F _ _ _ _ _ n hn
  dsimp only
  let _ := centralQuotientMeasurableSpace F n
  have := centralQuotientBorelSpace F n
  let _ : MeasurableSpace (GeneralLinear n F) := borel _
  have : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_secondCountableTopology F n
  let μG : Measure (GeneralLinear n F) := Measure.haar
  have := windowMeasure_isHaarMeasure F n hn μG
  have := centralQuotient_isInvInvariant F n (windowMeasure F n μG)
  obtain ⟨S, hS⟩ := WeylTorus.exists_representativeSet F n
  choose μT hμT hμTR νT hνT using fun T : WeylTorus F n => T.exists_haar_compatible μG
  obtain ⟨hcount, hmain⟩ :=
    windowMeasure_restrict_regularElliptic_eq_map hn μG hS μT hμT hμTR νT hνT
  have hE : IsOpen (QuotientGroup.mk '' {g : GeneralLinear n F | IsRegularElliptic g} :
      Set (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F))) :=
    QuotientGroup.isOpenMap_coe _ (regularEllipticOpen F n)
  refine ⟨Measure.sum fun T : S => T.val.ellipticOrbitMeasure (μT T.val), ?_, ?_⟩
  · rw [Measure.sum_apply _ hE.isClosed_compl.measurableSet]
    exact ENNReal.tsum_eq_zero.mpr fun T => T.val.ellipticOrbitMeasure_compl _
  · intro μ _ Φ hΦ
    have : IsClosed (Subgroup.center (GeneralLinear n F) : Set (GeneralLinear n F)) := by
      rw [Subgroup.coe_center, ← Set.centralizer_univ]
      exact Set.isClosed_centralizer _
    have (T : S) : SFinite (T.val.ellipticOrbitMeasure (μT T.val)) := by
      have := hμT T.val
      exact T.val.sFinite_ellipticOrbitMeasure _
    have hμ : μ = μ.haarScalarFactor (windowMeasure F n μG) • windowMeasure F n μG :=
      Measure.isMulLeftInvariant_eq_smul μ _
    have h : μ.restrict (QuotientGroup.mk '' {g : GeneralLinear n F | IsRegularElliptic g}) =
        (μ.prod (Measure.sum fun T : S => T.val.ellipticOrbitMeasure (μT T.val))).map
          fun p : (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F)) ×
            (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F)) => p.1 * p.2 * p.1⁻¹ := by
      rw [hμ, Measure.restrict_smul, hmain, Measure.prod_smul_left,
        Measure.map_smul _ measurable_centralQuotientConj.aemeasurable]
    exact integral_fubini_of_restrict_eq_map measurable_centralQuotientConj h hΦ

end Langlands.BaseChange
