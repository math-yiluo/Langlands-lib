import Langlands.BruhatTits.SpecialCompact.ApartmentCompactTransport
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.Representation.Plancherel.DynamicOppositeConjugationScalar
import Langlands.Analysis.Local.QuotientCompactOpenOrbitProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralQuotientHaar
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviDiscreteSeriesOrbitFiniteness

/-! # Source compact and split-central quotient Haar normalizations -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 650000

universe u uM uN

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Topology
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.SpecialCompact
open Langlands.AlgebraicGeometry.PointTopology Langlands.HarishChandraSchwartz

namespace Langlands.Plancherel.WaldspurgerSourceNormalization

section CompactGeometry

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- The source compact is the actual norm-one fixer of a special vertex in
an `ord_F`-compatible apartment of the displayed maximal split torus. -/
def IsSourceCompactAt (i : S.toGrp ⟶ G) (K : Subgroup (rationalPoints G)) : Prop :=
  IsCompactOpenMaximal F K ∧
    ∃ hi : IsMaximalSplitTorus i,
      let : Mono i.hom.hom.left := mono_of_isMaximalSplitTorus hi
      ∃ (C : CentralizerDatum i) (D : KPApartmentData i (localFieldOrder F)) (x : D.Apartment),
        D.IsOmegaCompatible C ∧ D.IsSpecialApartmentVertex x ∧ D.specialCompactSubgroup x = K

/-- The displayed cocharacter belongs to a maximal split torus with the
same source compact. Its centralizer contains that torus. -/
def IsSourceCompactFor (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (K : Subgroup (rationalPoints G)) : Prop :=
  ∃ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G) (ζ : cocharacterLattice S),
    χ = CommGroupScheme.groupHom ζ ≫ i ∧ IsSourceCompactAt i K

/-- The actual based inner isomorphism carries the apartment, its special
vertex, and the same compact trace normalization to the conjugate torus. -/
theorem IsSourceCompactAt.inner {i : S.toGrp ⟶ G} {K : Subgroup (rationalPoints G)}
    (hK : IsSourceCompactAt i K) (g : rationalPoints G) :
    IsSourceCompactAt (i ≫ (G.innerIso g).hom) (K.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hmax, hi, C, D, x, hD, hx, hfix⟩ := hK
  let f := G.innerIso g
  let hj := hi.comp_iso f
  let : Mono i.hom.hom.left := mono_of_isMaximalSplitTorus hi
  let : Mono (i ≫ f.hom).hom.hom.left := mono_of_isMaximalSplitTorus hj
  let e := CategoryTheory.Iso.refl S
  let hs : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ (i ≫ f.hom) := by
    change i ≫ f.hom = 𝟙 _ ≫ (i ≫ f.hom)
    rw [Category.id_comp]
  have hmax' := isCompactOpenMaximal_mapIso f K hmax
  rw [show f = G.innerIso g from rfl, rationalPoints_map_innerIso] at hmax'
  refine ⟨hmax', hj, C.mapIso f, D.transport e f hs, D.apartmentTransportEquiv e f hs x,
    hD.mapIso C f, (D.isSpecialApartmentVertex_transport_iff e f hs x).mpr hx, ?_⟩
  rw [← D.map_specialCompactSubgroup_transport e f hs x, hfix]
  simp only [f, rationalPoints_map_innerIso]

/-- The cocharacter and its chosen source compact transport by the same
actual ambient conjugation. -/
theorem IsSourceCompactFor.inner {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
    {K : Subgroup (rationalPoints G)} (hK : IsSourceCompactFor χ K) (g : rationalPoints G) :
    IsSourceCompactFor (χ ≫ (G.innerIso g).hom) (K.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨S, i, ζ, rfl, hK⟩ := hK
  exact ⟨S, i ≫ (G.innerIso g).hom, ζ, Category.assoc _ _ _, hK.inner g⟩

end CompactGeometry

section QuotientScale

variable {M : Type uM} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
  (C : Subgroup M) [C.Normal] (L : OpenSubgroup M)

/-- The image of the exact compact Levi trace in the split-central quotient. -/
def quotientTrace : OpenSubgroup (M ⧸ C) where
  toSubgroup := L.toSubgroup.map (QuotientGroup.mk' C)
  isOpen' := QuotientGroup.isOpenQuotientMap_mk.isOpenMap _ L.isOpen

@[simp]
theorem coe_quotientTrace : (quotientTrace C L : Set (M ⧸ C)) =
    QuotientGroup.mk '' (L : Set M) := rfl

/-- The image retains compactness in the actual quotient topology. -/
theorem quotientTrace_isCompact (hL : IsCompact (L : Set M)) :
    IsCompact (quotientTrace C L : Set (M ⧸ C)) :=
  hL.image QuotientGroup.continuous_mk

variable [MeasurableSpace (M ⧸ C)]

/-- The prescribed absolute quotient scale, using the original compact trace. -/
def IsNormalizedQuotientHaar (mu : Measure (M ⧸ C)) : Prop :=
  mu (quotientTrace C L : Set (M ⧸ C)) = 1

/-- A chosen Haar probability on the trace has no additional free scalar. -/
theorem IsNormalizedQuotientHaar.eq_of_haar [LocallyCompactSpace M]
    [SecondCountableTopology M] [BorelSpace (M ⧸ C)]
    (mu ν : Measure (M ⧸ C)) [mu.IsHaarMeasure] [ν.IsHaarMeasure]
    (hmu : IsNormalizedQuotientHaar C L mu) (hν : IsNormalizedQuotientHaar C L ν) : mu = ν := by
  let : SecondCountableTopology (M ⧸ C) :=
    QuotientGroup.isOpenQuotientMap_mk.secondCountableTopology
  let : LocallyCompactSpace (M ⧸ C) := QuotientGroup.isOpenQuotientMap_mk.locallyCompactSpace
  have he := isMulLeftInvariant_eq_smul mu ν
  have hscale := congrArg (fun rho : Measure (M ⧸ C) => rho (quotientTrace C L : Set (M ⧸ C))) he
  change mu (quotientTrace C L : Set (M ⧸ C)) = _ at hscale
  rw [show mu (quotientTrace C L : Set (M ⧸ C)) = 1 from hmu, Measure.smul_apply,
    show ν (quotientTrace C L : Set (M ⧸ C)) = 1 from hν] at hscale
  have h : (haarScalarFactor mu ν : ℝ≥0∞) = 1 := by
    simpa only [ENNReal.smul_def, smul_eq_mul, mul_one] using hscale.symm
  have hscalar : haarScalarFactor mu ν = 1 := ENNReal.coe_injective h
  rw [he, hscalar, one_smul]

section Weil

open QuotientIntegration

variable [BorelSpace (M ⧸ C)] [T2Space M] [LocallyCompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace C] [BorelSpace C]
  [MeasurableSpace (LeftQuotient C)] [BorelSpace (LeftQuotient C)]
  (hC : IsClosed (C : Set M)) (hL : IsCompact (L : Set M))
  (μM : Measure M) [μM.IsHaarMeasure] [μM.Regular]
  (μC : Measure C) [μC.IsHaarMeasure] [μC.Regular] [IsMulRightInvariant μC]

include hC hL in
/-- The Weil quotient for the two mass-one trace Haar measures has mass one
on the compact quotient trace. This applies to the split center of the Levi. -/
theorem normalizedQuotientHaar_of_weil (ν : Measure (LeftQuotient C))
    (hν : IsCompatible C μM μC ν)
    (hM : μM (L : Set M) = 1) (hCenter : μC {c : C | (c : M) ∈ L} = 1) :
    IsNormalizedQuotientHaar C L (ν.map (normalLeftQuotientHomeomorph C)) := by
  let e := normalLeftQuotientHomeomorph C
  have he : e ⁻¹' (quotientTrace C L : Set (M ⧸ C)) = leftQuotientMap C '' (L : Set M) := by
    have himage : (quotientTrace C L : Set (M ⧸ C)) =
        e '' (leftQuotientMap C '' (L : Set M)) := (Set.image_image e (leftQuotientMap C) (L : Set M)).symm
    rw [himage, Set.preimage_image_eq _ e.injective]
  have ht := IsCompatible.integral_compactOpenOrbit C hC μM μC L hL ν hν 1 (fun _ => 1) continuous_const
  simp only [inv_one, one_mul, mul_one, hCenter, ENNReal.toReal_one, integral_const,
    measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, hM] at ht
  let : T2Space (LeftQuotient C) := leftQuotient_t2Space C hC
  let : ν.Regular := hν.regular
  have hfinite : ν (leftQuotientMap C '' (L : Set M)) ≠ ⊤ :=
    (hL.image (leftQuotient_isOpenQuotientMap C).continuous).measure_lt_top.ne
  unfold IsNormalizedQuotientHaar
  rw [Measure.map_apply e.continuous.measurable (quotientTrace C L).isOpen.measurableSet, he]
  exact (ENNReal.toReal_eq_toReal_iff' hfinite ENNReal.one_ne_top).mp ht

include hC hL in
omit [μM.Regular] in
/-- At the two mass-one ambient and central traces, the given quotient Haar
has the source scale exactly when it equals the compatible Weil measure. -/
theorem normalizedQuotientHaar_iff_eq_weil [SecondCountableTopology M]
    (hc : C ≤ Subgroup.center M) (ν : Measure (LeftQuotient C)) (hν : IsCompatible C μM μC ν)
    (hM : μM (L : Set M) = 1) (hCenter : μC {c : C | (c : M) ∈ L} = 1)
    (rho : Measure (M ⧸ C)) [rho.IsHaarMeasure] :
    IsNormalizedQuotientHaar C L rho ↔ rho = ν.map (normalLeftQuotientHomeomorph C) := by
  have hn := normalizedQuotientHaar_of_weil C L hC hL μM μC ν hν hM hCenter
  refine ⟨fun hr => ?_, fun he => he.symm ▸ hn⟩
  obtain ⟨a, _, ha⟩ := hν.exists_smul_eq_map hC hc rho
  have hv := congrArg (fun v : Measure (M ⧸ C) => v (quotientTrace C L : Set (M ⧸ C))) ha
  change (ν.map (normalLeftQuotientHomeomorph C)) (quotientTrace C L : Set (M ⧸ C)) = _ at hv
  change (ν.map (normalLeftQuotientHomeomorph C)) (quotientTrace C L : Set (M ⧸ C)) = 1 at hn
  change rho (quotientTrace C L : Set (M ⧸ C)) = 1 at hr
  rw [hn, Measure.smul_apply, hr] at hv
  have hscale : (a : ℝ≥0∞) = 1 := by
    simpa only [ENNReal.smul_def, smul_eq_mul, mul_one] using hv.symm
  rw [ha, show a = 1 from ENNReal.coe_injective hscale, one_smul]

end Weil

section Transport

variable {N : Type uN} [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
  (C' : Subgroup N) [C'.Normal] (L' : OpenSubgroup N)
  (e : N ≃ₜ* M) (he : C'.map e.toMonoidHom = C)
  [BorelSpace (M ⧸ C)] [MeasurableSpace (N ⧸ C')] [BorelSpace (N ⧸ C')]

/-- The absolute quotient scale follows the prescribed trace under the
actual quotient isomorphism. -/
theorem normalizedQuotientHaar_map_iff (hL : ∀ n : N, e n ∈ L ↔ n ∈ L')
    (mu : Measure (N ⧸ C')) :
    IsNormalizedQuotientHaar C L (mu.map (quotientContinuousMulEquiv e C C' he)) ↔
      IsNormalizedQuotientHaar C' L' mu := by
  let E := quotientContinuousMulEquiv e C C' he
  have hpre : E ⁻¹' (quotientTrace C L : Set (M ⧸ C)) = quotientTrace C' L' := by
    ext x
    simp only [Set.mem_preimage, coe_quotientTrace, Set.mem_image]
    constructor
    · rintro ⟨m, hm, heq⟩
      refine ⟨e.symm m, (hL _).mp (by
        change e (e.symm m) ∈ (L : Set M)
        simpa only [e.apply_symm_apply] using hm), ?_⟩
      apply E.injective
      simpa only [E, quotientContinuousMulEquiv_mk, e.apply_symm_apply] using heq
    · rintro ⟨n, hn, rfl⟩
      exact ⟨e n, (hL n).mpr hn, rfl⟩
  unfold IsNormalizedQuotientHaar
  have hmeas : Measurable (E : (N ⧸ C') → M ⧸ C) := E.continuous.measurable
  rw [Measure.map_apply hmeas (quotientTrace C L).isOpen.measurableSet, hpre]

end Transport
end QuotientScale

section ActualLevi

open DynamicOppositeStandardIntertwining

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (K : OpenSubgroup (RationalPoint F G.X))

/-- The actual split-central quotient Haar has the absolute source scale
fixed by the image of `M ∩ K` in `M/A_M`. -/
def IsSourceQuotientHaar (C : Subgroup (levi χ)) [C.Normal]
    [MeasurableSpace (levi χ ⧸ C)] (mu : Measure (levi χ ⧸ C)) : Prop :=
  IsNormalizedQuotientHaar C (K.comap (levi χ).subtype continuous_subtype_val) mu

variable (g : RationalPoint F G.X) (K' : OpenSubgroup (RationalPoint F G.X))
  (hKK' : RationalDynamicSource.conjugateCompact g K = K')

include hKK' in
/-- Transported compacts retain the actual special point normalization. -/
theorem isSourceCompactFor_conjugate (hK : IsSourceCompactFor χ K.toSubgroup) :
    IsSourceCompactFor (χ ≫ (G.innerIso g).hom) K'.toSubgroup := by
  have h : K.toSubgroup.map (MulAut.conj g).toMonoidHom = K'.toSubgroup := by
    ext x
    obtain ⟨x, rfl⟩ := (MulAut.conj g).surjective x
    have hm := Subgroup.mem_map_iff_mem (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective (K := K.toSubgroup) (x := x)
    refine hm.trans ?_
    change x ∈ K ↔ g * x * g⁻¹ ∈ K'
    rw [← hKK', RationalDynamicSource.mem_conjugateCompact]
  exact h ▸ hK.inner g

set_option hygiene false in
set_option quotPrecheck false in
local notation "χg" => (χ ≫ (G.innerIso g).hom)

include hKK' in
/-- Pushforward equality at the source-normalized scale gives the prescribed
target scale on the actual conjugate quotient trace. -/
theorem isSourceQuotientHaar_conjugate
    (C : Subgroup (levi χ)) [C.Normal] (C' : Subgroup (levi χg)) [C'.Normal]
    (hc : C'.map (leviConjugation χ g).symm.toMonoidHom = C)
    [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
    [MeasurableSpace (levi χg ⧸ C')] [BorelSpace (levi χg ⧸ C')]
    (q : Measure (levi χ ⧸ C)) (q' : Measure (levi χg ⧸ C'))
    (hmap : q'.map (quotientContinuousMulEquiv (leviConjugation χ g).symm C C' hc) = q)
    (hq : IsSourceQuotientHaar χ K C q) : IsSourceQuotientHaar χg K' C' q' := by
  let e := leviConjugation χ g
  let L := K.comap (levi χ).subtype continuous_subtype_val
  let L' := K'.comap (levi χg).subtype continuous_subtype_val
  refine (normalizedQuotientHaar_map_iff C L C' L' e.symm hc (fun n => ?_) q').mp ?_
  · have h := RationalDynamicSource.mem_conjugateCompact g (e.symm n : RationalPoint F G.X) K
    rw [hKK'] at h
    have he : g * (e.symm n : RationalPoint F G.X) * g⁻¹ = (n : RationalPoint F G.X) :=
      (leviConjugation_apply_coe χ g (e.symm n)).symm.trans
        (congrArg Subtype.val (e.apply_symm_apply n))
    rw [he] at h
    exact h.symm
  · change IsSourceQuotientHaar χ K C
      (q'.map (quotientContinuousMulEquiv (leviConjugation χ g).symm C C' hc))
    rw [hmap]
    exact hq

end ActualLevi

end Langlands.Plancherel.WaldspurgerSourceNormalization
