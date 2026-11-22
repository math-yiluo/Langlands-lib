import Langlands.Global.LeftCosetParabolicPeriodVanishing
import Langlands.Global.EisensteinConstantTerm.Points
import Langlands.Global.AdelicLeviFiniteVolume
import Langlands.Global.UnipotentRationalQuotientCompactProof
import Langlands.Automorphic.GroupSchemeParabolicL2Period
import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.Analysis.Local.QuotientMeasureEquiv
import Langlands.GroupScheme.Rational.LeviRetraction

/-! # Vanishing of an adelic parabolic period from the radical constant term -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set Topology
open scoped CategoryTheory.MonObj ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints Langlands.QuotientIntegration
  Langlands.Automorphic.GroupSchemeFunctions

private theorem integral_fundamentalDomain_map
    {S T : Type u} [Group S] [Group T] [TopologicalSpace S] [TopologicalSpace T]
    [IsTopologicalGroup S] [IsTopologicalGroup T] [SecondCountableTopology S] [SecondCountableTopology T]
    [MeasurableSpace S] [MeasurableSpace T] [BorelSpace S] [BorelSpace T]
    (e : S ≃ₜ* T) (Γ : Subgroup S) (Λ : Subgroup T)
    (h : ∀ x, e x ∈ Λ ↔ x ∈ Γ) (hΓ : IsDiscrete (Γ : Set S))
    (hΛ : IsDiscrete (Λ : Set T)) (m : Measure S) [m.IsMulLeftInvariant]
    [(m.map e).IsMulLeftInvariant] (f : T → ℂ) (hf : ∀ a : Λ, ∀ x, f (a.val * x) = f x) :
    (∫ x in LeftCosetSpace.fundamentalDomain Λ hΛ, f x ∂m.map e) =
      ∫ x in LeftCosetSpace.fundamentalDomain Γ hΓ, f (e x) ∂m := by
  let a := subgroupContinuousMulEquiv e Γ Λ h
  let E := LeftCosetSpace.fundamentalDomain Γ hΓ
  let mp : MeasurePreserving e m (m.map e) := ⟨e.continuous.measurable, rfl⟩
  have hE : IsFundamentalDomain Λ (e '' E) (m.map e) :=
    (LeftCosetSpace.isFundamentalDomain Γ hΓ m).image_of_equiv e.toMulEquiv.toEquiv
      (mp.symm e.toHomeomorph.toMeasurableEquiv).quasiMeasurePreserving
      a.symm.toMulEquiv.toEquiv fun b x => by
        change e ((e.symm b.val) * x) = b.val * e x
        rw [map_mul, e.apply_symm_apply]
  let : Countable Λ := LeftCosetSpace.countable_of_isDiscrete Λ hΛ
  rw [(LeftCosetSpace.isFundamentalDomain Λ hΛ _).setIntegral_eq hE hf]
  exact (mp.setIntegral_image_emb e.toHomeomorph.isClosedEmbedding.measurableEmbedding f E)

variable {F : Type u} [Field F] [NumberField F]
  {G P L U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine U.X.left] [LocallyOfFiniteType U.X.hom]

private theorem integral_radical_fundamentalDomain_eq_zero
    (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left] [CompactSpace (RationalQuotient F U)]
    (f : AdelicGroupPoints F G → ℂ) (hf : Continuous f)
    (hInv : IsLeftInvariantUnder F G (rationalImage F j) f)
    (g : AdelicGroupPoints F G) (hzero : subgroupConstantTerm F j f g = 0) :
    ∫ u in LeftCosetSpace.fundamentalDomain (rationalSubgroup F U) (isDiscrete_rationalSubgroup F U),
      f (map F U G j u * g) ∂Measure.haar = 0 := by
  let V := AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)
  let ΓV := AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range j)
  let ΓU := rationalSubgroup F U
  let hΓV := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G (SubgroupFunctor.range j)
  let hΓU := isDiscrete_rationalSubgroup F U
  let hV := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : IsClosed (V : Set (AdelicGroupPoints F G)) := hV
  let : LocallyCompactSpace V := hV.locallyCompactSpace
  let : CompactSpace (LeftCosetSpace ΓV) := AdelicSubgroupPoints.compactSpace_rationalQuotient_range F j
  let : IsLocallyFiniteMeasure (LeftCosetSpace.haarQuotientMeasure ΓV hΓV) :=
    LeftCosetSpace.isLocallyFiniteMeasure_haarQuotientMeasure ΓV hΓV
  let : BorelSpace (LeftCosetSpace ΓV) :=
    AdelicSubgroupPoints.rationalQuotientBorelSpace F G (SubgroupFunctor.range j)
  let v := AdelicSubgroupPoints.adelicRangeMap F j
  have hv : IsEmbedding v :=
    IsEmbedding.subtypeVal.of_comp_iff.mp (isClosedEmbedding_map F U G j).isEmbedding
  let a := MulEquiv.ofBijective v ⟨hv.injective, AdelicSubgroupPoints.adelicRangeMap_surjective F j⟩
  let e : AdelicGroupPoints F U ≃ₜ* V :=
    { toMulEquiv := a
      continuous_toFun := AdelicSubgroupPoints.continuous_adelicRangeMap F j
      continuous_invFun := hv.isInducing.continuous_iff.mpr (by
        change Continuous (a ∘ a.symm)
        rw [show a ∘ a.symm = (id : V → V) from funext a.apply_symm_apply]
        exact continuous_id) }
  have he (x : AdelicGroupPoints F U) : e x ∈ ΓV ↔ x ∈ ΓU := by
    constructor
    · rintro ⟨z, hz⟩
      obtain ⟨y, hy⟩ := z.property
      change RationalGroupPoints F U at y
      have hzy : AdelicSubgroupPoints.rationalRangeMap F j y = z := Subtype.ext hy
      refine ⟨y, e.injective ?_⟩
      change AdelicSubgroupPoints.adelicRangeMap F j (rational F U y) = e x
      rw [AdelicSubgroupPoints.adelicRangeMap_rational, hzy, hz]
    · rintro ⟨y, rfl⟩
      exact ⟨AdelicSubgroupPoints.rationalRangeMap F j y,
        (AdelicSubgroupPoints.adelicRangeMap_rational F j y).symm⟩
  let fV : V → ℂ := fun v => f (v.val * g)
  have hfV (δ : ΓV) (x : V) : fV (δ.val * x) = fV x := by
    obtain ⟨z, hz⟩ := δ.property
    obtain ⟨y, hy⟩ := z.property
    change RationalGroupPoints F U at y
    have hδ : δ.val.val ∈ rationalImage F j := by
      refine ⟨y, ?_⟩
      change map F U G j (rational F U y) = δ.val.val
      rw [map_rational]
      exact (congrArg (rational F G) hy).trans (congrArg Subtype.val hz)
    change f ((δ.val.val * x.val) * g) = f (x.val * g)
    rw [mul_assoc, hInv _ hδ]
  let fQ := LeftCosetSpace.lift ΓV fV hfV
  have hfQ : Continuous fQ :=
    LeftCosetSpace.continuous_lift _ _ _ (hf.comp (continuous_subtype_val.mul_const g))
  have hzero' : ∫ q, fQ q
      ∂AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G (SubgroupFunctor.range j) = 0 := by
    convert hzero using 1
    apply integral_congr_ae
    filter_upwards [] with q
    change fQ q = fV q.out
    exact congrArg fQ (Quotient.out_eq q).symm
  rw [AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_eq_normalizedMeasure,
    LeftCosetSpace.normalizedMeasure, integral_smul_measure,
    LeftCosetSpace.integral_quotientMeasure _ _ _ _ hfQ.aestronglyMeasurable] at hzero'
  have hmass : (((Measure.haar : Measure V) (LeftCosetSpace.fundamentalDomain ΓV hΓV))⁻¹).toReal ≠ 0 := by
    apply ENNReal.toReal_ne_zero.mpr
    exact ⟨ENNReal.inv_ne_zero.mpr (LeftCosetSpace.haar_fundamentalDomain_ne_top ΓV hΓV),
      ENNReal.inv_ne_top.mpr (LeftCosetSpace.haar_fundamentalDomain_ne_zero ΓV hΓV)⟩
  have hVzero : ∫ v in LeftCosetSpace.fundamentalDomain ΓV hΓV, fV v ∂Measure.haar = 0 :=
    (smul_eq_zero.mp hzero').resolve_left hmass
  let μU : Measure (AdelicGroupPoints F U) := Measure.haar
  let μV : Measure V := μU.map e
  let : μV.IsHaarMeasure := e.isHaarMeasure_map μU
  have hscalar := Measure.isMulLeftInvariant_eq_smul μV (Measure.haar : Measure V)
  change (∫ u in LeftCosetSpace.fundamentalDomain ΓU hΓU, fV (e u) ∂μU) = 0
  rw [← integral_fundamentalDomain_map e ΓU ΓV he hΓU hΓV μU fV hfV]
  change (∫ v in LeftCosetSpace.fundamentalDomain ΓV hΓV, fV v ∂μV) = 0
  rw [hscalar, Measure.restrict_smul, integral_smul_nnreal_measure, hVzero, smul_zero]

variable [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine L.X.left] [LocallyOfFiniteType L.X.hom]
  (p : P ⟶ G) (l : L ⟶ P) (iU : U ⟶ P)
  [IsClosedImmersion p.hom.hom.left] [IsClosedImmersion (iU ≫ p).hom.hom.left]

/-- The rational parabolic viewed inside the ambient norm-one adelic group. -/
def parabolicRationalNormOneSubgroup : Subgroup (normOneSubgroup F G) :=
  (rationalNormOneSubgroup F P).map (mapNormOne F P G p).toMonoidHom

omit [IsAffine U.X.left] [LocallyOfFiniteType U.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine L.X.left] [LocallyOfFiniteType L.X.hom]
  [IsClosedImmersion p.hom.hom.left] [IsClosedImmersion (iU ≫ p).hom.hom.left] in
theorem isDiscrete_parabolicRationalNormOneSubgroup :
    IsDiscrete (parabolicRationalNormOneSubgroup p : Set (normOneSubgroup F G)) := by
  apply (isDiscrete_rationalNormOneSubgroup F G).mono
  rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
  exact ⟨P.affinePointsTarget p _ y, (mapNormOne_rationalNormOne F P G p y).symm⟩

/-- An absolutely integrable period on `P(F) \ G(𝔸)¹` vanishes if the
actual normalized constant term along the radical of `P` vanishes. -/
def AdelicParabolicPeriodVanishingStatement : Prop :=
  LeviSubgroup.IsGeometricUnipotentRadical iU →
  IsIso (subgroupMultiplication l iU) →
  IsFiniteMeasure (normOneRationalQuotientHaarMeasure F G) →
  IsFiniteMeasure (normOneRationalQuotientHaarMeasure F P) →
  IsFiniteMeasure (normOneRationalQuotientHaarMeasure F L) →
  ∀ f : AdelicGroupPoints F G → ℂ, Continuous f →
    IsLeftInvariantUnder F G (rationalImage F p) f →
    IntegrableOn (fun g : normOneSubgroup F G => f g.val)
      (LeftCosetSpace.fundamentalDomain (parabolicRationalNormOneSubgroup p)
        (isDiscrete_parabolicRationalNormOneSubgroup p)) Measure.haar →
    subgroupConstantTerm F (iU ≫ p) f = 0 →
    ∫ g in LeftCosetSpace.fundamentalDomain (parabolicRationalNormOneSubgroup p)
        (isDiscrete_parabolicRationalNormOneSubgroup p),
      f g.val ∂Measure.haar = 0

set_option maxHeartbeats 1400000 in
theorem adelicParabolicPeriodVanishing : AdelicParabolicPeriodVanishingStatement p l iU := by
  intro hU hsplit hGfin hPfin hLfin f hf hInv hInt hZero
  let : IsIso (subgroupMultiplication l iU) := hsplit
  let : IsClosedImmersion iU.hom.hom.left := hU.1.isClosedSubgroup
  let : CompactSpace (RationalQuotient F U) :=
    unipotentRationalQuotientCompact F U hU.1.smooth hU.1.connectedSpace hU.1.isUnipotent
  let proj := leviRetraction l iU hU.1.isNormal
  let M := normOneSubgroup F G
  let S := normOneSubgroup F P
  let H := (mapNormOne F P G p).toMonoidHom.range
  let ΓP := rationalNormOneSubgroup F P
  let Γ := parabolicRationalNormOneSubgroup p
  let hΓ := isDiscrete_parabolicRationalNormOneSubgroup p
  let fM : M → ℂ := fun g => f g.val
  let μM : Measure M := Measure.haar
  let μP : Measure S := Measure.haar
  have hemb : IsClosedEmbedding (mapNormOne F P G p) := by
    apply IsClosedEmbedding.of_comp (IsEmbedding.subtypeVal (p := (· ∈ normOneSubgroup F G)))
    exact (isClosedEmbedding_map F P G p).comp
      (isClosed_normOneSubgroup F P).isClosedEmbedding_subtypeVal
  have hH : IsClosed (H : Set M) := hemb.isClosed_range
  let e : S ≃ₜ* H :=
    { toMulEquiv := MonoidHom.ofInjective (f := (mapNormOne F P G p).toMonoidHom) hemb.injective
      continuous_toFun := (mapNormOne F P G p).continuous.subtype_mk _
      continuous_invFun := hemb.isEmbedding.isInducing.continuous_iff.mpr (by
        change Continuous (fun x : H =>
          (mapNormOne F P G p).toMonoidHom ((MonoidHom.ofInjective hemb.injective).symm x))
        simpa only [MonoidHom.apply_ofInjective_symm] using continuous_subtype_val) }
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let : SecondCountableTopology H :=
    TopologicalSpace.secondCountableTopology_induced _ M Subtype.val
  let : BorelSpace (LeftCosetSpace H) := LeftCosetSpace.quotient_borelSpace H
  let μH : Measure H := μP.map e
  let : μH.IsHaarMeasure := e.isHaarMeasure_map μP
  let : μH.Regular := Measure.Regular.map e.toHomeomorph
  let : IsFiniteMeasure (LeftCosetSpace.haarQuotientMeasure (rationalNormOneSubgroup F G)
    (isDiscrete_rationalNormOneSubgroup F G)) := hGfin
  let : IsFiniteMeasure (LeftCosetSpace.haarQuotientMeasure ΓP
    (isDiscrete_rationalNormOneSubgroup F P)) := hPfin
  let : μM.IsMulRightInvariant := LeftCosetSpace.isMulRightInvariant_haar_of_isFiniteMeasure
    (rationalNormOneSubgroup F G) (isDiscrete_rationalNormOneSubgroup F G)
  let : μP.IsMulRightInvariant := LeftCosetSpace.isMulRightInvariant_haar_of_isFiniteMeasure
    ΓP (isDiscrete_rationalNormOneSubgroup F P)
  let : μH.IsMulRightInvariant := isMulRightInvariant_map e μP
  obtain ⟨ν, hν⟩ := compatibleMeasureExists H hH μM μH
  have hle : Γ ≤ H := fun _ ⟨x, _, hx⟩ => ⟨x, hx⟩
  have hfMInv (b : Γ) (x : M) : fM (b.val * x) = fM x := by
    obtain ⟨_, ⟨y, rfl⟩, hy⟩ := b.property
    exact hInv _ ⟨y, congrArg Subtype.val hy⟩ x.val
  refine LeftCosetSpace.closedSubgroupPeriodVanishing hle hΓ hH μM μH ν hν fM
    (hf.comp continuous_subtype_val).measurable hfMInv hInt fun g => ?_
  let ΓH := Γ.comap H.subtype
  have hΓH : IsDiscrete (ΓH : Set H) :=
    hΓ.preimage continuous_subtype_val.continuousOn Subtype.val_injective
  have heΓ (x : S) : e x ∈ ΓH ↔ x ∈ ΓP := by
    change mapNormOne F P G p x ∈ Γ ↔ x ∈ ΓP
    constructor
    · rintro ⟨y, hy, hey⟩
      exact hemb.injective hey ▸ hy
    · exact fun hx => ⟨x, hx, rfl⟩
  rw [integral_fundamentalDomain_map e ΓP ΓH heΓ
    (isDiscrete_rationalNormOneSubgroup F P) hΓH μP (fun h => fM (h.val * g)) (by
      intro a b
      change fM ((a.val.val * b.val) * g) = fM (b.val * g)
      rw [mul_assoc]
      exact hfMInv ⟨a.val.val, a.property⟩ (b.val * g))]
  let i : AdelicGroupPoints F U →* S :=
    (mapNormOne F U P iU).toMonoidHom.comp
      ((MonoidHom.id _).codRestrict (normOneSubgroup F U) (mem_normOneSubgroup_of_compactSpace F U))
  let j := (mapNormOne F L P l).toMonoidHom
  let π := (mapNormOne F P L proj).toMonoidHom
  let ΓL := rationalNormOneSubgroup F L
  let : IsFiniteMeasure (LeftCosetSpace.haarQuotientMeasure ΓL
    (isDiscrete_rationalNormOneSubgroup F L)) := hLfin
  have hpj (m : normOneSubgroup F L) : π (j m) = m := by
    apply Subtype.ext
    change map F P L proj (map F L P l m.val) = m.val
    rw [← map_comp_apply_of_hom, levi_comp_leviRetraction]
    change (m.val : AdelicGroupPoints F L) ≫ 𝟙 L.X = m.val
    exact Category.comp_id _
  have hker (x : S) : π x = 1 → ∃ n, i n = x := by
    intro hx
    have hx' : x.val ≫ proj.hom.hom = 1 := congrArg Subtype.val hx
    obtain ⟨n, hn⟩ := (comp_leviRetraction_eq_one_iff l iU hU.1.isNormal x.val).mp hx'
    exact ⟨n, Subtype.ext hn⟩
  have hpi (n : AdelicGroupPoints F U) : π (i n) = 1 := by
    apply Subtype.ext
    exact (comp_leviRetraction_eq_one_iff l iU hU.1.isNormal _).mpr ⟨n, rfl⟩
  have hi : IsEmbedding i := IsEmbedding.subtypeVal.of_comp_iff.mp
    (isClosedEmbedding_map F U P iU).isEmbedding
  have hjΓ : ∀ m ∈ ΓL, j m ∈ ΓP := by
    rintro _ ⟨y, rfl⟩
    exact ⟨L.affinePointsTarget l _ y, (mapNormOne_rationalNormOne F L P l y).symm⟩
  have hpΓ : ∀ x ∈ ΓP, π x ∈ ΓL := by
    rintro _ ⟨y, rfl⟩
    exact ⟨P.affinePointsTarget proj _ y, (mapNormOne_rationalNormOne F P L proj y).symm⟩
  have hΓN : ΓP.comap i = rationalSubgroup F U := by
    ext n
    constructor
    · rintro ⟨y, hy⟩
      have hy' : π (rationalNormOne F P y) = 1 := (congrArg π hy).trans (hpi n)
      change mapNormOne F P L proj _ = 1 at hy'
      rw [mapNormOne_rationalNormOne] at hy'
      have hy₁ : y ≫ proj.hom.hom = 1 := by
        change P.affinePointsTarget proj (CommAlgCat.of F F) y = 1
        exact rationalNormOne_injective F L (hy'.trans (map_one _).symm)
      obtain ⟨z, hz⟩ := (comp_leviRetraction_eq_one_iff l iU hU.1.isNormal y).mp hy₁
      change RationalGroupPoints F U at z
      refine ⟨z, hi.injective (Subtype.ext ?_)⟩
      change map F U P iU (rational F U z) = map F U P iU n
      rw [map_rational]
      exact (congrArg (rational F P) hz).trans (congrArg Subtype.val hy)
    · rintro ⟨y, rfl⟩
      exact ⟨U.affinePointsTarget iU _ y, (map_rational iU y).symm |> Subtype.ext⟩
  let hΓU : _root_.IsDiscrete (ΓP.comap i : Set (AdelicGroupPoints F U)) := by
    rw [hΓN]
    exact isDiscrete_rationalSubgroup F U
  have hFinite (Λ : Subgroup (AdelicGroupPoints F U)) (heq : Λ = rationalSubgroup F U)
      (hΛ : _root_.IsDiscrete (Λ : Set (AdelicGroupPoints F U))) :
      IsFiniteMeasure (LeftCosetSpace.haarQuotientMeasure Λ hΛ) := by
    subst Λ
    exact (inferInstance : IsFiniteMeasure (rationalQuotientHaarMeasure F U))
  let : IsFiniteMeasure (LeftCosetSpace.haarQuotientMeasure (ΓP.comap i) hΓU) :=
    hFinite _ hΓN hΓU
  refine LeftCosetSpace.Semidirect.integral_fundamentalDomain_eq_zero_of_normalPeriods
    i j π hpj hker hpi hi (mapNormOne F L P l).continuous (mapNormOne F P L proj).continuous
    ΓP (isDiscrete_rationalNormOneSubgroup F P) ΓL (isDiscrete_rationalNormOneSubgroup F L)
    hjΓ hpΓ hΓU (fun x => fM ((e x).val * g)) (by
      intro a b
      rw [map_mul]
      change fM (((e a.val).val * (e b).val) * g) = fM ((e b).val * g)
      rw [mul_assoc]
      exact hfMInv ⟨(e a.val).val, ⟨a.val, a.property, rfl⟩⟩ _) fun m => ?_
  have hDomain (Λ : Subgroup (AdelicGroupPoints F U)) (heq : Λ = rationalSubgroup F U)
      (hΛ : _root_.IsDiscrete (Λ : Set (AdelicGroupPoints F U))) :
      LeftCosetSpace.fundamentalDomain Λ hΛ =
      LeftCosetSpace.fundamentalDomain (rationalSubgroup F U) (isDiscrete_rationalSubgroup F U) := by
    subst Λ
    rfl
  rw [hDomain _ hΓN hΓU]
  let y : AdelicGroupPoints F G := map F P G p (map F L P l m.val) * g.val
  have hZeroY : subgroupConstantTerm F (iU ≫ p) f y = 0 := congrFun hZero y
  have hInvU : IsLeftInvariantUnder F G (rationalImage F (iU ≫ p)) f := by
    rintro _ ⟨z, rfl⟩ x
    change f (map F U G (iU ≫ p) (rational F U z) * x) = f x
    rw [← map_rational_affinePointsTarget]
    exact hInv _ ⟨U.affinePointsTarget iU _ z, rfl⟩ x
  convert integral_radical_fundamentalDomain_eq_zero (iU ≫ p) f hf hInvU y hZeroY using 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  change f (map F P G p (map F U P iU n * map F L P l m.val) * g.val) =
    f (map F U G (iU ≫ p) n * y)
  rw [map_mul, map_comp_apply_of_hom, mul_assoc]

end Langlands.Global
