import Langlands.Global.AdelicIntrinsicStandardFamily
import Langlands.Global.AdelicNestedRadicalLattices
import Langlands.Global.DiscreteLeftCosetMeasureTransport

/-! # The complementary radical and its Haar measure in the intrinsic Levi -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set Topology
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints AdelicSubgroupPoints

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) {I Q : StandardIndex F G fam.i fam.ν}
  (d : fam.NestedRadicalSplit I Q)

local notation "p" => fam.p Q
local notation "l" => fam.l Q
local notation "u" => fam.iU Q
local notation "j" => (l ≫ p)
local notation "v" => (fam.iU I ≫ fam.p I)
local notation "M" => fam.M Q
local notation "hU" => fam.isUnipotentRadical Q
local instance : IsAffineHom (M).X.hom := (fam.isCompatible Q).levi.isConnectedReductive.isAffineHom

omit [NumberField F] in
/-- The Levi inclusion of the complementary radical represents the preimage of the
ambient nested radical in the outer Levi. -/
theorem range_complementLeviHom :
    SubgroupFunctor.range d.leviHom = (SubgroupFunctor.range v).comap j := by
  let : Mono (p).hom.hom.left := (fam.isCompatible Q).parabolic.isClosedSubgroup.mono
  let : Mono (p).hom.hom := Over.mono_of_mono_left _
  let : IsIso (subgroupMultiplication l u) :=
    Langlands.Plancherel.parabolicRadical_isIso_subgroupMultiplication
      (⟨⟨fam.T, fam.i, fam.ν, Q.val, fam.f Q⟩, fam.isCompatible Q⟩ :
        ParabolicRootPresentation p l (fam.a Q)) fam.connectedReductive hU
  let π := leviRetraction l u (hU).1.isNormal
  apply SubgroupFunctor.ext
  intro X
  apply Subgroup.ext
  intro x
  rw [SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨s, rfl⟩
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨s ≫ d.sectionHom.hom.hom, ?_⟩
    have h := congrArg (fun f => f.hom.hom) d.section_comp
    simpa only [Grp.comp_hom_hom, Category.assoc] using congrArg (s ≫ ·) h
  · intro hx
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hx
    let s := z ≫ d.projection.hom.hom
    let t := s ≫ d.sectionHom.hom.hom
    have htz : t ≫ d.projection.hom.hom = z ≫ d.projection.hom.hom := by
      change (s ≫ d.sectionHom.hom.hom) ≫ d.projection.hom.hom = s
      rw [Category.assoc, ← Grp.comp_hom_hom, d.section_projection, Grp.id_hom_hom, Category.comp_id]
    have hk : (z * t⁻¹) ≫ d.projection.hom.hom = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, htz, mul_inv_cancel]
    obtain ⟨n, hn⟩ := (d.kernel X (z * t⁻¹)).mp hk
    have hz' : (n ≫ d.normal.hom.hom) * t = z := by rw [hn, inv_mul_cancel_right]
    have hpEq :
        (n ≫ (u).hom.hom) * (s ≫ d.leviHom.hom.hom ≫ (l).hom.hom) =
          x ≫ (l).hom.hom := by
      apply (cancel_mono (p).hom.hom).mp
      have hnormal := congrArg (fun f => f.hom.hom) d.normal_comp
      have hsection := congrArg (fun f => f.hom.hom) d.section_comp
      simp only [Grp.comp_hom_hom] at hnormal hsection hz
      rw [MonObj.mul_comp]
      simp only [Category.assoc]
      rw [← hnormal, ← hsection]
      simpa only [MonObj.mul_comp, t, Category.assoc] using
        (congrArg (· ≫ (fam.iU I).hom.hom ≫ (fam.p I).hom.hom) hz').trans hz
    have hnπ : (n ≫ (u).hom.hom) ≫ π.hom.hom = 1 :=
      (comp_leviRetraction_eq_one_iff l u (hU).1.isNormal _).mpr ⟨n, rfl⟩
    have hlπ (y : X ⟶ (M).X) : (y ≫ (l).hom.hom) ≫ π.hom.hom = y := by
      rw [Category.assoc, ← Grp.comp_hom_hom, levi_comp_leviRetraction, Grp.id_hom_hom, Category.comp_id]
    refine ⟨s, ?_⟩
    have hret := congrArg (· ≫ π.hom.hom) hpEq
    rw [MonObj.mul_comp, hnπ, one_mul, ← Category.assoc s, hlπ, hlπ] at hret
    exact hret

variable (hIQ : I ≤ Q)

local notation "low" => fam.intrinsicStandardFamily Q
local notation "L" => fam.intrinsicStandardIndex Q I hIQ
set_option quotPrecheck false in
local notation "r" => (low).iU L ≫ (low).p L
local notation "w" => d.complementHom fam

omit [NumberField F] in
private theorem complementLevi_closed : IsClosedSubgroup d.leviHom := by
  have hw : IsClosedSubgroup (d.leviHom ≫ j) := by
    rw [← d.section_comp]
    exact d.complement_closed fam
  change IsClosedImmersion (d.leviHom ≫ j).hom.hom.left at hw
  have : IsClosedImmersion (d.leviHom.hom.hom.left ≫ (j).hom.hom.left) := by
    simpa only [Grp.comp_hom_hom, Over.comp_left] using hw
  exact IsClosedImmersion.of_comp _ (j).hom.hom.left

/-- The intrinsic radical and the complementary radical are the representatives
of the same subgroup of the outer Levi. -/
def intrinsicRadicalSchemeIso : (low).U L ≅ d.W := by
  have hw : SubgroupFunctor.range r = SubgroupFunctor.range d.leviHom := by
    rw [(low).range_radical_eq_standardUnipotent, fam.range_complementLeviHom d,
      fam.range_radical_eq_standardUnipotent]
    exact ((fam.intrinsicStandardRootData Q).2.2.2 I.val hIQ).2.2
  let hr : IsClosedSubgroup r := (low).closedU L
  let : Mono (r).hom.hom.left := hr.mono
  let : Mono d.leviHom.hom.hom.left := (fam.complementLevi_closed d).mono
  let h₁ : (SubgroupFunctor.range r).IsRepresentedBy r := ⟨Over.mono_of_mono_left _, rfl⟩
  let h₂ : (SubgroupFunctor.range r).IsRepresentedBy d.leviHom := ⟨Over.mono_of_mono_left _, hw.symm⟩
  exact h₁.isoOfIsRepresentedBy h₂

set_option maxHeartbeats 1800000 in
omit [NumberField F] in
theorem intrinsicRadicalSchemeIso_hom_comp :
    (fam.intrinsicRadicalSchemeIso d hIQ).hom ≫ w = r ≫ j := by
  have h₀ : w = d.leviHom ≫ j := d.section_comp
  rw [h₀, ← Category.assoc]
  congr 1
  unfold intrinsicRadicalSchemeIso
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

local notation "W" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range w)
local notation "U" => AdelicSubgroupPoints.adelicPoints F M (SubgroupFunctor.range r)
local notation "ΓW" => AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range w)
local notation "ΓU" => AdelicSubgroupPoints.rationalSubgroup F M (SubgroupFunctor.range r)
local notation "dW" => AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G (SubgroupFunctor.range w)
local notation "dU" => AdelicSubgroupPoints.isDiscrete_rationalSubgroup F M (SubgroupFunctor.range r)

private theorem isClosed_complementAdelic : IsClosed (W : Set (AdelicGroupPoints F G)) := by
  have hw := d.complement_closed fam
  let : IsClosedImmersion (w).hom.hom.left := hw
  let : IsAffine d.W.X.left := isAffine_left_of_isClosedSubgroup F w hw
  exact isClosed_adelicPoints_range F G w

local instance : IsClosed (W : Set (AdelicGroupPoints F G)) := fam.isClosed_complementAdelic d
local instance : IsClosed (U : Set (AdelicGroupPoints F M)) := isClosed_adelicPoints_range F M r
local instance : LocallyOfFiniteType (M).X.hom := fam.finiteTypeM Q

private def rangePointIso {H H' : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H'.X.left]
    (f : H ⟶ H') (hf : IsClosedSubgroup f) :
    AdelicGroupPoints F H ≃ₜ* AdelicSubgroupPoints.adelicPoints F H' (SubgroupFunctor.range f) := by
  let : IsClosedImmersion f.hom.hom.left := hf
  let : IsAffine H.X.left := isAffine_left_of_isClosedSubgroup F f hf
  exact rangeEquiv F f (isClosedEmbedding_map F H H' f).isEmbedding

private theorem rangePointIso_mem_principal
    {H H' : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H'.X.left]
    (f : H ⟶ H') (hf : IsClosedSubgroup f) (x : AdelicGroupPoints F H) :
    rangePointIso f hf x ∈ AdelicSubgroupPoints.rationalSubgroup F H' (SubgroupFunctor.range f) ↔
      x ∈ AdelicGroupPoints.rationalSubgroup F H := by
  rw [mem_rationalSubgroup_range_iff]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, (rangePointIso f hf).injective (Subtype.ext hy)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩

/-- The adelic group isomorphism commutes with the ambient embeddings,
identifies the principal lattices and preserves their quotient-normalized Haar measures. -/
def IntrinsicRadicalHaarStatement : Prop :=
  ∃ e : U ≃ₜ* W, (∀ x : U, (e x).val = map F M G j x.val) ∧
    (∀ x : U, e x ∈ ΓW ↔ x ∈ ΓU) ∧
    MeasurePreserving e (normalizedHaarMeasure F M (SubgroupFunctor.range r))
      (normalizedHaarMeasure F G (SubgroupFunctor.range w))

set_option maxHeartbeats 2500000 in
theorem intrinsicRadicalHaar : fam.IntrinsicRadicalHaarStatement d hIQ := by
  let e := fam.intrinsicRadicalSchemeIso d hIQ
  let a := rangePointIso r ((low).closedU L)
  let b := rangePointIso w (d.complement_closed fam)
  let c := adelicPointsIso F e
  let E := (a.symm.trans c).trans b
  have hE (x : U) : (E x).val = map F M G j x.val := by
    change map F d.W G w (map F ((low).U L) d.W e.hom (a.symm x)) = _
    rw [← map_comp_apply_of_hom, fam.intrinsicRadicalSchemeIso_hom_comp d hIQ, map_comp_apply_of_hom]
    exact congrArg (fun y : U => map F M G j y.val) (a.apply_symm_apply x)
  have hLat (x : U) : E x ∈ ΓW ↔ x ∈ ΓU := by
    change b (c (a.symm x)) ∈ ΓW ↔ x ∈ ΓU
    rw [rangePointIso_mem_principal, ← show a (a.symm x) = x from a.apply_symm_apply x,
      rangePointIso_mem_principal, a.symm_apply_apply]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨d.W.affinePointsTarget e.inv (CommAlgCat.of F F) y, ?_⟩
      rw [← map_rational, hy]
      exact c.symm_apply_apply _
    · rintro ⟨y, hy⟩
      refine ⟨_, (map_rational e.hom y).symm.trans ?_⟩
      exact congrArg c hy
  let : LocallyCompactSpace U := (show IsClosed (U : Set (AdelicGroupPoints F M)) from inferInstance).locallyCompactSpace
  let : LocallyCompactSpace W := (fam.isClosed_complementAdelic d).locallyCompactSpace
  let du : Measure U := Measure.haar
  let dw := du.map E
  let : dw.IsHaarMeasure := E.isHaarMeasure_map du
  have hp : MeasurePreserving E du dw := ⟨E.continuous.measurable, rfl⟩
  have hq := LeftCosetSpace.measurePreserving_discreteQuotientMeasure E ΓU ΓW hLat dU dW du dw hp
  have hmass : dw (LeftCosetSpace.fundamentalDomain ΓW dW) =
      du (LeftCosetSpace.fundamentalDomain ΓU dU) := by
    have h := congrArg (fun (m : Measure (LeftCosetSpace ΓW)) => m univ) hq.map_eq
    rw [Measure.map_apply hq.measurable MeasurableSet.univ, preimage_univ,
      LeftCosetSpace.discreteQuotientMeasure, LeftCosetSpace.discreteQuotientMeasure,
      LeftCosetSpace.quotientMeasure_univ, LeftCosetSpace.quotientMeasure_univ] at h
    exact h.symm
  refine ⟨E, hE, hLat, hp.measurable, ?_⟩
  rw [← normalizedHaarMeasureFrom_eq F M (SubgroupFunctor.range r) du,
    ← normalizedHaarMeasureFrom_eq F G (SubgroupFunctor.range w) dw]
  change Measure.map E ((du (LeftCosetSpace.fundamentalDomain ΓU dU))⁻¹ • du) =
    (dw (LeftCosetSpace.fundamentalDomain ΓW dW))⁻¹ • dw
  rw [hmass, Measure.map_smul _ hp.measurable.aemeasurable, hp.map_eq]

end Langlands.Global.StandardParabolicFamily
