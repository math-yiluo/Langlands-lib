import Langlands.Global.AdelicNormOneParabolicCoordinates
import Langlands.Global.AdelicParabolicPeriodVanishing

/-! # Unfolded weighted Iwasawa measure on the norm-one parabolic quotient -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Set Topology
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints.ParabolicIwasawaMeasure

open Langlands.GroupScheme Langlands.Global.PositiveRealTorus
open Langlands.Global.LeftCosetSpace
  (mk fundamentalDomain measurableSet_fundamentalDomain haarQuotientMeasure)

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
  (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P)
  [IsClosedImmersion (iU ≫ p).hom.hom.left] (l : M ⟶ P)
  [IsIso (subgroupMultiplication l iU)] (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)

local notation "G₁" => normOneSubgroup F G
local notation "H" => ambientNormOneLevi p
local notation "L" => ambientNormOneLevi (l ≫ p)
local notation "N" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ p))
local notation "Q" => ambientNormOneParabolicImage p
local notation "ΓG" => parabolicRationalNormOneSubgroup p
local notation "ΓP" => relativeLeviRationalSubgroup p
local notation "ΓM" => relativeLeviRationalSubgroup (l ≫ p)
local notation "ΓN" => AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iU ≫ p))

variable {K : Subgroup (AdelicGroupPoints F G)}

omit [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType P.X.hom]
  [LocallyOfFiniteType M.X.hom] in
/-- Radical, Levi and compact multiplication, followed by the principal parabolic
quotient map. -/
def normOneParabolicQuotientCoordinates (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) :
    (N × L) × K → LeftCosetSpace ΓG := fun x =>
  mk ΓG ((normOneParabolicImageEquiv p (normOneParabolicCoordinates p iU l hU x.1)).val *
    compactToNormOne K hKc x.2)

omit [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType P.X.hom] in
private theorem map_relativeParabolicPrincipal :
    (ΓP).map ((Q).subtype.comp (normOneParabolicImageEquiv p).toMonoidHom) = ΓG := by
  rw [relativeLeviRationalSubgroup, Subgroup.map_map, parabolicRationalNormOneSubgroup]
  rfl

private theorem existsUnique_smul_mem_of_fundamentalDomain_all_measures
    {X B : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [Group B] [MulAction B X]
    {D : Set X} (hD : ∀ dx : Measure X, IsFundamentalDomain B D dx) (x : X) :
    ∃! b : B, b • x ∈ D := by
  have h := hD (Measure.dirac x)
  have hc := h.ae_covers
  rw [ae_dirac_eq, Filter.eventually_pure] at hc
  obtain ⟨a, ha⟩ := hc
  refine ⟨a, ha, fun b hb => ?_⟩
  by_contra hne
  have hd := h.aedisjoint (show b⁻¹ ≠ a⁻¹ from fun he => hne (inv_injective he))
  change Measure.dirac x ((b⁻¹ • D) ∩ (a⁻¹ • D)) = 0 at hd
  have hx : x ∈ (b⁻¹ • D) ∩ (a⁻¹ • D) := by
    simp only [mem_inter_iff, mem_smul_set_iff_inv_smul_mem, inv_inv, hb, ha, and_self]
  have hd' : Measure.dirac x {x} ≤ Measure.dirac x ((b⁻¹ • D) ∩ (a⁻¹ • D)) :=
    measure_mono (singleton_subset_iff.mpr hx)
  rw [Measure.dirac_apply_of_mem (mem_singleton x), hd] at hd'
  exact (not_le_of_gt zero_lt_one) hd'

/-- Normalize the ambient norm-one Levi Haar independently of the integrand. The actual
parabolic rational quotient then has the radical-first weighted measure through the two
strict principal transversals and compact Haar probability. -/
theorem exists_normOneParabolicQuotientIwasawaMeasure
    (hK : IsIwasawaCompact p K) (dn : Measure N) [dn.IsHaarMeasure] :
    ∃ dm : Measure L, dm.IsHaarMeasure ∧
      haarQuotientMeasure ΓG (isDiscrete_parabolicRationalNormOneSubgroup p) =
        Measure.map (normOneParabolicQuotientCoordinates p iU l hU hK.isCompact)
          (((dn.restrict (fundamentalDomain ΓN
              (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G (SubgroupFunctor.range (iU ≫ p))))).prod
            ((dm.withDensity (normOneParabolicDensity p iU l hU)).restrict
              (fundamentalDomain ΓM (isDiscrete_relativeLeviRationalSubgroup (l ≫ p))))).prod
            (compactHaarProbability F G K hK.isCompact)) := by
  let E := normOneParabolicCoordinates p iU l hU
  let e := normOneParabolicImageEquiv p
  let incl := (Q).subtype.comp e.toMonoidHom
  let kIncl := compactToNormOne K hK.isCompact
  let dk := compactHaarProbability F G K hK.isCompact
  let : LocallyCompactSpace N :=
    (AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iU ≫ p)).locallyCompactSpace
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  let : SecondCountableTopology K := inferInstanceAs
    (SecondCountableTopology (K : Set (AdelicGroupPoints F G)))
  obtain ⟨dq, hqHaar, hq⟩ := exists_ambientNormOneIwasawaMeasure p hK
  let dp := dq.map e.symm
  let : dp.IsHaarMeasure := e.symm.isHaarMeasure_map dq
  have he : MeasurePreserving e dp dq :=
    MeasurePreserving.symm e.symm.toHomeomorph.toMeasurableEquiv
      ⟨e.symm.toHomeomorph.continuous.measurable, rfl⟩
  have hIncl : Measurable incl := continuous_subtype_val.measurable.comp he.measurable
  have hKIncl : Measurable kIncl := by
    exact (continuous_subtype_val.subtype_mk _ :
      Continuous (fun k : K => (⟨k.val, (kIncl k).property⟩ : G₁))).measurable
  have hpush : Measure.map (fun x : H × K => incl x.1 * kIncl x.2) (dp.prod dk) =
      (Measure.haar : Measure G₁) := by
    let mult : Q × K → G₁ := fun x => x.1.val * kIncl x.2
    have hm : Measurable mult := (continuous_subtype_val.measurable.comp measurable_fst).mul
      (hKIncl.comp measurable_snd)
    have hp := he.prod (MeasurePreserving.id dk)
    change Measure.map (mult ∘ Prod.map e id) (dp.prod dk) = _
    rw [← Measure.map_map hm hp.measurable, hp.map_eq]
    exact hq
  obtain ⟨dm, hmHaar, hm⟩ := exists_normOneParabolicHaarProduct p iU l hU dn dp
  refine ⟨dm, hmHaar, ?_⟩
  let dM := dm.withDensity (normOneParabolicDensity p iU l hU)
  let hN := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G (SubgroupFunctor.range (iU ≫ p))
  let Dn := fundamentalDomain ΓN hN
  let Dm := fundamentalDomain ΓM (isDiscrete_relativeLeviRationalSubgroup (l ≫ p))
  let D := E '' (Dn ×ˢ Dm)
  have hD : MeasurableSet D := E.toMeasurableEquiv.measurableEmbedding.measurableSet_image'
    ((measurableSet_fundamentalDomain _ _).prod (measurableSet_fundamentalDomain _ _))
  have huniq (x : H) : ∃! g' : ΓP, g'.val * x ∈ D :=
    existsUnique_smul_mem_of_fundamentalDomain_all_measures
      (normOneParabolicFundamentalDomain p iU l hU) x
  have hu := LeftCosetSpace.discreteQuotientMeasure_map_mul_prod incl
    (Subtype.val_injective.comp e.injective) hIncl kIncl hKIncl ΓP ΓG
    (isDiscrete_parabolicRationalNormOneSubgroup p) Measure.haar dp dk
    (map_relativeParabolicPrincipal p) hpush hD huniq
  have hres : dp.restrict D = Measure.map E ((dn.restrict Dn).prod (dM.restrict Dm)) := by
    rw [← hm.map_eq]
    change (Measure.map E (dn.prod dM)).restrict D = _
    rw [Measure.restrict_map E.continuous.measurable hD, show E ⁻¹' D = Dn ×ˢ Dm
      from E.preimage_image _, ← Measure.prod_restrict]
  let f : H × K → LeftCosetSpace ΓG := fun x => mk ΓG (incl x.1 * kIncl x.2)
  have hf : Measurable f := (LeftCosetSpace.measurable_mk _).comp
    ((hIncl.comp measurable_fst).mul (hKIncl.comp measurable_snd))
  change haarQuotientMeasure ΓG _ = Measure.map f ((dp.restrict D).prod dk) at hu
  have hmap := Measure.map_prod_map ((dn.restrict Dn).prod (dM.restrict Dm)) dk
    E.continuous.measurable (measurable_id (α := K))
  rw [Measure.map_id] at hmap
  rw [hres, hmap, Measure.map_map hf (E.continuous.measurable.prodMap measurable_id)] at hu
  exact hu

end Langlands.Global.AdelicGroupPoints.ParabolicIwasawaMeasure
