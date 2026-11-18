import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardGlobalForm

/-! # Actual standard specialization of semistandard source constructions -/

noncomputable section

set_option maxHeartbeats 600000
set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.Aubert.General
open Langlands.Plancherel.DynamicOppositeStandardIntertwining
open Langlands.Plancherel.DynamicOppositeCanonicalScalar

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.SourceModelComparison

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean

attribute [local instance]
  SourceMeasure.modelAffineHom SourceMeasure.modelAffine SourceMeasure.modelSmooth
  SourceMeasure.modelFiniteType SourceMeasure.modelTopology SourceMeasure.modelNonarchimedean

attribute [local instance]
  SourceMeasure.intrinsicQuotientMeasurable SourceMeasure.intrinsicQuotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}
  {p : SemistandardSpectralIndex i} (hG : IsConnectedReductive G) (m n : LeviModel p)
  (r : CocharacterPresentation hG p) (d : CompactData p)

variable (hsm : ModelSmoothComparisonStatement.{u, uV} (F := F) (G := G) (i := i))
  (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))

/-- Restrict the existing actual model reindexing, conditional on its named smoothness target. -/
def smoothModelChange : smoothOrbitSections m d pi ≃ₗ[ℂ] smoothOrbitSections n d pi where
  toFun v := ⟨m.orbitSectionsModelEquiv n pi v.val,
    (hsm p m n d d pi v.val).mpr v.property⟩
  invFun w := ⟨(m.orbitSectionsModelEquiv n pi).symm w.val,
    (hsm p m n d d pi ((m.orbitSectionsModelEquiv n pi).symm w.val)).mp
      (by simpa only [LinearEquiv.apply_symm_apply] using w.property)⟩
  left_inv v := Subtype.ext ((m.orbitSectionsModelEquiv n pi).symm_apply_apply v.val)
  right_inv w := Subtype.ext ((m.orbitSectionsModelEquiv n pi).apply_symm_apply w.val)
  map_add' v w := Subtype.ext ((m.orbitSectionsModelEquiv n pi).map_add v.val w.val)
  map_smul' c v := Subtype.ext ((m.orbitSectionsModelEquiv n pi).map_smul c v.val)

@[simp] theorem smoothModelChange_val (v : smoothOrbitSections m d pi) :
    (smoothModelChange m n d hsm pi v).val = m.orbitSectionsModelEquiv n pi v.val := rfl

/-- Model comparison changes neither the continuous unitary characters nor their values. -/
def unitaryModelHomeomorph : unitaryUnramifiedCharacters m.normCharacters ≃ₜ*
    unitaryUnramifiedCharacters n.normCharacters where
  toMulEquiv := m.unitaryCharactersEquiv n
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

@[simp] theorem unitaryModelHomeomorph_val (z : unitaryUnramifiedCharacters m.normCharacters) :
    (unitaryModelHomeomorph m n z).val = z.val := rfl

variable {A B : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffine A.X.left] [IsAffine B.X.left]
  (a : A.toGrp ⟶ m.scheme) (ha : IsSplitComponent a)
  (b : B.toGrp ⟶ n.scheme) (hb : IsSplitComponent b)
  [(m.splitCenter a).Normal] [(n.splitCenter b).Normal]
  [(rationalPoints.map a).range.Normal] [(rationalPoints.map b).range.Normal]
  (hc : m.splitCenter a = n.splitCenter b)
  [MeasurableSpace (levi p ⧸ m.splitCenter a)] [BorelSpace (levi p ⧸ m.splitCenter a)]
  [MeasurableSpace (levi p ⧸ n.splitCenter b)] [BorelSpace (levi p ⧸ n.splitCenter b)]
  (mu : Measure (levi p ⧸ m.splitCenter a)) [mu.IsHaarMeasure] [mu.IsInvInvariant]

/-- The actual split-center quotient comparison fixes every literal Levi point. -/
def quotientModelHomeomorph (hc0 : m.splitCenter a = n.splitCenter b) : (levi p ⧸ m.splitCenter a) ≃ₜ* (levi p ⧸ n.splitCenter b) :=
  quotientContinuousMulEquiv (ContinuousMulEquiv.refl (levi p))
    (n.splitCenter b) (m.splitCenter a) (by
      change (m.splitCenter a).map (MonoidHom.id (levi p)) = n.splitCenter b
      simpa only [Subgroup.map_id] using hc0)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]
  [IsAffine A.X.left] [IsAffine B.X.left]
  [(rationalPoints.map a).range.Normal] [(rationalPoints.map b).range.Normal]
  [MeasurableSpace (levi p ⧸ m.splitCenter a)] [BorelSpace (levi p ⧸ m.splitCenter a)]
  [MeasurableSpace (levi p ⧸ n.splitCenter b)] [BorelSpace (levi p ⧸ n.splitCenter b)] in
@[simp] theorem quotientModelHomeomorph_mk (x : levi p) :
    quotientModelHomeomorph m n a b hc (QuotientGroup.mk x) = QuotientGroup.mk x := rfl

/-- The second quotient Haar is prescribed by this actual point-identity comparison. -/
def quotientModelHaar : Measure (levi p ⧸ n.splitCenter b) :=
  Measure.map (quotientModelHomeomorph m n a b hc) mu

instance isHaarMeasure_quotientModelHaar : (quotientModelHaar m n a b hc mu).IsHaarMeasure :=
  (quotientModelHomeomorph m n a b hc).isHaarMeasure_map mu

instance isInvInvariant_quotientModelHaar : (quotientModelHaar m n a b hc mu).IsInvInvariant := by
  let e := quotientModelHomeomorph m n a b hc
  constructor
  change Measure.map Inv.inv (Measure.map e mu) = Measure.map e mu
  have he : Measurable (fun x => e x) := e.continuous.measurable
  have hcomp : Inv.inv ∘ (fun x => e x) = (fun x => e x) ∘ Inv.inv := by
    funext x
    exact (map_inv e x).symm
  calc
    _ = Measure.map (Inv.inv ∘ (fun x => e x)) mu := Measure.map_map measurable_inv he
    _ = Measure.map ((fun x => e x) ∘ Inv.inv) mu := congrArg (fun f => Measure.map f mu) hcomp
    _ = Measure.map (fun x => e x) (Measure.map Inv.inv mu) :=
      (Measure.map_map he measurable_inv).symm
    _ = _ := congrArg (fun v => Measure.map (fun x => e x) v) (Measure.map_inv_eq_self mu)

omit [IsAffine A.X.left] [IsAffine B.X.left]
  [(rationalPoints.map a).range.Normal] [(rationalPoints.map b).range.Normal] [mu.IsInvInvariant] in
/-- Square integrability transfers to precisely the prescribed quotient-Haar pushforward. -/
theorem squareIntegrable_modelHaar
    (hsq : IsSquareIntegrableModCentralSubgroup (m.splitCenter a)
      (m.splitCenter_le_center a ha) pi.obj.representation mu) :
    IsSquareIntegrableModCentralSubgroup (n.splitCenter b)
      (n.splitCenter_le_center b hb) pi.obj.representation (quotientModelHaar m n a b hc mu) := by
  have h := isSquareIntegrableModCentralSubgroup_comp_iff (ContinuousMulEquiv.refl (levi p))
    (n.splitCenter b) (n.splitCenter_le_center b hb)
    (m.splitCenter a) (m.splitCenter_le_center a ha) (by
      change (m.splitCenter a).map (MonoidHom.id (levi p)) = n.splitCenter b
      simpa only [Subgroup.map_id] using hc)
    (quotientModelHaar m n a b hc mu) mu rfl pi.obj.representation
  apply h.mp
  convert hsq using 1
  apply MonoidHom.ext
  intro x
  rfl

variable (hindexA : (RenardCartan.splitValuationImage a).FiniteIndex)
  (hindexB : (RenardCartan.splitValuationImage b).FiniteIndex)
  (hsq : IsSquareIntegrableModCentralSubgroup (m.splitCenter a)
    (m.splitCenter_le_center a ha) pi.obj.representation mu)
  (q : OrbitPacketData r pi)

set_option hygiene false in
local notation "muN" => quotientModelHaar m n a b hc mu
set_option hygiene false in
local notation "hsqN" => squareIntegrable_modelHaar m n pi a ha b hb hc mu hsq

omit [IsAffine A.X.left] [IsAffine B.X.left]
  [(rationalPoints.map a).range.Normal] [(rationalPoints.map b).range.Normal] [mu.IsInvInvariant] in
/-- Model reindexing preserves the actual normalized coefficient at every inducing object. -/
theorem coefficient_model (v : smoothOrbitSections m d pi)
    (D : UnitaryOrbitRepresentative m.normCharacters pi) :
    SourcePacket.coefficientMap hG n r d pi (n.splitCenter b) (n.splitCenter_le_center b hb)
      muN hsqN (smoothModelChange m n d hsm pi v)
        (unitaryOrbitRepresentativeDiscreteSeriesOrbit n.normCharacters pi (n.splitCenter b)
          (n.splitCenter_le_center b hb) muN hsqN (m.representativeModelEquiv n pi D)) =
    SourcePacket.coefficientMap hG m r d pi (m.splitCenter a) (m.splitCenter_le_center a ha)
      mu hsq v (unitaryOrbitRepresentativeDiscreteSeriesOrbit m.normCharacters pi (m.splitCenter a)
        (m.splitCenter_le_center a ha) mu hsq D) := by
  have hn := SourcePacket.coefficientMap_representative hG n r d pi (n.splitCenter b)
    (n.splitCenter_le_center b hb) muN hsqN (smoothModelChange m n d hsm pi v)
    (m.representativeModelEquiv n pi D)
  have hm := SourcePacket.coefficientMap_representative hG m r d pi (m.splitCenter a)
    (m.splitCenter_le_center a ha) mu hsq v D
  exact hn.trans hm.symm

/-- Exact remaining model-independence of the prescribed source Haar and integrals.
The quotient Haar, characters and smooth section map are actual constructions above. -/
def ModelSourceComparisonStatement : Prop :=
  Measure.map (unitaryModelHomeomorph m n)
      (SourceMeasure.unitaryCharacterHaar m a ha hindexA) =
    SourceMeasure.unitaryCharacterHaar n b hb hindexB ∧
  (IsMaximalSplitTorus i →
    ∀ (nu : cocharacterLattice S), IsGenericCocharacter i nu →
      ∀ (K0 : OpenSubgroup (rationalPoints G)) (_hK0 : IsCompact (K0 : Set (rationalPoints G))),
        BruhatTits.SpecialCompact.SpecialCompactProperties F i nu
          (K0 : Subgroup (rationalPoints G)) → d.compact = K0 → q.compact = K0 →
        ∀ (v w : smoothOrbitSections m d pi),
          q.packetLinear n d b hb hindexB muN hsqN (smoothModelChange m n d hsm pi v) =
            q.packetLinear m d a ha hindexA mu hsq v ∧
          SourceForm.weightedOrbitForm hG n r d b hb hindexB muN pi hsqN q
              (smoothModelChange m n d hsm pi v) (smoothModelChange m n d hsm pi w) =
            SourceForm.weightedOrbitForm hG m r d a ha hindexA mu pi hsq q v w)

end Langlands.HarishChandraSchwartz.RationalSemistandard.SourceModelComparison
