import Langlands.BruhatTits.IntegralModels.IntegralOppositeNecessity
import Langlands.BruhatTits.IntegralModels.IntegralTorusGenericRoots
import Langlands.BruhatTits.IntegralModels.CommonTorusQuotientMaximality
import Langlands.BruhatTits.IntegralModels.ReductiveQuotientExistence
import Langlands.GroupScheme.IntegralModel.KernelCentralizerOppositeSufficiency
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # Opposite factors over a Henselian discrete valuation ring -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels.IntegralTorusData

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [PerfectField (IsLocalRing.ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    {D : RelativeComponentModelData R K G}
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    (T : IntegralTorusData D S i)

/-- Nonradical reduction makes both prescribed opposite factors integral.
Closedness of the split integral torus follows from its maximal generic fibre. -/
theorem integral_oppositeFactors_of_not_mem_positivePoints
    (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints i a) (hg1 : g ≠ 1)
    (hgR : g ∈ D.neutral.integralPoints)
    {p : rationalPoints G × rationalPoints G}
    (hp : RelativeRoot.IsOppositeFactorPair i a g p)
    (hnon : g ∉ Q.positivePoints) :
    p.1 ∈ D.neutral.integralPoints ∧ p.2 ∈ D.neutral.integralPoints := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : Smooth D.neutral.group.X.hom := D.neutral_smooth
  have hiK := T.genericHom_isMaximalSplitTorus hi
  let : IsClosedImmersion (D.neutral.genericHom T.inclusion).hom.hom.left := hiK.1.2
  let : Mono (D.neutral.genericHom T.inclusion).hom.hom.left := inferInstance
  have hj : IsClosedSubgroup T.inclusion :=
    D.neutral.isClosedSubgroup_of_split_generic T.torus hT T.inclusion hiK.1.2
  have hiRaw : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T.torus)
      ((baseChange (Spec.algebraMap R K)).map T.inclusion) :=
    (IsMaximalSplitTorus.comp_iso_iff _ D.neutral.genericIso).mp hiK
  have hiRes : IsMaximalSplitTorus T.specialFibreInclusion := by
    have hr := isMaximalSplitTorus_residue_of_generic
      (IsLocalRing.residue_surjective : Function.Surjective
        (algebraMap R (IsLocalRing.ResidueField R)))
      D.neutral.group (hG.of_iso D.neutral.genericIso) T.torus hT T.inclusion hj hiRaw
    simpa only [IntegralTorusData.specialFibreInclusion, IntegralModel.residueBaseMap,
      IntegralTorusData.specialFibre, IntegralModel.specialFibre, Spec.algebraMap,
      IsLocalRing.ResidueField.algebraMap_eq] using hr
  have hiQ : IsMaximalSplitTorus (T.specialFibreInclusion ≫ Q.projection) := by
    let : Smooth Q.radical.X.hom := hQ.1.smooth
    let : ConnectedSpace Q.radical.X.left := hQ.1.connectedSpace
    let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
    let : IsAffineHom D.neutral.specialFibre.X.hom := by
      change IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
        (IntegralModel.residueBaseMap R))
      infer_instance
    let : LocallyOfFiniteType D.neutral.specialFibre.X.hom := by
      change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
        (IntegralModel.residueBaseMap R))
      infer_instance
    exact (IsMaximalSplitTorus.comp_iff_of_perfect_field_unipotent_kernel
      Q.radicalInclusion hQ.1.isClosedSubgroup hQ.1.isUnipotent
      Q.projection hQ.2.1 T.specialFibreInclusion).mpr hiRes
  obtain ⟨x, hx⟩ := (D.neutral.mem_integralPoints g).mp hgR
  have hqx : rationalPoints.map Q.projection (D.neutral.reduction x) ≠ 1 := by
    intro hz
    apply hnon
    apply (Q.mem_positivePoints g).mpr
    refine ⟨x, ?_, hx⟩
    have hr := (mem_range_kernelι_iff Q.projection (D.neutral.reduction x)).mpr hz
    rw [hQ.2.1.2.2.2] at hr
    exact hr
  let χ := (T.genericCharacterEquiv hT).symm a
  have hχa : T.genericCharacter χ = a :=
    (T.genericCharacterEquiv hT).apply_symm_apply a
  have haK : characterLattice.baseChange (Spec.algebraMap R K) T.torus χ ∈
      relativeRoots (D.neutral.genericHom T.inclusion) :=
    (T.generic_mem_relativeRoots_iff χ).mpr (by rwa [hχa])
  have hxroot : D.neutral.integralPointMap x ∈
      (RelativeRoot.subgroup (D.neutral.genericHom T.inclusion)
        (characterLattice.baseChange (Spec.algebraMap R K) T.torus χ)).carrier
          (Over.mk (𝟙 _)) := by
    rw [T.generic_subgroup_eq χ, hχa, hx]
    exact hg
  have hpK : RelativeRoot.IsOppositeFactorPair (D.neutral.genericHom T.inclusion)
      (characterLattice.baseChange (Spec.algebraMap R K) T.torus χ)
      (D.neutral.integralPointMap x) p :=
    (T.generic_isOppositeFactorPair_iff χ _ _).mp (by
      rwa [hχa, hx])
  obtain ⟨ν, -, hpos⟩ := RelativeRoot.exists_genericCocharacter_pairing_pos i hi.1.1 ha.1
  obtain ⟨νR, -, hνRpair⟩ := T.exists_integralCocharacter_compatible hT ν
  have hposR : 0 < latticePairing T.torus χ νR := by
    have hpair := hνRpair a
    rw [← hχa, T.characterSpecialization_genericCharacter hT χ] at hpair
    rw [hχa] at hpair
    change latticePairing T.specialFibre
      (characterLattice.baseChange (IntegralModel.residueBaseMap R) T.torus χ)
      (cocharacterLattice.baseChange (IntegralModel.residueBaseMap R) T.torus νR) =
        latticePairing S a ν at hpair
    rw [latticePairing_baseChange] at hpair
    rwa [hpair]
  exact D.neutral.integral_oppositeFactors_of_residueQuotient
    T.inclusion hT χ νR hposR Q.projection hQ.2.2
    (Q.projection_smooth hQ) (SpecialFibreQuotientData.hasSmoothConnectedUnipotentKernel hQ)
    hiQ (relativeRootSystem K G hG _ _ hiK) haK x hxroot (by rwa [hx]) hqx p hpK

end Langlands.BruhatTits.IntegralModels.IntegralTorusData

namespace Langlands.BruhatTits.IntegralModels

/-- The general-base sufficiency assertion for integral opposite factors:
nonradical reduction forces every prescribed opposite pair to be integral. -/
def HenselianIntegralOppositeFactorsStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [PerfectField (IsLocalRing.ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    (D : RelativeComponentModelData R K G)
    (S : CommGroupScheme (Spec (CommRingCat.of K))) (i : S.toGrp ⟶ G)
    (T : IntegralTorusData D S i),
    IsSplitTorus T.torus.toGrp →
    ∀ (Q : SpecialFibreQuotientData D), Q.IsReductiveQuotient →
      IsConnectedReductive G → IsMaximalSplitTorus i →
      ∀ (a : characterLattice S), a ∈ relativeRoots i →
        ∀ (g : rationalPoints G), g ∈ rootGroupPoints i a → g ≠ 1 →
          g ∈ D.neutral.integralPoints →
          ∀ (p : rationalPoints G × rationalPoints G),
            RelativeRoot.IsOppositeFactorPair i a g p →
            g ∉ Q.positivePoints →
            p.1 ∈ D.neutral.integralPoints ∧ p.2 ∈ D.neutral.integralPoints

/-- Split-generic closedness and the Henselian quotient theorem establish
the general-base opposite-factor sufficiency assertion. -/
theorem henselianIntegralOppositeFactors :
    HenselianIntegralOppositeFactorsStatement.{u} := by
  intro R K _ _ _ _ _ _ _ _ G _ D S i T hT Q hQ hG hi a ha g hg hg1 hgR p hp hnon
  exact T.integral_oppositeFactors_of_not_mem_positivePoints
    hT Q hQ hG hi ha hg hg1 hgR hp hnon

end Langlands.BruhatTits.IntegralModels
