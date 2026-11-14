import Langlands.BruhatTits.IntegralModels.IntegralOppositeFactorsStatement
import Langlands.BruhatTits.IntegralModels.IntegralRootReduction
import Langlands.BruhatTits.IntegralModels.IntegralCocharacterLift
import Langlands.BruhatTits.IntegralModels.ReductiveQuotientRoots
import Langlands.BruhatTits.IntegralModels.QuotientGenericOppositeCell
import Langlands.GroupScheme.IntegralModel.UnipotentQuotientCell
import Langlands.GroupScheme.IntegralModel.ConnectedFibreDescent
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Rational.RootFactorPairExistenceReduction
import Langlands.GroupScheme.Rational.RootFactorPairConsequences
import Langlands.GroupScheme.Rational.RootSubgroupSeparation
import Langlands.GroupScheme.Rational.RelativeReflectionProperties
import Langlands.GroupScheme.IntegralModel.GenericOppositeCell

/-! # Integral opposite factors exclude radical reduction -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels


namespace IntegralTorusData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {D : RelativeComponentModelData R K G}
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    (T : IntegralTorusData D S i) (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient)

include T hT hQ in
/-- Integral opposite factors of a nonidentity root point force its reduction
outside the supplied unipotent radical. -/
theorem not_mem_positivePoints_of_integral_oppositeFactors
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {a : characterLattice S} (ha : a ≠ 0)
    {g : rationalPoints G}
    (hg : g ∈ rootGroupPoints i a) (hg1 : g ≠ 1)
    {g' g'' : rationalPoints G}
    (hg' : g' ∈ rootGroupPoints i (-a))
    (hg'' : g'' ∈ rootGroupPoints i (-a))
    (hn : g' * g * g'' ∈ normalizerPoints i)
    (hg'R : g' ∈ D.neutral.integralPoints)
    (hg''R : g'' ∈ D.neutral.integralPoints) :
    g ∉ Q.positivePoints := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsClosedImmersion i.hom.hom.left := hi.1.2
  let : Mono i.hom.hom.left := inferInstance
  intro hgpos
  obtain ⟨x, hx, hxg⟩ := (Q.mem_positivePoints g).mp hgpos
  obtain ⟨x', hx'g⟩ := (D.neutral.mem_integralPoints g').mp hg'R
  obtain ⟨x'', hx''g⟩ := (D.neutral.mem_integralPoints g'').mp hg''R
  obtain ⟨ν, hν, hpos⟩ :=
    RelativeRoot.exists_genericCocharacter_pairing_pos i hi.1.1 ha
  obtain ⟨νR, hνRK, hνRpair⟩ := T.exists_integralCocharacter_compatible hT ν
  let νs := cocharacterLattice.baseChange (IntegralModel.residueBaseMap R) T.torus νR
  let χ := CommGroupScheme.groupHom νR ≫ T.inclusion
  let iQ := T.specialFibreInclusion ≫ Q.projection
  have hχs : Dynamic.baseChangeCocharacter (IntegralModel.residueBaseMap R) χ ≫
      Q.projection = CommGroupScheme.groupHom νs ≫ iQ := by
    change ((Gm.baseChangeIso _).inv ≫
      (GroupScheme.baseChange _).map (CommGroupScheme.groupHom νR ≫ T.inclusion)) ≫
        Q.projection = _
    rw [Functor.map_comp, Category.assoc]
    rfl
  have hposS : 0 < latticePairing T.specialFibre
      (T.characterSpecialization hT (-a)) (-νs) := by
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
    rw [hνRpair]
    exact hpos
  have hxq : rationalPoints.map Q.projection (D.neutral.reduction x) = 1 := by
    apply (mem_range_kernelι_iff Q.projection (D.neutral.reduction x)).mp
    rw [hQ.2.1.2.2.2]
    exact hx
  have hneg (y : D.neutral.integralSections)
      (hy : D.neutral.integralPointMap y ∈ rootGroupPoints i (-a)) :
      rationalPoints.map Q.projection (D.neutral.reduction y) ∈
        (Dynamic.unipotent (Dynamic.oppositeCocharacter
          (Dynamic.baseChangeCocharacter (IntegralModel.residueBaseMap R) χ ≫
            Q.projection))).carrier (Over.mk (𝟙 _)) := by
    rw [hχs, ← groupHom_neg_comp_eq_oppositeCocharacter]
    exact RelativeRoot.subgroup_le_dynamicUnipotent iQ (-νs) hposS _
      (T.quotient_reduction_mem_rootFunctor hT Q (-a) (neg_ne_zero.mpr ha) y hy)
  have hx'q := hneg x' (by rwa [hx'g])
  have hx''q := hneg x'' (by rwa [hx''g])
  have hnq : rationalPoints.map Q.projection (D.neutral.reduction (x' * x * x'')) ∈
      (Dynamic.unipotent (Dynamic.oppositeCocharacter
        (Dynamic.baseChangeCocharacter (IntegralModel.residueBaseMap R) χ ≫
          Q.projection))).carrier (Over.mk (𝟙 _)) := by
    simp only [map_mul, hxq, mul_one]
    exact Subgroup.mul_mem _ hx'q hx''q
  obtain ⟨v, hv, w, hw, he⟩ :=
    Q.generic_oppositeCell_of_quotient_unipotent hQ χ (x' * x * x'') hnq
  have hgen : Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ ≫
      D.neutral.genericIso.hom = CommGroupScheme.groupHom ν ≫ i := hνRK
  rw [hgen] at hv hw
  have he' : g' * g * g'' = v * w := by
    simpa only [map_mul, hx'g, hxg, hx''g] using he
  let n : normalizerPoints i := ⟨g' * g * g'', hn⟩
  have hnc : n.val ∈ centralizerPoints i :=
    normalizer_mem_centralizer_of_generic_oppositeCell i ν
      (genericCentralizer K G hG S i hi ν hν) n hv hw he'
  have hn1 : weylAction i n = 1 := (hi.1.1.weylAction_eq_one_iff i n).mpr hnc
  have hp : RelativeRoot.IsOppositeFactorPair i a g (g', g'') := ⟨hg', hg'', hn⟩
  have hflip : weylAction i n a = -a := hp.weylAction_eq_neg i hi.1.1 ha hg hg1
  rw [hn1] at hflip
  have hpair := congrArg (fun b => latticePairing S b ν) hflip
  change latticePairing S a ν = latticePairing S (-a) ν at hpair
  simp only [map_neg, LinearMap.neg_apply] at hpair
  omega

end IntegralTorusData

/-- Over a local domain with specified fraction field, integral normalizing
opposite factors force a nonidentity generic root point outside the actual
radical preimage of a supplied reductive quotient. -/
def IntegralOppositeNecessityStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    (G : GroupScheme (Spec (CommRingCat.of K))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of K))) (i : S.toGrp ⟶ G)
    (_hi : IsMaximalSplitTorus i)
    (D : RelativeComponentModelData R K G) (T : IntegralTorusData D S i)
    (_hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData D) (_hQ : Q.IsReductiveQuotient),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ a : characterLattice S, a ≠ 0 →
      ∀ g : rationalPoints G, g ∈ rootGroupPoints i a → g ≠ 1 →
        ∀ g' g'' : rationalPoints G,
          g' ∈ rootGroupPoints i (-a) → g'' ∈ rootGroupPoints i (-a) →
          g' * g * g'' ∈ normalizerPoints i →
          g' ∈ D.neutral.integralPoints → g'' ∈ D.neutral.integralPoints →
          g ∉ Q.positivePoints

/-- Necessity of nonradical reduction for integral opposite factors. -/
theorem integralOppositeNecessity : IntegralOppositeNecessityStatement.{u} := by
  intro R K _ _ _ _ _ _ G hG S i hi D T hT Q hQ
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro a ha g hg hg1 g' g'' hg' hg'' hn hg'R hg''R
  exact T.not_mem_positivePoints_of_integral_oppositeFactors hT Q hQ hG hi
    ha hg hg1 hg' hg'' hn hg'R hg''R

end Langlands.BruhatTits.IntegralModels
