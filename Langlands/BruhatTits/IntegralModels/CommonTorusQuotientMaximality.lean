import Langlands.BruhatTits.IntegralModels.CommonTorusMaximality
import Langlands.GroupScheme.Torus.UnipotentQuotientMaximalSplit
import Langlands.BruhatTits.IntegralModels.DepthZeroInduction
import Langlands.Geometry.Building.KPParahoric

/-! # Common maximal split tori through a reductive special-fibre quotient -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.BruhatTits.IntegralModels

open Langlands.GroupScheme Langlands.Geometry.Building

/-- Passing to a reductive special-fibre quotient preserves maximality of the
same supplied torus over a perfect residue field. -/
theorem RelativeComponentModelHom.isMaximalSplitTorus_quotientTorusInclusion
    {R K : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [PerfectField (IsLocalRing.ResidueField R)]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {source target : RelativeComponentModelData R K G}
    (φ : RelativeComponentModelHom source target)
    (Q : SpecialFibreQuotientData target) (hQ : Q.IsReductiveQuotient)
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    (T : IntegralTorusData source S i)
    (hi : IsMaximalSplitTorus (φ.targetTorusInclusion T)) :
    IsMaximalSplitTorus (φ.quotientTorusInclusion Q T) := by
  let : Smooth Q.radical.X.hom := hQ.1.smooth
  let : ConnectedSpace Q.radical.X.left := hQ.1.connectedSpace
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  let : IsAffineHom target.neutral.specialFibre.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd target.neutral.group.X.hom
      (IntegralModel.residueBaseMap R))
    infer_instance
  let : LocallyOfFiniteType target.neutral.specialFibre.X.hom := by
    change LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.snd target.neutral.group.X.hom
        (IntegralModel.residueBaseMap R))
    infer_instance
  exact (IsMaximalSplitTorus.comp_iff_of_perfect_field_unipotent_kernel
    Q.radicalInclusion hQ.1.isClosedSubgroup hQ.1.isUnipotent
    Q.projection hQ.2.1 (φ.targetTorusInclusion T)).mpr hi

/-- Common maximal split tori over a noetherian Henselian domain with perfect
residue field, for compatible model morphisms and reductive quotients. -/
def CommonTorusMaximalityStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [HenselianLocalRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [PerfectField (IsLocalRing.ResidueField R)]
    (G : GroupScheme (Spec (CommRingCat.of K))),
    IsConnectedReductive G →
    ∀ (source target : RelativeComponentModelData R K G)
      (φ : RelativeComponentModelHom source target)
      (Q : SpecialFibreQuotientData target)
      (S : CommGroupScheme (Spec (CommRingCat.of K))) (i : S.toGrp ⟶ G)
      (T : IntegralTorusData source S i),
      IsMaximalSplitTorus i → Q.IsReductiveQuotient → T.SatisfiesTorusClause →
        φ.HasMaximalSplitTori Q T

/-- Generic maximality and the source torus clause imply the common-torus
maximality assertions in the target special fibre and its reductive quotient. -/
theorem commonTorusMaximality : CommonTorusMaximalityStatement.{u} := by
  intro R K _ _ _ _ _ _ _ _ G hG source target φ Q S i T hi hQ hT
  have ht := φ.isMaximalSplitTorus_targetTorusInclusion hG T hT.1.1 hi
  exact ⟨hT.2, ht, φ.isMaximalSplitTorus_quotientTorusInclusion Q hQ T ht⟩

/-- The maximality clauses for the common torus in the local-field facet
setting; no apartment incidence or model-fixer characterization is needed. -/
theorem RelativeComponentModelHom.hasMaximalSplitTori_integer
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (g : rationalPoints G)
    {source target : RelativeComponentModelData ↥𝒪[F] F G}
    (φ : RelativeComponentModelHom source target)
    (Q : SpecialFibreQuotientData target)
    (T : IntegralTorusData source P.toValuationBuildingData.S
      (P.toValuationBuildingData.i ≫ (G.innerIso g).hom))
    (hQ : Q.IsReductiveQuotient) (hT : T.SatisfiesTorusClause) :
    φ.HasMaximalSplitTori Q T := by
  let : HenselianLocalRing ↥𝒪[F] := henselianLocalRing_integer
  exact commonTorusMaximality ↥𝒪[F] F G P.isConnectedReductive source target φ Q
    P.S (P.i ≫ (G.innerIso g).hom) T
    (P.isMaximalSplitTorus.comp_iso (G.innerIso g)) hQ hT

end Langlands.BruhatTits.IntegralModels
