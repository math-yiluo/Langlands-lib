import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedCoefficients
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.Representation.Plancherel.SplitTorusCompactKernel

/-! # The full standard Levi scheme and its actual norm kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

section Scheme

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  [Fintype (RationalPointFamily.SimpleRoot i ν)]
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

include hG hi hν in
/-- The full-index standard Levi functor is the full functor on every test
scheme, rather than only on rational points. -/
theorem rationalFullLeviFunctor_eq_top :
    standardLevi i ν (RationalPointFamily.rootSet i ν Finset.univ) = ⊤ := by
  rw [RationalPointFamily.rootSet_univ]
  exact (standardParabolicEndpoints F G hG S i hi ν hν).2.2.2.1

/-- The chosen representative of the full standard Levi is actually
isomorphic to the ambient group scheme. -/
def rationalFullLeviSchemeIso :
    Standard.leviScheme i ν (RationalPointFamily.rootSet i ν Finset.univ) ≅ G :=
  (show (⊤ : SubgroupFunctor G).IsRepresentedBy
      (Standard.leviHom i ν (RationalPointFamily.rootSet i ν Finset.univ)) from
    rationalFullLeviFunctor_eq_top hG hi hν ▸
      Standard.isRepresentedBy_leviHom i ν (RationalPointFamily.rootSet i ν Finset.univ)).topIso

/-- The forward map of the endpoint isomorphism is the original inclusion. -/
theorem rationalFullLeviSchemeIso_hom :
    (rationalFullLeviSchemeIso hG hi hν).hom =
      Standard.leviHom i ν (RationalPointFamily.rootSet i ν Finset.univ) :=
  SubgroupFunctor.IsRepresentedBy.topIso_hom _

end Scheme

section Rational

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  [Fintype (RationalPointFamily.SimpleRoot i ν)]
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

local instance : IsClosedImmersion
    (Standard.leviHom i ν (RationalPointFamily.rootSet i ν Finset.univ)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (RationalPointFamily.rootSet i ν Finset.univ)
local instance : IsAffine
    (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν Finset.univ)).X.left :=
  isAffine_of_isAffineHom
    (Standard.leviHom i ν (RationalPointFamily.rootSet i ν Finset.univ)).hom.hom.left
local instance : TopologicalSpace (rationalPoints
    (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν Finset.univ))) :=
  rationalPointTopology F _

/-- The full-root intrinsic Levi points map homeomorphically to ambient
points by the original Levi inclusion. -/
def rationalFullLeviPointHomeomorph :
    rationalPoints (Standard.leviScheme i ν
      (RationalPointFamily.rootSet i ν Finset.univ)) ≃ₜ* rationalPoints G where
  toMulEquiv := isoPointsEquiv (rationalFullLeviSchemeIso hG hi hν) (Over.mk (𝟙 _))
  continuous_toFun :=
    continuous_rationalPointMap F (rationalFullLeviSchemeIso hG hi hν).hom.hom.hom
  continuous_invFun :=
    continuous_rationalPointMap F (rationalFullLeviSchemeIso hG hi hν).inv.hom.hom

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
theorem rationalFullLeviPointHomeomorph_apply
    (m : rationalPoints (Standard.leviScheme i ν
      (RationalPointFamily.rootSet i ν Finset.univ))) :
    rationalFullLeviPointHomeomorph hG hi hν m =
      rationalPoints.map (rationalFullLeviSchemeIso hG hi hν).hom m := rfl

/-- The actual common norm kernel is preserved by the full-Levi point
identification, retaining the norm family of each group scheme. -/
theorem mem_rationalCommonNormKernel_fullLevi_iff
    (m : rationalPoints (Standard.leviScheme i ν
      (RationalPointFamily.rootSet i ν Finset.univ))) :
    m ∈ rationalCommonNormKernel
        (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν Finset.univ)) ↔
      rationalFullLeviPointHomeomorph hG hi hν m ∈ rationalCommonNormKernel G := by
  rw [rationalFullLeviPointHomeomorph_apply]
  constructor
  · exact SplitTorus.map_mem_commonNormKernel (rationalFullLeviSchemeIso hG hi hν).hom
  · intro hm
    have h := SplitTorus.map_mem_commonNormKernel
      (rationalFullLeviSchemeIso hG hi hν).inv hm
    change (isoPointsEquiv (rationalFullLeviSchemeIso hG hi hν) _).symm
      ((isoPointsEquiv (rationalFullLeviSchemeIso hG hi hν) _) m) ∈ _ at h
    simpa only [MulEquiv.symm_apply_apply] using h

end Rational

end Langlands.HarishChandraSchwartz
