import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSubgroupSmoothTrace
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSubgroupTransitivity

/-! # Smooth coefficient transitivity for the original rational subgroup maps -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Topology
open Langlands.Sheaf.Equivariant

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}

namespace OpenSubgroupTransport

namespace SmoothSheafVariation

variable (R : Type u) [CommRing R]
  {X Y Z : ρ.OpenSubgroupTransport}
  [HasStableNeighbourhoods X.subgroup.toSubgroup X.LocalSpectrum]
  [HasStableNeighbourhoods Y.subgroup.toSubgroup Y.LocalSpectrum]
  [HasStableNeighbourhoods Z.subgroup.toSubgroup Z.LocalSpectrum]

/-- Transport the actual lax comparison along equality of the original rational arrows. -/
def directImageCompMapOfEq (f : X ⟶ Y) (g : Y ⟶ Z) (q : X ⟶ Z)
    (e : f ≫ g = q) :
    directImage R f ⋙ directImage R g ⟶ directImage R q :=
  directImageCompMap R f g ≫ eqToHom (congrArg (directImage R) e)

private theorem coefficientMap_comp_ofEq
    (f : X ⟶ Y) (g : Y ⟶ Z) (q : X ⟶ Z) (e : f ≫ g = q)
    (M : SmoothRep.{u, u, u} R G) :
    coefficientMap R q M =
      coefficientMap R g M ≫ (directImage R g).map (coefficientMap R f M) ≫
        (directImageCompMapOfEq R f g q e).app ((coefficientFunctor R X).obj M) := by
  subst q
  simpa [directImageCompMapOfEq] using coefficientMap_comp R f g M

private theorem coefficientNatTrans_comp_ofEq
    (f : X ⟶ Y) (g : Y ⟶ Z) (q : X ⟶ Z) (e : f ≫ g = q) :
    coefficientNatTrans R q =
      coefficientNatTrans R g ≫
        Functor.whiskerRight (coefficientNatTrans R f) (directImage R g) ≫
          Functor.whiskerLeft (coefficientFunctor R X)
            (directImageCompMapOfEq R f g q e) := by
  apply NatTrans.ext
  funext M
  exact coefficientMap_comp_ofEq R f g q e M

private theorem coefficientTrace_comp_ofEq
    (f : X ⟶ Y) (g : Y ⟶ Z) (q : X ⟶ Z) (e : f ≫ g = q)
    [finiteF : ∀ y, Finite (f.inducedMap ⁻¹' {y})]
    [finiteG : ∀ z, Finite (g.inducedMap ⁻¹' {z})]
    [finiteQ : ∀ z, Finite (q.inducedMap ⁻¹' {z})]
    (hf : IsCoveringMap f.inducedMap) (hg : IsCoveringMap g.inducedMap)
    (hq : IsCoveringMap q.inducedMap) (M : SmoothRep.{u, u, u} R G) :
    (directImageCompMapOfEq R f g q e).app ((coefficientFunctor R X).obj M) ≫
        coefficientTrace R q hq M =
      (directImage R g).map (coefficientTrace R f hf M) ≫
        coefficientTrace R g hg M := by
  subst q
  simpa [directImageCompMapOfEq] using coefficientTrace_comp R f g hf hg hq M

private theorem coefficientTraceNatTrans_comp_ofEq
    (f : X ⟶ Y) (g : Y ⟶ Z) (q : X ⟶ Z) (e : f ≫ g = q)
    [finiteF : ∀ y, Finite (f.inducedMap ⁻¹' {y})]
    [finiteG : ∀ z, Finite (g.inducedMap ⁻¹' {z})]
    [finiteQ : ∀ z, Finite (q.inducedMap ⁻¹' {z})]
    (hf : IsCoveringMap f.inducedMap) (hg : IsCoveringMap g.inducedMap)
    (hq : IsCoveringMap q.inducedMap) :
    Functor.whiskerLeft (coefficientFunctor R X)
        (directImageCompMapOfEq R f g q e) ≫ coefficientTraceNatTrans R q hq =
      Functor.whiskerRight (coefficientTraceNatTrans R f hf) (directImage R g) ≫
        coefficientTraceNatTrans R g hg := by
  subst q
  simpa [directImageCompMapOfEq] using coefficientTraceNatTrans_comp R f g hf hg hq

end SmoothSheafVariation

variable {U V W : OpenSubgroup G} (h : V ≤ U) (k : W ≤ V)
  (d : ρ.InvariantRationalDomain U)
  [targetStable : HasStableNeighbourhoods ((inclusion U).obj d).subgroup.toSubgroup
    ((inclusion U).obj d).LocalSpectrum]

include targetStable in
local instance middleStable :
    HasStableNeighbourhoods
      ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)).subgroup.toSubgroup
      ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)).LocalSpectrum :=
  subgroupRestriction_hasStableNeighbourhoods h d

include targetStable in
local instance innerStable :
    HasStableNeighbourhoods
      ((inclusion W).obj ((ρ.invariantRestrictionFunctor (k.trans h)).obj d)).subgroup.toSubgroup
      ((inclusion W).obj ((ρ.invariantRestrictionFunctor (k.trans h)).obj d)).LocalSpectrum :=
  subgroupRestriction_hasStableNeighbourhoods (k.trans h) d

variable (R : Type u) [CommRing R]

/-- The two successive actual smooth images map to the direct original subgroup image. -/
def subgroupRestrictionSmoothDirectImageCompMap :
    SmoothSheafVariation.directImage R
        (subgroupRestriction k ((ρ.invariantRestrictionFunctor h).obj d)) ⋙
      SmoothSheafVariation.directImage R (subgroupRestriction h d) ⟶
        SmoothSheafVariation.directImage R (subgroupRestriction (k.trans h) d) :=
  SmoothSheafVariation.directImageCompMapOfEq R
    (X := (inclusion W).obj ((ρ.invariantRestrictionFunctor (k.trans h)).obj d))
    (subgroupRestriction k ((ρ.invariantRestrictionFunctor h).obj d))
    (subgroupRestriction h d) (subgroupRestriction (k.trans h) d)
    (subgroupRestriction_comp h k d)

/-- Full original smooth pullbacks compose through the actual lax comparison. -/
theorem subgroupRestrictionSmoothCoefficientMap_comp (M : SmoothRep.{u, u, u} R G) :
    let X := (inclusion W).obj ((ρ.invariantRestrictionFunctor (k.trans h)).obj d)
    let Y := (inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)
    let Z := (inclusion U).obj d
    let f : X ⟶ Y := subgroupRestriction k ((ρ.invariantRestrictionFunctor h).obj d)
    let g : Y ⟶ Z := subgroupRestriction h d
    let q : X ⟶ Z := subgroupRestriction (k.trans h) d
    SmoothSheafVariation.coefficientMap R q M =
      SmoothSheafVariation.coefficientMap R g M ≫
        (SmoothSheafVariation.directImage R g).map
          (SmoothSheafVariation.coefficientMap R f M) ≫
        (SmoothSheafVariation.directImageCompMapOfEq R f g q
          (subgroupRestriction_comp h k d)).app
            ((SmoothSheafVariation.coefficientFunctor R X).obj M) :=
  SmoothSheafVariation.coefficientMap_comp_ofEq R
    (X := (inclusion W).obj ((ρ.invariantRestrictionFunctor (k.trans h)).obj d))
    (subgroupRestriction k ((ρ.invariantRestrictionFunctor h).obj d))
    (subgroupRestriction h d) (subgroupRestriction (k.trans h) d)
    (subgroupRestriction_comp h k d) M

/-- Smooth pullback transitivity retains every original coefficient intertwiner. -/
theorem subgroupRestrictionSmoothCoefficientNatTrans_comp :
    subgroupRestrictionSmoothCoefficientNatTrans (k.trans h) d R =
      subgroupRestrictionSmoothCoefficientNatTrans h d R ≫
        Functor.whiskerRight
          (subgroupRestrictionSmoothCoefficientNatTrans k
            ((ρ.invariantRestrictionFunctor h).obj d) R)
          (SmoothSheafVariation.directImage R (subgroupRestriction h d)) ≫
        Functor.whiskerLeft
          (SmoothSheafVariation.coefficientFunctor R
            ((inclusion W).obj ((ρ.invariantRestrictionFunctor (k.trans h)).obj d)))
          (subgroupRestrictionSmoothDirectImageCompMap h k d R) :=
  SmoothSheafVariation.coefficientNatTrans_comp_ofEq R
    (X := (inclusion W).obj ((ρ.invariantRestrictionFunctor (k.trans h)).obj d))
    (subgroupRestriction k ((ρ.invariantRestrictionFunctor h).obj d))
    (subgroupRestriction h d) (subgroupRestriction (k.trans h) d)
    (subgroupRestriction_comp h k d)

section Finite

variable [Finite (V ⧸ W.toSubgroup.subgroupOf V.toSubgroup)]
  [Finite (U ⧸ V.toSubgroup.subgroupOf U.toSubgroup)]

/-- The direct original smooth trace agrees with successive traces after the lax map. -/
theorem subgroupRestrictionSmoothCoefficientTrace_comp (M : SmoothRep.{u, u, u} R G) :
    letI : Finite (U ⧸ W.toSubgroup.subgroupOf U.toSubgroup) :=
      finite_relativeQuotient_trans U V W
    let X := (inclusion W).obj ((ρ.invariantRestrictionFunctor (k.trans h)).obj d)
    let Y := (inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)
    let Z := (inclusion U).obj d
    let f : X ⟶ Y := subgroupRestriction k ((ρ.invariantRestrictionFunctor h).obj d)
    let g : Y ⟶ Z := subgroupRestriction h d
    let q : X ⟶ Z := subgroupRestriction (k.trans h) d
    letI : ∀ y, Finite (f.inducedMap ⁻¹' {y}) :=
      finite_subgroupRestriction_inducedMap_fiber k ((ρ.invariantRestrictionFunctor h).obj d)
    letI : ∀ y, Finite (g.inducedMap ⁻¹' {y}) :=
      finite_subgroupRestriction_inducedMap_fiber h d
    letI : ∀ y, Finite (q.inducedMap ⁻¹' {y}) :=
      finite_subgroupRestriction_inducedMap_fiber (k.trans h) d
    (SmoothSheafVariation.directImageCompMapOfEq R f g q
          (subgroupRestriction_comp h k d)).app
          ((SmoothSheafVariation.coefficientFunctor R X).obj M) ≫
        SmoothSheafVariation.coefficientTrace R q
          (isCoveringMap_subgroupRestriction_inducedMap (k.trans h) d) M =
      (SmoothSheafVariation.directImage R g).map
          (SmoothSheafVariation.coefficientTrace R f
            (isCoveringMap_subgroupRestriction_inducedMap k _) M) ≫
        SmoothSheafVariation.coefficientTrace R g
          (isCoveringMap_subgroupRestriction_inducedMap h d) M := by
  let : Finite (U ⧸ W.toSubgroup.subgroupOf U.toSubgroup) :=
    finite_relativeQuotient_trans U V W
  exact SmoothSheafVariation.coefficientTrace_comp_ofEq R
    (X := (inclusion W).obj ((ρ.invariantRestrictionFunctor (k.trans h)).obj d))
    (finiteF := finite_subgroupRestriction_inducedMap_fiber k
      ((ρ.invariantRestrictionFunctor h).obj d))
    (finiteG := finite_subgroupRestriction_inducedMap_fiber h d)
    (finiteQ := finite_subgroupRestriction_inducedMap_fiber (k.trans h) d)
    (subgroupRestriction k ((ρ.invariantRestrictionFunctor h).obj d))
    (subgroupRestriction h d) (subgroupRestriction (k.trans h) d)
    (subgroupRestriction_comp h k d)
    (isCoveringMap_subgroupRestriction_inducedMap k _)
    (isCoveringMap_subgroupRestriction_inducedMap h d)
    (isCoveringMap_subgroupRestriction_inducedMap (k.trans h) d) M

/-- Smooth trace transitivity is natural on the entire original smooth coefficient category. -/
theorem subgroupRestrictionSmoothCoefficientTraceNatTrans_comp :
    letI : Finite (U ⧸ W.toSubgroup.subgroupOf U.toSubgroup) :=
      finite_relativeQuotient_trans U V W
    Functor.whiskerLeft
        (SmoothSheafVariation.coefficientFunctor R
          ((inclusion W).obj ((ρ.invariantRestrictionFunctor (k.trans h)).obj d)))
        (subgroupRestrictionSmoothDirectImageCompMap h k d R) ≫
          subgroupRestrictionSmoothCoefficientTraceNatTrans (k.trans h) d R =
      Functor.whiskerRight
          (subgroupRestrictionSmoothCoefficientTraceNatTrans k
            ((ρ.invariantRestrictionFunctor h).obj d) R)
          (SmoothSheafVariation.directImage R (subgroupRestriction h d)) ≫
        subgroupRestrictionSmoothCoefficientTraceNatTrans h d R := by
  let : Finite (U ⧸ W.toSubgroup.subgroupOf U.toSubgroup) :=
    finite_relativeQuotient_trans U V W
  exact SmoothSheafVariation.coefficientTraceNatTrans_comp_ofEq R
    (X := (inclusion W).obj ((ρ.invariantRestrictionFunctor (k.trans h)).obj d))
    (finiteF := finite_subgroupRestriction_inducedMap_fiber k
      ((ρ.invariantRestrictionFunctor h).obj d))
    (finiteG := finite_subgroupRestriction_inducedMap_fiber h d)
    (finiteQ := finite_subgroupRestriction_inducedMap_fiber (k.trans h) d)
    (subgroupRestriction k ((ρ.invariantRestrictionFunctor h).obj d))
    (subgroupRestriction h d) (subgroupRestriction (k.trans h) d)
    (subgroupRestriction_comp h k d)
    (isCoveringMap_subgroupRestriction_inducedMap k _)
    (isCoveringMap_subgroupRestriction_inducedMap h d)
    (isCoveringMap_subgroupRestriction_inducedMap (k.trans h) d)

end Finite

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
