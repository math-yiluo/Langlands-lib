import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSubgroupTrace

/-! # Transitivity for the original rational subgroup maps and coefficient traces -/

noncomputable section

universe u v r w a b

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Topology
open Langlands.Sheaf.Equivariant

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}

namespace OpenSubgroupTransport

/-- Identity subgroup restriction is the unchanged original rational arrow. -/
@[simp]
theorem subgroupRestriction_id (U : OpenSubgroup G) (d : ρ.InvariantRationalDomain U) :
    subgroupRestriction (le_refl U) d = 𝟙 ((inclusion U).obj d) :=
  Hom.ext rfl

/-- Successive original subgroup restrictions are the direct original restriction. -/
@[simp]
theorem subgroupRestriction_comp {U V W : OpenSubgroup G}
    (h : V ≤ U) (k : W ≤ V) (d : ρ.InvariantRationalDomain U) :
    subgroupRestriction k ((ρ.invariantRestrictionFunctor h).obj d) ≫
        subgroupRestriction h d =
      subgroupRestriction (k.trans h) d :=
  Hom.ext (one_mul 1)

omit [IsTopologicalGroup G] in
/-- Finite short relative quotients imply a finite long relative quotient. -/
theorem finite_relativeQuotient_trans (U V W : OpenSubgroup G)
    [Finite (V ⧸ W.toSubgroup.subgroupOf V.toSubgroup)]
    [Finite (U ⧸ V.toSubgroup.subgroupOf U.toSubgroup)] :
    Finite (U ⧸ W.toSubgroup.subgroupOf U.toSubgroup) :=
  Subgroup.index_ne_zero_iff_finite.mp
    (Subgroup.relIndex_ne_zero_trans
      (Subgroup.index_ne_zero_of_finite
        (H := W.toSubgroup.subgroupOf V.toSubgroup))
      (Subgroup.index_ne_zero_of_finite
        (H := V.toSubgroup.subgroupOf U.toSubgroup)))

variable {U V W : OpenSubgroup G} (h : V ≤ U) (k : W ≤ V)
  (d : ρ.InvariantRationalDomain U)

/-- The actual continuous maps compose on every original quotient point. -/
theorem subgroupRestriction_inducedMap_comp
    (z : ((inclusion W).obj
      ((ρ.invariantRestrictionFunctor (k.trans h)).obj d)).InducedSpectrum) :
    (subgroupRestriction (k.trans h) d).inducedMap z =
      (subgroupRestriction h d).inducedMap
        ((subgroupRestriction k ((ρ.invariantRestrictionFunctor h).obj d)).inducedMap z) := by
  rw [← subgroupRestriction_comp h k d]
  exact Hom.inducedMap_comp _ _ z

/-- Transport the full direct-image comparison along equality of the rational arrows. -/
def directImageCompIsoOfEq {X Y Z : ρ.OpenSubgroupTransport}
    (f : X ⟶ Y) (g : Y ⟶ Z) (q : X ⟶ Z) (e : f ≫ g = q)
    (A : Type a) [Category.{b} A] :
    SheafVariation.directImage A q ≅
      SheafVariation.directImage A f ⋙ SheafVariation.directImage A g :=
  eqToIso (congrArg (SheafVariation.directImage A) e.symm) ≪≫
    SheafVariation.directImageCompIso A f g

/-- The direct long image is compared with the two original successive images. -/
def subgroupRestrictionDirectImageCompIso (A : Type a) [Category.{b} A] :
    SheafVariation.directImage A (subgroupRestriction (k.trans h) d) ≅
      SheafVariation.directImage A
          (subgroupRestriction k ((ρ.invariantRestrictionFunctor h).obj d)) ⋙
        SheafVariation.directImage A (subgroupRestriction h d) :=
  directImageCompIsoOfEq
    (X := (inclusion W).obj ((ρ.invariantRestrictionFunctor (k.trans h)).obj d))
    (subgroupRestriction k ((ρ.invariantRestrictionFunctor h).obj d))
    (subgroupRestriction h d) (subgroupRestriction (k.trans h) d)
    (subgroupRestriction_comp h k d) A

section Congruence

variable {X Y Z : ρ.OpenSubgroupTransport}
  {R : Type r} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M]

/-- Transport the existing coefficient pullback law along equality of rational arrows. -/
private theorem coefficientMap_comp_congr
    (f : X ⟶ Y) (g : Y ⟶ Z) (q : X ⟶ Z) (e : f ≫ g = q)
    (τ : Representation R G M) :
    SheafVariation.coefficientMap q τ ≫
        (directImageCompIsoOfEq f g q e (ModuleCat.{max (max u v) w} R)).hom.app
            (LocallyConstantSheaf.sheaf (X := X.InducedSpectrum) τ) =
      SheafVariation.coefficientMap g τ ≫
        (SheafVariation.directImage (ModuleCat.{max (max u v) w} R) g).map
          (SheafVariation.coefficientMap f τ) := by
  subst q
  simpa [directImageCompIsoOfEq] using SheafVariation.coefficientMap_comp f g τ

/-- The original full trace law respects equality of the original rational arrows. -/
private theorem coefficientTrace_comp_congr
    (f : X ⟶ Y) (g : Y ⟶ Z) (q : X ⟶ Z) (e : f ≫ g = q)
    [finiteF : ∀ y, Finite (f.inducedMap ⁻¹' {y})]
    [finiteG : ∀ z, Finite (g.inducedMap ⁻¹' {z})]
    [finiteQ : ∀ z, Finite (q.inducedMap ⁻¹' {z})]
    (hf : IsCoveringMap f.inducedMap) (hg : IsCoveringMap g.inducedMap)
    (hq : IsCoveringMap q.inducedMap) (τ : Representation R G M) :
    SheafVariation.coefficientTrace q hq τ =
      (directImageCompIsoOfEq f g q e (ModuleCat.{max (max u v) w} R)).hom.app
          (LocallyConstantSheaf.sheaf (X := X.InducedSpectrum) τ) ≫
        (SheafVariation.directImage (ModuleCat.{max (max u v) w} R) g).map
          (SheafVariation.coefficientTrace f hf τ) ≫
            SheafVariation.coefficientTrace g hg τ := by
  subst q
  simpa [directImageCompIsoOfEq] using SheafVariation.coefficientTrace_comp f g hf hg hq τ

/-- Equality transport for traces on the full original coefficient category. -/
private theorem coefficientTraceNatTrans_comp_congr
    (f : X ⟶ Y) (g : Y ⟶ Z) (q : X ⟶ Z) (e : f ≫ g = q)
    [finiteF : ∀ y, Finite (f.inducedMap ⁻¹' {y})]
    [finiteG : ∀ z, Finite (g.inducedMap ⁻¹' {z})]
    [finiteQ : ∀ z, Finite (q.inducedMap ⁻¹' {z})]
    (hf : IsCoveringMap f.inducedMap) (hg : IsCoveringMap g.inducedMap)
    (hq : IsCoveringMap q.inducedMap) :
    SheafVariation.coefficientTraceNatTrans (R := R) q hq =
      Functor.whiskerLeft (SheafVariation.coefficientFunctor X R)
          (directImageCompIsoOfEq f g q e (ModuleCat.{max (max u v) w} R)).hom ≫
        Functor.whiskerRight (SheafVariation.coefficientTraceNatTrans f hf)
          (SheafVariation.directImage (ModuleCat.{max (max u v) w} R) g) ≫
            SheafVariation.coefficientTraceNatTrans g hg := by
  subst q
  simpa [directImageCompIsoOfEq] using
    SheafVariation.coefficientTraceNatTrans_comp (R := R) f g hf hg hq

/-- Equality transport for compact traces on the original smooth coefficients. -/
private theorem compactSupportTrace_comp_congr
    (f : X ⟶ Y) (g : Y ⟶ Z) (q : X ⟶ Z) (e : f ≫ g = q)
    [finiteF : ∀ y, Finite (f.inducedMap ⁻¹' {y})]
    [finiteG : ∀ z, Finite (g.inducedMap ⁻¹' {z})]
    [finiteQ : ∀ z, Finite (q.inducedMap ⁻¹' {z})]
    (hf : IsCoveringMap f.inducedMap) (hg : IsCoveringMap g.inducedMap)
    (hq : IsCoveringMap q.inducedMap) (M : SmoothRep.{r, v, w} R G) :
    Hom.compactSupportTrace q hq M =
      Hom.compactSupportTrace f hf M ≫ Hom.compactSupportTrace g hg M := by
  subst q
  exact Hom.compactSupportTrace_comp f g hf hg hq M

end Congruence

section SheafPullback

variable {R : Type r} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M]

/-- Full original coefficient pullbacks compose through the actual image comparison. -/
theorem subgroupRestrictionCoefficientMap_comp (τ : Representation R G M) :
    let X := (inclusion W).obj ((ρ.invariantRestrictionFunctor (k.trans h)).obj d)
    let Y := (inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)
    let Z := (inclusion U).obj d
    let f : X ⟶ Y := subgroupRestriction k ((ρ.invariantRestrictionFunctor h).obj d)
    let g : Y ⟶ Z := subgroupRestriction h d
    let q : X ⟶ Z := subgroupRestriction (k.trans h) d
    SheafVariation.coefficientMap q τ ≫
        (directImageCompIsoOfEq f g q (subgroupRestriction_comp h k d)
          (ModuleCat.{max (max u v) w} R)).hom.app
            (LocallyConstantSheaf.sheaf (X := X.InducedSpectrum) τ) =
      SheafVariation.coefficientMap g τ ≫
        (SheafVariation.directImage (ModuleCat.{max (max u v) w} R) g).map
          (SheafVariation.coefficientMap f τ) :=
  coefficientMap_comp_congr
    (X := (inclusion W).obj ((ρ.invariantRestrictionFunctor (k.trans h)).obj d))
    (subgroupRestriction k ((ρ.invariantRestrictionFunctor h).obj d))
    (subgroupRestriction h d) (subgroupRestriction (k.trans h) d)
    (subgroupRestriction_comp h k d) τ

end SheafPullback

section Finite

variable [Finite (V ⧸ W.toSubgroup.subgroupOf V.toSubgroup)]
  [Finite (U ⧸ V.toSubgroup.subgroupOf U.toSubgroup)]

local instance finite_shortInnerFiber :
    ∀ y, Finite ((subgroupRestriction k
      ((ρ.invariantRestrictionFunctor h).obj d)).inducedMap ⁻¹' {y}) :=
  finite_subgroupRestriction_inducedMap_fiber k _

local instance finite_shortOuterFiber :
    ∀ y, Finite ((subgroupRestriction h d).inducedMap ⁻¹' {y}) :=
  finite_subgroupRestriction_inducedMap_fiber h d

/-- The proper original subgroup arrows also compose in the proper transport category. -/
theorem properSubgroupRestriction_comp :
    letI : Finite (U ⧸ W.toSubgroup.subgroupOf U.toSubgroup) :=
      finite_relativeQuotient_trans U V W
    properSubgroupRestriction k ((ρ.invariantRestrictionFunctor h).obj d) ≫
        properSubgroupRestriction h d =
      properSubgroupRestriction (k.trans h) d := by
  let : Finite (U ⧸ W.toSubgroup.subgroupOf U.toSubgroup) :=
    finite_relativeQuotient_trans U V W
  apply (properTransportInclusion ρ).map_injective
  exact subgroupRestriction_comp h k d

section Sheaf

variable {R : Type r} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M]

/-- The direct original finite-index trace equals the two full successive traces. -/
theorem subgroupRestrictionCoefficientTrace_comp (τ : Representation R G M) :
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
    SheafVariation.coefficientTrace q
        (isCoveringMap_subgroupRestriction_inducedMap (k.trans h) d) τ =
      (directImageCompIsoOfEq f g q (subgroupRestriction_comp h k d)
          (ModuleCat.{max (max u v) w} R)).hom.app
          (LocallyConstantSheaf.sheaf (X := X.InducedSpectrum) τ) ≫
        (SheafVariation.directImage (ModuleCat.{max (max u v) w} R) g).map
          (SheafVariation.coefficientTrace f
            (isCoveringMap_subgroupRestriction_inducedMap k _) τ) ≫
          SheafVariation.coefficientTrace g
            (isCoveringMap_subgroupRestriction_inducedMap h d) τ := by
  let : Finite (U ⧸ W.toSubgroup.subgroupOf U.toSubgroup) :=
    finite_relativeQuotient_trans U V W
  exact coefficientTrace_comp_congr
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
    (isCoveringMap_subgroupRestriction_inducedMap (k.trans h) d) τ

/-- Transitivity of traces retains every original coefficient intertwiner. -/
theorem subgroupRestrictionCoefficientTraceNatTrans_comp :
    letI : Finite (U ⧸ W.toSubgroup.subgroupOf U.toSubgroup) :=
      finite_relativeQuotient_trans U V W
    subgroupRestrictionCoefficientTraceNatTrans (R := R) (k.trans h) d =
      Functor.whiskerLeft
          (SheafVariation.coefficientFunctor
            ((inclusion W).obj ((ρ.invariantRestrictionFunctor (k.trans h)).obj d)) R)
          (subgroupRestrictionDirectImageCompIso h k d
            (ModuleCat.{max (max u v) w} R)).hom ≫
        Functor.whiskerRight
          (subgroupRestrictionCoefficientTraceNatTrans k
            ((ρ.invariantRestrictionFunctor h).obj d))
          (SheafVariation.directImage (ModuleCat.{max (max u v) w} R)
            (subgroupRestriction h d)) ≫
          subgroupRestrictionCoefficientTraceNatTrans h d := by
  let : Finite (U ⧸ W.toSubgroup.subgroupOf U.toSubgroup) :=
    finite_relativeQuotient_trans U V W
  exact coefficientTraceNatTrans_comp_congr
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

end Sheaf

section CompactSupport

variable {R : Type r} [CommRing R]

/-- Proper original compact pullbacks compose contravariantly. -/
theorem subgroupRestrictionCompactSupportPullback_comp (M : SmoothRep.{r, v, w} R G) :
    letI : Finite (U ⧸ W.toSubgroup.subgroupOf U.toSubgroup) :=
      finite_relativeQuotient_trans U V W
    subgroupRestrictionCompactSupportPullback (k.trans h) d M =
      subgroupRestrictionCompactSupportPullback h d M ≫
        subgroupRestrictionCompactSupportPullback k
          ((ρ.invariantRestrictionFunctor h).obj d) M := by
  let : Finite (U ⧸ W.toSubgroup.subgroupOf U.toSubgroup) :=
    finite_relativeQuotient_trans U V W
  ext s
  apply Subtype.ext
  apply LocallyConstant.ext
  intro z
  exact congrArg s.val (subgroupRestriction_inducedMap_comp h k d z)

/-- The full compact trace sums first over W-to-V and then V-to-U fibers. -/
theorem subgroupRestrictionCompactSupportTrace_comp (M : SmoothRep.{r, v, w} R G) :
    letI : Finite (U ⧸ W.toSubgroup.subgroupOf U.toSubgroup) :=
      finite_relativeQuotient_trans U V W
    subgroupRestrictionCompactSupportTrace (k.trans h) d M =
      subgroupRestrictionCompactSupportTrace k
          ((ρ.invariantRestrictionFunctor h).obj d) M ≫
        subgroupRestrictionCompactSupportTrace h d M := by
  let : Finite (U ⧸ W.toSubgroup.subgroupOf U.toSubgroup) :=
    finite_relativeQuotient_trans U V W
  exact compactSupportTrace_comp_congr
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

/-- Compact pullback transitivity is natural in every original smooth coefficient. -/
theorem subgroupRestrictionCompactSupportPullbackNatTrans_comp :
    letI : Finite (U ⧸ W.toSubgroup.subgroupOf U.toSubgroup) :=
      finite_relativeQuotient_trans U V W
    subgroupRestrictionCompactSupportPullbackNatTrans (R := R) (k.trans h) d =
      subgroupRestrictionCompactSupportPullbackNatTrans h d ≫
        subgroupRestrictionCompactSupportPullbackNatTrans k
          ((ρ.invariantRestrictionFunctor h).obj d) := by
  let : Finite (U ⧸ W.toSubgroup.subgroupOf U.toSubgroup) :=
    finite_relativeQuotient_trans U V W
  apply NatTrans.ext
  funext M
  exact subgroupRestrictionCompactSupportPullback_comp h k d M

/-- Compact trace transitivity is natural on the entire original coefficient category. -/
theorem subgroupRestrictionCompactSupportTraceNatTrans_comp :
    letI : Finite (U ⧸ W.toSubgroup.subgroupOf U.toSubgroup) :=
      finite_relativeQuotient_trans U V W
    subgroupRestrictionCompactSupportTraceNatTrans (R := R) (k.trans h) d =
      subgroupRestrictionCompactSupportTraceNatTrans k
          ((ρ.invariantRestrictionFunctor h).obj d) ≫
        subgroupRestrictionCompactSupportTraceNatTrans h d := by
  let : Finite (U ⧸ W.toSubgroup.subgroupOf U.toSubgroup) :=
    finite_relativeQuotient_trans U V W
  apply NatTrans.ext
  funext M
  exact subgroupRestrictionCompactSupportTrace_comp h k d M

end CompactSupport

end Finite

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
