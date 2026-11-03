import Langlands.GroupScheme.Rational.RelativeWeylCoxeterStatement
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Dynamic.OppositeIntersection

/-! # Associated standard groups and ambient opposite groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [IsAffineHom G.X.hom]
  (ν : cocharacterLattice T)

/-- Every longest lift sends the associated ambient standard parabolic and
radical to the opposite dynamic groups of every standard cocharacter for `J`,
as subgroup functors on every test scheme. -/
def IsStandardAssociatedOppositeTransport
    [Fintype (SimpleRoot i ν)] [Fintype (relativeWeylGroup i)]
    {CM : CoxeterMatrix (SimpleRoot i ν)}
    (cs : CoxeterSystem CM (relativeWeylGroup i)) : Prop :=
  ∀ (J : Finset (SimpleRoot i ν)) (n : normalizerPoints i),
    QuotientGroup.mk n = longestRep cs J →
    ∀ zeta : cocharacterLattice T, IsStandardCocharacter i ν (rootSet i ν J) zeta →
      (standardParabolic i ν (rootSet i ν (associatedSubset cs J)) =
        (Dynamic.parabolic
          (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).comap
          (G.innerIso (n : GroupScheme.rationalPoints G)).hom) ∧
      (standardUnipotent i ν (rootSet i ν (associatedSubset cs J)) =
        (Dynamic.unipotent
          (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).comap
          (G.innerIso (n : GroupScheme.rationalPoints G)).hom)

/-- The outer opposite P/U transport target over every field and for every
finite actual relative-Weyl Coxeter realization. Neither realization existence
nor either structural equality is supplied by this proposition. -/
def StandardAssociatedOppositeTransportStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
      ∀ [Fintype (SimpleRoot i ν)] [Fintype (relativeWeylGroup i)]
        (CM : CoxeterMatrix (SimpleRoot i ν))
        (cs : CoxeterSystem CM (relativeWeylGroup i)),
        IsRelativeWeylCoxeterRealization i ν cs →
          IsStandardAssociatedOppositeTransport i ν cs

/-- Supplied all-test opposite transport equalities give the actual
inverse-conjugation images on rational points, for the same lift and cocharacter. -/
theorem IsStandardAssociatedOppositeTransport.rationalPoints
    [Fintype (SimpleRoot i ν)] [Fintype (relativeWeylGroup i)]
    {CM : CoxeterMatrix (SimpleRoot i ν)}
    {cs : CoxeterSystem CM (relativeWeylGroup i)}
    (h : IsStandardAssociatedOppositeTransport i ν cs)
    (J : Finset (SimpleRoot i ν)) (n : normalizerPoints i)
    (hn : QuotientGroup.mk n = longestRep cs J)
    (zeta : cocharacterLattice T)
    (hzeta : IsStandardCocharacter i ν (rootSet i ν J) zeta) :
    ((standardParabolic i ν (rootSet i ν (associatedSubset cs J))).rationalPoints =
      (Dynamic.parabolic
        (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints.map
        (MulAut.conj ((n : GroupScheme.rationalPoints G)⁻¹)).toMonoidHom) ∧
    ((standardUnipotent i ν (rootSet i ν (associatedSubset cs J))).rationalPoints =
      (Dynamic.unipotent
        (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints.map
        (MulAut.conj ((n : GroupScheme.rationalPoints G)⁻¹)).toMonoidHom) := by
  obtain ⟨hP, hU⟩ := h J n hn zeta hzeta
  constructor
  · simpa only [SubgroupFunctor.rationalPoints_comap_innerIso_hom_eq_map] using
      congrArg (fun P : SubgroupFunctor G => P.rationalPoints) hP
  · simpa only [SubgroupFunctor.rationalPoints_comap_innerIso_hom_eq_map] using
      congrArg (fun U : SubgroupFunctor G => U.rationalPoints) hU

/-- The membership form uses forward conjugation by `n`; consumers writing
`g⁻¹ * x * g` therefore take the same actual point `g = n⁻¹`. -/
theorem IsStandardAssociatedOppositeTransport.mem_rationalPoints
    [Fintype (SimpleRoot i ν)] [Fintype (relativeWeylGroup i)]
    {CM : CoxeterMatrix (SimpleRoot i ν)}
    {cs : CoxeterSystem CM (relativeWeylGroup i)}
    (h : IsStandardAssociatedOppositeTransport i ν cs)
    (J : Finset (SimpleRoot i ν)) (n : normalizerPoints i)
    (hn : QuotientGroup.mk n = longestRep cs J)
    (zeta : cocharacterLattice T)
    (hzeta : IsStandardCocharacter i ν (rootSet i ν J) zeta)
    (x : GroupScheme.rationalPoints G) :
    (x ∈ (standardParabolic i ν (rootSet i ν (associatedSubset cs J))).rationalPoints ↔
      (n : GroupScheme.rationalPoints G) * x * (n : GroupScheme.rationalPoints G)⁻¹ ∈
        (Dynamic.parabolic
          (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints) ∧
    (x ∈ (standardUnipotent i ν (rootSet i ν (associatedSubset cs J))).rationalPoints ↔
      (n : GroupScheme.rationalPoints G) * x * (n : GroupScheme.rationalPoints G)⁻¹ ∈
        (Dynamic.unipotent
          (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints) := by
  obtain ⟨hP, hU⟩ := h J n hn zeta hzeta
  constructor
  · rw [hP]
    exact SubgroupFunctor.mem_rationalPoints_comap_innerIso_hom _ _ x
  · rw [hU]
    exact SubgroupFunctor.mem_rationalPoints_comap_innerIso_hom _ _ x

end Langlands.GroupScheme
