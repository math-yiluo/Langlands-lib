import Langlands.Representation.Geometric.RepresentedGeometricLemmaTargetEndpoint
import Langlands.Representation.Geometric.RepresentedGeometricLemmaCoefficient
import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Representation.Induction.SmoothGroupTransport

/-! # Compact target induction and the original represented piece -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Induction

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance targetInductionAmbientPointTopology :
    TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
  q lQ rQ hq hrQ hlQ hmulQ z)

local instance targetInductionCommonSourceLeviPointTopology :
    TopologicalSpace (rationalPoints D.M') := leviPointTopology D.l' D.hl'
local instance targetInductionCommonTargetLeviPointTopology :
    TopologicalSpace (rationalPoints D.L') := leviPointTopology D.lQ' D.hlQ'

local notation "MI" => pointImage (lQ ≫ q)
local notation "PJ" => pointImage p
local notation "K" => geometricTargetIntersection MI PJ z⁻¹
local notation "Ki" => Subgroup.subgroupOf K MI
local notation "flatE" => subgroupOfContinuousEquiv (inf_le_left : K ≤ MI)
local notation "S" => pointImage (D.r' ≫ D.p')
local notation "Hs" => pointImage (D.l' ≫ D.p')
local notation "hHsS" => pointImage_le_normalizer D.p' D.l' D.r' D.hr'
local notation "iT" => D.targetCommonTorusHom ≫ D.lQ' ≫ D.q' ≫ lQ ≫ q

/-- The original target quotient and the literal intersection quotient
inside the original target Levi image have the same topology. -/
def targetParabolicQuotientHomeomorph :
    letI := leviPointTopology lQ hlQ
    LeftQuotient (pointImage D.q') ≃ₜ LeftQuotient Ki := by
  letI := leviPointTopology lQ hlQ
  refine Homeomorph.Quotient.congr (leviPointsEquiv q lQ hq hlQ).toHomeomorph ?_
  intro x y
  rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
  change (y * x⁻¹ ∈ pointImage D.q') ↔
    (leviPointsEquiv q lQ hq hlQ y) * (leviPointsEquiv q lQ hq hlQ x)⁻¹ ∈ Ki
  simpa only [map_mul, map_inv] using
    D.mem_targetParabolicPoints_leviPointsEquiv (y * x⁻¹)

omit [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- Actual quotient compactness transfers through the original point-group
equivalence; no compactness assertion is supplied for an auxiliary quotient. -/
theorem targetIntersectionQuotient_compactSpace
    (hcompact : letI := leviPointTopology lQ hlQ;
      CompactSpace (LeftQuotient (pointImage D.q'))) :
    CompactSpace (LeftQuotient Ki) := by
  let := leviPointTopology lQ hlQ
  let := hcompact
  exact D.targetParabolicQuotientHomeomorph.compactSpace

variable (A : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))

/-- The exact normalized coefficient on the literal intersection's copy
inside the original target Levi image. -/
def targetIntersectionCoefficientInLevi :
    letI := leviPointTopology l hl
    Representation ℂ Ki (Jacquet.Localization.Coinvariants A.representation S 1) := by
  letI := leviPointTopology l hl
  exact (D.normalizedTargetIntersectionCoefficientAction A).comp (flatE).toMonoidHom

/-- The actual quotient map of each original source intertwiner, with the
normalized intersection action and nested target subgroup retained. -/
def targetIntersectionCoefficientMap
    {B : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)}
    (f : A ⟶ B) :
    letI := leviPointTopology l hl
    (D.targetIntersectionCoefficientInLevi A).IntertwiningMap
      (D.targetIntersectionCoefficientInLevi B) := by
  letI := leviPointTopology l hl
  let π := D.targetIntersectionLeviProjection.comp (flatE).toMonoidHom
  exact twistIntertwining
    (D.normalizedTargetIntersectionCoefficientCharacter.comp (flatE).toMonoidHom)
    ({ toLinearMap := Jacquet.Localization.mapLinear S 1 (SmoothRep.hom f)
       isIntertwining' x := (Jacquet.Localization.map S 1 Hs hHsS
         (Jacquet.Localization.isInvariant_one S Hs hHsS) (SmoothRep.hom f)).isIntertwining'
           ((rationalPoints.map (D.l' ≫ D.p')).rangeRestrict
             (D.e (D.targetIntersectionLeviProjection ((flatE) x)))) } :
      Representation.IntertwiningMap ((D.ordinaryCommonLeviCoefficientAction A).comp π)
        ((D.ordinaryCommonLeviCoefficientAction B).comp π))

/-- The full normalized intersection coefficient and its original quotient
maps form a functor on the full smooth source category. -/
def normalizedTargetIntersectionCoefficientFunctor :
    letI := leviPointTopology l hl
    SmoothRep.{0, u, v} ℂ (rationalPoints M) ⥤ Rep.{v} ℂ Ki := by
  letI := leviPointTopology l hl
  exact {
    obj A := Rep.of (D.targetIntersectionCoefficientInLevi A)
    map f := Rep.ofHom (D.targetIntersectionCoefficientMap _ f)
    map_id A := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply Jacquet.Localization.hom_ext
      ext a
      rfl
    map_comp f g := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply Jacquet.Localization.hom_ext
      ext a
      rfl }

/-- Actual compact induction from the literal target intersection,
transported to the original target Levi's own rational points. -/
def targetNormalizedCompactFunctor :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    SmoothRep.{0, u, v} ℂ (rationalPoints M) ⥤ Rep.{max u v} ℂ (rationalPoints L) := by
  letI := leviPointTopology l hl
  letI := leviPointTopology lQ hlQ
  exact D.normalizedTargetIntersectionCoefficientFunctor ⋙ compactInductionFunctor Ki ⋙
    SmoothRep.pullbackFunctor (leviPointsEquiv q lQ hq hlQ) ⋙ SmoothRep.toRep

namespace DynamicRealization

variable [ValuativeRel k] [IsNonarchimedeanLocalField k] [Smooth G.X.hom]
  (R : D.DynamicRealization)

local instance targetInductionTorusClosed : IsClosedImmersion (iT).hom.hom.left :=
  D.targetCommonTorus_isMaximalSplitTorus_ambient.1.2

/-- Compact induction of the actual normalized intersection coefficient,
transported to the original target Levi, is the original represented piece.
The actual inner target quotient compactness and structural inputs are explicit. -/
def targetNormalizedInductionEquiv
    (hcompact : letI := leviPointTopology lQ hlQ;
      CompactSpace (LeftQuotient (pointImage D.q')))
    (hroot : HasRelativeRootSystem iT)
    (hinj : Function.Injective (characterRestrict D.targetCommonTorusHom)) :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    Representation.Equiv
      ((compactInduced Ki (D.targetIntersectionCoefficientInLevi A)).comp
        (leviPointsEquiv q lQ hq hlQ).toMonoidHom)
      ((D.pieceFunctor.obj A).ρ) := by
  letI := hl.isConnectedReductive.isAffineHom
  letI := hlQ.isConnectedReductive.isAffineHom
  letI := leviPointTopology l hl
  letI := leviPointTopology lQ hlQ
  letI := leviPoints_locallyCompactSpace p l hp hl
  letI := leviPoints_nonarchimedeanGroup p l hp hl
  letI := leviPoints_locallyCompactSpace q lQ hq hlQ
  letI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  letI := D.targetIntersectionQuotient_compactSpace hcompact
  let e := GroupTransport.subgroupEquiv (leviPointsEquiv q lQ hq hlQ)
    D.mem_targetParabolicPoints_leviPointsEquiv
  have hcoeff :
      (D.normalizedTargetIntersectionCoefficientAction A).comp
          D.targetParabolicPointsEquiv.toMonoidHom =
        D.originalTargetInducingCoefficient A := by
    rw [normalizedTargetIntersectionCoefficientAction_eq_endpoints
        (D := D) (A := A) (R := R) hroot hinj,
      ← D.originalTargetInducingCoefficient_eq_endpoint A]
  have hcov (a : pointImage D.q') :
      D.targetIntersectionCoefficientInLevi A (e a) = D.originalTargetInducingCoefficient A a :=
    congrArg (fun ρ : Representation ℂ (pointImage D.q')
      (Jacquet.Localization.Coinvariants A.representation S 1) => ρ a) hcoeff
  let e0 := (compactInclusion Ki (D.targetIntersectionCoefficientInLevi A)).ofBijective
    (compactInclusion_bijective_of_compactSpace Ki (D.targetIntersectionCoefficientInLevi A))
  let e1 := precomposeSmoothInducedGroupEquiv (leviPointsEquiv q lQ hq hlQ)
    e.toMulEquiv (fun _ => rfl) hcov
  exact (restrictAlongEquiv (leviPointsEquiv q lQ hq hlQ).toMonoidHom e0).trans e1

@[simp]
theorem targetNormalizedInductionEquiv_eval
    (hcompact : letI := leviPointTopology lQ hlQ;
      CompactSpace (LeftQuotient (pointImage D.q')))
    (hroot : HasRelativeRootSystem iT)
    (hinj : Function.Injective (characterRestrict D.targetCommonTorusHom))
    (F : letI := leviPointTopology l hl;
      CompactFunctions Ki (D.targetIntersectionCoefficientInLevi A))
    (x : rationalPoints L) :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    eval (pointImage D.q') (D.originalTargetInducingCoefficient A)
        (targetNormalizedInductionEquiv (D := D) (A := A) (R := R) hcompact hroot hinj F) x =
      eval Ki (D.targetIntersectionCoefficientInLevi A) F.val
        (leviPointsEquiv q lQ hq hlQ x) := by
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  rfl

/-- The target function-space equivalence commutes with every source
intertwiner through the original source Jacquet quotient map. -/
theorem targetNormalizedInductionEquiv_natural
    (hcompact : letI := leviPointTopology lQ hlQ;
      CompactSpace (LeftQuotient (pointImage D.q')))
    (hroot : HasRelativeRootSystem iT)
    (hinj : Function.Injective (characterRestrict D.targetCommonTorusHom))
    {B : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)}
    (f : A ⟶ B)
    (F : letI := leviPointTopology l hl;
      CompactFunctions Ki (D.targetIntersectionCoefficientInLevi A)) :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    targetNormalizedInductionEquiv (D := D) (A := B) (R := R) hcompact hroot hinj
        (compactInducedMap Ki (D.targetIntersectionCoefficientMap A f) F) =
      (D.pieceFunctor.map f).hom
        (targetNormalizedInductionEquiv (D := D) (A := A) (R := R) hcompact hroot hinj F) := by
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  apply Subtype.ext
  apply Subtype.ext
  funext x
  rfl

/-- The natural target adapter from actual normalized compact induction
to the original represented Jacquet--conjugation--induction piece. -/
def targetNormalizedCompactIso
    (hcompact : letI := leviPointTopology lQ hlQ;
      CompactSpace (LeftQuotient (pointImage D.q')))
    (hroot : HasRelativeRootSystem iT)
    (hinj : Function.Injective (characterRestrict D.targetCommonTorusHom)) :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    D.targetNormalizedCompactFunctor ≅ D.pieceFunctor := by
  letI := leviPointTopology l hl
  letI := leviPointTopology lQ hlQ
  refine NatIso.ofComponents
    (fun A => Rep.mkIso
      (targetNormalizedInductionEquiv (D := D) (A := A) (R := R) hcompact hroot hinj)) ?_
  intro A B f
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro F
  exact targetNormalizedInductionEquiv_natural
    (D := D) (A := A) (R := R) hcompact hroot hinj f F

end DynamicRealization

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
