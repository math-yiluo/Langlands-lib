import Langlands.Representation.CuspidalSupport.BernsteinRepresentedInduction
import Langlands.Representation.CuspidalSupport.BernsteinSupportComparison
import Langlands.Representation.Exponents.LeviSupercuspidalInductionAssociationStatement

/-! # Actual Bernstein support association from represented VI.5.4 -/

noncomputable section

set_option maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

set_option maxHeartbeats 20000 in
private theorem representedAssociation_of_common
    (hAssociate :
      RepresentedParabolic.LeviSupercuspidalInductionAssociationStatement.{uF, uV})
    (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [T2Space F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U P' M' U' : GroupScheme (Spec (CommRingCat.of F)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (p' : P' ⟶ G) (l' : M' ⟶ P') (r' : U' ⟶ P')
      (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
      (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
      (hmul' : IsIso (subgroupMultiplication l' r')),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) :=
        RepresentedParabolic.leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) :=
        RepresentedParabolic.leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) :=
        RepresentedParabolic.leviPoints_nonarchimedeanGroup p l hp hl
      haveI := hl'.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M') :=
        RepresentedParabolic.leviPointTopology l' hl'
      haveI : LocallyCompactSpace (rationalPoints M') :=
        RepresentedParabolic.leviPoints_locallyCompactSpace p' l' hp' hl'
      haveI : NonarchimedeanGroup (rationalPoints M') :=
        RepresentedParabolic.leviPoints_nonarchimedeanGroup p' l' hp' hl'
      ∀ (ρ : SmoothRep.{0, uF, uV} ℂ (rationalPoints M))
        (ρ' : SmoothRep.{0, uF, uV} ℂ (rationalPoints M')),
        ρ.IsIrreducible → RepresentedParabolic.IsSupercuspidal ρ →
        ρ'.IsIrreducible → RepresentedParabolic.IsSupercuspidal ρ' →
        (∃ σ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
          σ.IsIrreducible ∧
          SmoothRep.IsSubquotient σ
            ((RepresentedParabolic.leviInductionFunctor p l r hp hr hl hmul).obj ρ) ∧
          SmoothRep.IsSubquotient σ
            ((RepresentedParabolic.leviInductionFunctor p' l' r' hp' hr' hl' hmul').obj ρ')) →
        ∃ (g : rationalPoints G) (φ : M ≅ M'),
          φ.hom ≫ l' ≫ p' = l ≫ p ≫ (G.innerIso g).hom ∧
          ∃ L : ρ ≃ₗ[ℂ] ρ', ∀ (m : rationalPoints M) (x : ρ),
            L (ρ.representation m x) =
              ρ'.representation (rationalPoints.map φ.hom m) (L x) := by
  intro _ _ P M U P' M' U' p l r hp hl hr hmul p' l' r' hp' hl' hr' hmul'
    ρ ρ' hρ hρsc hρ' hρ'sc hcommon
  have hfull := (hAssociate F G hG P M U P' M' U'
    p l r hp hl hr hmul p' l' r' hp' hl' hr' hmul' ρ ρ' hρ hρsc hρ' hρ'sc).2
  exact (hfull.out 4 1).mp hcommon

set_option maxHeartbeats 20000 in
private def pullbackIsoOfPointwiseIntertwiner
    {H K : Type uF} [Group H] [TopologicalSpace H] [Group K] [TopologicalSpace K]
    (e : H ≃ₜ* K) (ρ : SmoothRep.{0, uF, uV} ℂ H)
    (ρ' : SmoothRep.{0, uF, uV} ℂ K) (L : ρ ≃ₗ[ℂ] ρ')
    (hL : ∀ (m : H) (x : ρ),
      L (ρ.representation m x) = ρ'.representation (e m) (L x)) :
    ρ ≅ SmoothRep.pullback e ρ' := by
  refine SmoothRep.mkIso (Representation.Equiv.mk L ?_)
  intro m
  ext x
  exact hL m x

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinAssocReductionInstance1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance bernsteinAssocReductionInstance2 : T2Space F := Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
local instance bernsteinAssocReductionInstance3 : TopologicalSpace (rationalPoints G) := pointTopology
local instance bernsteinAssocReductionInstance4 (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance bernsteinAssocReductionInstance5 (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance bernsteinAssocReductionInstance6 (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance bernsteinAssocReductionInstance7 (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

local instance bernsteinAssocReductionInstance8 (I : Finset (SimpleRoot i ν)) :
    LocallyCompactSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  bernsteinRepresentedCuspInstance7 i ν I

local instance bernsteinAssocReductionInstance9 (I : Finset (SimpleRoot i ν)) :
    NonarchimedeanGroup (rationalPoints (bernsteinLeviScheme i ν I)) :=
  bernsteinRepresentedCuspInstance8 i ν I

omit [LocallyOfFiniteType G.X.hom] in
set_option maxHeartbeats 20000 in
set_option backward.isDefEq.respectTransparency.types true in
private theorem bernsteinStandardRepresentedWitness_of_common
    (hAssociate :
      RepresentedParabolic.LeviSupercuspidalInductionAssociationStatement.{uF, max uF uV})
    (I J : Finset (SimpleRoot i ν))
    (ρ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I)))
    (ρ' : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν J)))
    (hρ : ρ.IsIrreducible) (hρsc : RepresentedParabolic.IsSupercuspidal ρ)
    (hρ' : ρ'.IsIrreducible) (hρ'sc : RepresentedParabolic.IsSupercuspidal ρ')
    (hcommon : ∃ σ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
      σ.IsIrreducible ∧
      SmoothRep.IsSubquotient σ
        ((bernsteinStandardRepresentedInductionFunctor i ν family I).obj ρ) ∧
      SmoothRep.IsSubquotient σ
        ((bernsteinStandardRepresentedInductionFunctor i ν family J).obj ρ')) :
    ∃ (g : rationalPoints G) (φ : bernsteinLeviScheme i ν I ≅ bernsteinLeviScheme i ν J),
      φ.hom ≫ Standard.leviToParabolic i ν (rootSet i ν J) ≫
          Standard.parabolicHom i ν (rootSet i ν J) =
        Standard.leviToParabolic i ν (rootSet i ν I) ≫
          Standard.parabolicHom i ν (rootSet i ν I) ≫ (G.innerIso g).hom ∧
      ∃ L : ρ ≃ₗ[ℂ] ρ', ∀ (m : rationalPoints (bernsteinLeviScheme i ν I)) (x : ρ),
        L (ρ.representation m x) = ρ'.representation (rationalPoints.map φ.hom m) (L x) := by
  let A := bernsteinStandardRepresentativesGeometric i ν family I
  let B := bernsteinStandardRepresentativesGeometric i ν family J
  have hfull := representedAssociation_of_common hAssociate
    F G family.connectedReductive
    (Standard.parabolicScheme i ν (rootSet i ν I))
    (bernsteinLeviScheme i ν I)
    (Standard.unipotentScheme i ν (rootSet i ν I))
    (Standard.parabolicScheme i ν (rootSet i ν J))
    (bernsteinLeviScheme i ν J)
    (Standard.unipotentScheme i ν (rootSet i ν J))
    (Standard.parabolicHom i ν (rootSet i ν I))
    (Standard.leviToParabolic i ν (rootSet i ν I))
    (Standard.unipotentToParabolic i ν (rootSet i ν I))
    A.1 A.2.1 A.2.2.1 A.2.2.2
    (Standard.parabolicHom i ν (rootSet i ν J))
    (Standard.leviToParabolic i ν (rootSet i ν J))
    (Standard.unipotentToParabolic i ν (rootSet i ν J))
    B.1 B.2.1 B.2.2.1 B.2.2.2
  have hspec := hfull ρ ρ' hρ hρsc hρ' hρ'sc
  dsimp only [bernsteinStandardRepresentedInductionFunctor, bernsteinLeviScheme,
    RepresentedParabolic.leviPointTopology, RepresentedParabolic.leviAmbientPointTopology,
    bernsteinRepresentedInductionInstance3, bernsteinRepresentedInductionInstance7,
    bernsteinAssocReductionInstance3] at hcommon hspec
  exact hspec hcommon

omit [LocallyOfFiniteType G.X.hom] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
set_option maxHeartbeats 20000 in
set_option backward.isDefEq.respectTransparency.types true in
private theorem bernsteinStandardAssociation_of_witness
    (I J : Finset (SimpleRoot i ν))
    (ρ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I)))
    (ρ' : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν J)))
    (hwit :
    ∃ (g : rationalPoints G) (φ : bernsteinLeviScheme i ν I ≅ bernsteinLeviScheme i ν J),
      φ.hom ≫ Standard.leviToParabolic i ν (rootSet i ν J) ≫
          Standard.parabolicHom i ν (rootSet i ν J) =
        Standard.leviToParabolic i ν (rootSet i ν I) ≫
          Standard.parabolicHom i ν (rootSet i ν I) ≫ (G.innerIso g).hom ∧
      ∃ L : ρ ≃ₗ[ℂ] ρ', ∀ (m : rationalPoints (bernsteinLeviScheme i ν I)) (x : ρ),
        L (ρ.representation m x) = ρ'.representation (rationalPoints.map φ.hom m) (L x)) :
    ∃ c : RationalLeviConjugacy
      (Standard.leviHom i ν (rootSet i ν I))
      (Standard.leviHom i ν (rootSet i ν J)),
      Nonempty (ρ ≅ rationalIsoPullback c.iso ρ') := by
  obtain ⟨g, φ, hφ, L, hL⟩ := hwit
  let c : RationalLeviConjugacy
      (Standard.leviHom i ν (rootSet i ν I))
      (Standard.leviHom i ν (rootSet i ν J)) :=
    ⟨g, φ, by
      simpa only [← Standard.leviToParabolic_comp, Category.assoc] using hφ.symm⟩
  let e : ρ ≅ rationalIsoPullback φ ρ' :=
    pullbackIsoOfPointwiseIntertwiner
      (H := rationalPoints (bernsteinLeviScheme i ν I))
      (K := rationalPoints (bernsteinLeviScheme i ν J))
      (rationalPointIso φ) ρ ρ' L hL
  exact ⟨c, ⟨e⟩⟩

omit [LocallyOfFiniteType G.X.hom] in
set_option maxHeartbeats 20000 in
set_option backward.isDefEq.respectTransparency.types true in
/-- The common-constituent implication of represented VI.5.4 applies to the
original actual Bernstein data. The global VI.5.4 target remains explicit. -/
theorem bernsteinCuspidalSupportAssociation_of_represented
    (hAssociate :
      RepresentedParabolic.LeviSupercuspidalInductionAssociationStatement.{uF, max uF uV}) :
    BernsteinCuspidalSupportAssociationStatement.{uF, uV} i ν family := by
  intro a b π ha hb
  have hcommon :
      ∃ σ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
        σ.IsIrreducible ∧
        SmoothRep.IsSubquotient σ (bernsteinRepresentedInduction i ν family a) ∧
        SmoothRep.IsSubquotient σ (bernsteinRepresentedInduction i ν family b) :=
    ⟨π, ha.1,
      ha.2.of_iso_right (bernsteinRepresentedInductionIso i ν family a).symm,
      hb.2.of_iso_right (bernsteinRepresentedInductionIso i ν family b).symm⟩
  dsimp only [bernsteinRepresentedInduction] at hcommon
  apply bernsteinStandardAssociation_of_witness i ν a.roots b.roots
    a.representation b.representation
  have hasc := a.isSupercuspidal i ν family
  have hbsc := b.isSupercuspidal i ν family
  have hw := bernsteinStandardRepresentedWitness_of_common i ν family hAssociate
    a.roots b.roots a.representation b.representation
    a.irreducible hasc b.irreducible hbsc
  dsimp only [bernsteinLeviScheme,
    bernsteinRepresentedInductionInstance3, bernsteinRepresentedInductionInstance7,
    bernsteinAssocReductionInstance3] at hcommon hw ⊢
  exact hw hcommon

omit [LocallyOfFiniteType G.X.hom] in
set_option backward.isDefEq.respectTransparency.types true in
/-- A chosen actual conjugacy and equivariant pullback isomorphism obtained
from the represented common-constituent theorem. -/
def bernsteinCuspidalSupportAssociationWitnessOfRepresented
    (hAssociate :
      RepresentedParabolic.LeviSupercuspidalInductionAssociationStatement.{uF, max uF uV})
    (a b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (ha : IsBernsteinCuspidalSupport i ν family a π)
    (hb : IsBernsteinCuspidalSupport i ν family b π) :
    Σ c : RationalLeviConjugacy
      (Standard.leviHom i ν (rootSet i ν a.roots))
      (Standard.leviHom i ν (rootSet i ν b.roots)),
      a.representation ≅ rationalIsoPullback c.iso b.representation := by
  have h := bernsteinCuspidalSupportAssociation_of_represented i ν family hAssociate
    a b π ha hb
  exact ⟨Classical.choose h, Classical.choice (Classical.choose_spec h)⟩

/-- Actual inertial-support uniqueness follows from represented VI.5.4,
with all standard/represented structural comparisons discharged. -/
theorem bernsteinInertialSupportUniqueness_of_represented
    (hAssociate :
      RepresentedParabolic.LeviSupercuspidalInductionAssociationStatement.{uF, max uF uV}) :
    BernsteinInertialSupportUniquenessStatement.{uF, uV} i ν family :=
  bernsteinInertialSupportUniqueness_of_association
    (bernsteinCuspidalSupportAssociation_of_represented i ν family hAssociate)

end Langlands.CuspidalSupport
