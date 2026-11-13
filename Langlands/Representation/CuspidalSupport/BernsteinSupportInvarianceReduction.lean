import Langlands.Representation.CuspidalSupport.BernsteinSupportAssociationReduction
import Langlands.Representation.Classification.HeadDetectingCount
import Langlands.Representation.Filtration.LengthCriterionProof

/-! # Actual Bernstein support invariance under association from represented VI.5.4

Renard VI.5.4, Theorem: associated cuspidal data have inductions with the same
Jordan–Hölder factors. This module derives the standard-family statement
`BernsteinAssociatedSupportInvarianceStatement` from the represented-parabolic statement
`RepresentedParabolic.LeviSupercuspidalInductionAssociationStatement`.
-/

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
/-- Represented VI.5.4 at the level of arbitrary actual parabolics: an association witness
transfers every irreducible subquotient of `i_P^G ρ` to `i_{P'}^G ρ'`. -/
private theorem representedSubquotient_of_associated
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
        (∃ (g : rationalPoints G) (φ : M ≅ M'),
          φ.hom ≫ l' ≫ p' = l ≫ p ≫ (G.innerIso g).hom ∧
          ∃ L : ρ ≃ₗ[ℂ] ρ', ∀ (m : rationalPoints M) (x : ρ),
            L (ρ.representation m x) =
              ρ'.representation (rationalPoints.map φ.hom m) (L x)) →
        ∀ σ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G), σ.IsIrreducible →
          (SmoothRep.IsSubquotient σ
            ((RepresentedParabolic.leviInductionFunctor p l r hp hr hl hmul).obj ρ) ↔
          SmoothRep.IsSubquotient σ
            ((RepresentedParabolic.leviInductionFunctor p' l' r' hp' hr' hl' hmul').obj ρ')) := by
  intro _ _ P M U P' M' U' p l r hp hl hr hmul p' l' r' hp' hl' hr' hmul'
    ρ ρ' hρ hρsc hρ' hρ'sc hwit σ hσ
  have hab := hAssociate F G hG P M U P' M' U'
    p l r hp hl hr hmul p' l' r' hp' hl' hr' hmul' ρ ρ' hρ hρsc hρ' hρ'sc
  have hba := hAssociate F G hG P' M' U' P M U
    p' l' r' hp' hl' hr' hmul' p l r hp hl hr hmul ρ' ρ hρ' hρ'sc hρ hρsc
  have hJH := (hab.2.out 1 3).mp hwit
  obtain ⟨n, hn⟩ := hab.1
  obtain ⟨n', hn'⟩ := hba.1
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := pointTopology
  have hfin := LengthCriterionProof.isFiniteLength_of_hasCompositionSeriesLength hn
  have hfin' := LengthCriterionProof.isFiniteLength_of_hasCompositionSeriesLength hn'
  exact ⟨Classification.HeadDetectingCount.isSubquotient_of_haveSameJordanHolderFactors
      hfin hfin' hJH hσ,
    Classification.HeadDetectingCount.isSubquotient_of_haveSameJordanHolderFactors
      hfin' hfin (haveSameJordanHolderFactors_symm hJH) hσ⟩

set_option maxHeartbeats 20000 in
/-- An isomorphism `ρ ≅ e^* ρ'` of smooth representations is, on carriers, a linear
equivalence `ρ ≃ ρ'` intertwining `ρ(m)` with `ρ'(e m)`. -/
private theorem exists_pointwiseIntertwiner_of_pullbackIso
    {H K : Type uF} [Group H] [TopologicalSpace H] [Group K] [TopologicalSpace K]
    (e : H ≃ₜ* K) (ρ : SmoothRep.{0, uF, uV} ℂ H)
    (ρ' : SmoothRep.{0, uF, uV} ℂ K) (f : ρ ≅ SmoothRep.pullback e ρ') :
    ∃ L : ρ ≃ₗ[ℂ] ρ', ∀ (m : H) (x : ρ),
      L (ρ.representation m x) = ρ'.representation (e m) (L x) :=
  ⟨(SmoothRep.equivOfIso f).toLinearEquiv, fun m x =>
    LinearMap.congr_fun ((SmoothRep.equivOfIso f).isIntertwining' m) x⟩

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinSuppInvInstance1 : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance bernsteinSuppInvInstance2 : T2Space F :=
  Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
local instance bernsteinSuppInvInstance3 : TopologicalSpace (rationalPoints G) := pointTopology
local instance bernsteinSuppInvInstance4 (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance bernsteinSuppInvInstance5 (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance bernsteinSuppInvInstance6 (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance bernsteinSuppInvInstance7 (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

local instance bernsteinSuppInvInstance8 (I : Finset (SimpleRoot i ν)) :
    LocallyCompactSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  bernsteinRepresentedCuspInstance7 i ν I

local instance bernsteinSuppInvInstance9 (I : Finset (SimpleRoot i ν)) :
    NonarchimedeanGroup (rationalPoints (bernsteinLeviScheme i ν I)) :=
  bernsteinRepresentedCuspInstance8 i ν I

omit [LocallyOfFiniteType G.X.hom] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
set_option maxHeartbeats 20000 in
set_option backward.isDefEq.respectTransparency.types true in
/-- An actual association of standard data gives the represented association witness:
the conjugating point, the isomorphism of Levi schemes, and the equivariant linear
isomorphism underlying the pullback isomorphism. -/
private theorem bernsteinStandardWitness_of_association
    (I J : Finset (SimpleRoot i ν))
    (ρ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I)))
    (ρ' : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν J)))
    (c : RationalLeviConjugacy
      (Standard.leviHom i ν (rootSet i ν I))
      (Standard.leviHom i ν (rootSet i ν J)))
    (e : ρ ≅ rationalIsoPullback c.iso ρ') :
    ∃ (g : rationalPoints G) (φ : bernsteinLeviScheme i ν I ≅ bernsteinLeviScheme i ν J),
      φ.hom ≫ Standard.leviToParabolic i ν (rootSet i ν J) ≫
          Standard.parabolicHom i ν (rootSet i ν J) =
        Standard.leviToParabolic i ν (rootSet i ν I) ≫
          Standard.parabolicHom i ν (rootSet i ν I) ≫ (G.innerIso g).hom ∧
      ∃ L : ρ ≃ₗ[ℂ] ρ', ∀ (m : rationalPoints (bernsteinLeviScheme i ν I)) (x : ρ),
        L (ρ.representation m x) = ρ'.representation (rationalPoints.map φ.hom m) (L x) := by
  refine ⟨c.point, c.iso, ?_, ?_⟩
  · simpa only [← Standard.leviToParabolic_comp, Category.assoc] using c.commutes.symm
  · exact exists_pointwiseIntertwiner_of_pullbackIso
      (H := rationalPoints (bernsteinLeviScheme i ν I))
      (K := rationalPoints (bernsteinLeviScheme i ν J))
      (rationalPointIso c.iso) ρ ρ' e

omit [LocallyOfFiniteType G.X.hom] in
set_option maxHeartbeats 20000 in
set_option backward.isDefEq.respectTransparency.types true in
/-- Represented VI.5.4 specialised to standard parabolics: an association witness between
supercuspidal `ρ` on `M_I` and `ρ'` on `M_J` identifies the irreducible subquotients of the
two represented inductions. -/
private theorem bernsteinStandardSubquotient_iff_of_witness
    (hAssociate :
      RepresentedParabolic.LeviSupercuspidalInductionAssociationStatement.{uF, max uF uV})
    (I J : Finset (SimpleRoot i ν))
    (ρ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I)))
    (ρ' : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν J)))
    (hρ : ρ.IsIrreducible) (hρsc : RepresentedParabolic.IsSupercuspidal ρ)
    (hρ' : ρ'.IsIrreducible) (hρ'sc : RepresentedParabolic.IsSupercuspidal ρ')
    (hwit :
    ∃ (g : rationalPoints G) (φ : bernsteinLeviScheme i ν I ≅ bernsteinLeviScheme i ν J),
      φ.hom ≫ Standard.leviToParabolic i ν (rootSet i ν J) ≫
          Standard.parabolicHom i ν (rootSet i ν J) =
        Standard.leviToParabolic i ν (rootSet i ν I) ≫
          Standard.parabolicHom i ν (rootSet i ν I) ≫ (G.innerIso g).hom ∧
      ∃ L : ρ ≃ₗ[ℂ] ρ', ∀ (m : rationalPoints (bernsteinLeviScheme i ν I)) (x : ρ),
        L (ρ.representation m x) = ρ'.representation (rationalPoints.map φ.hom m) (L x))
    (σ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)) (hσ : σ.IsIrreducible) :
    SmoothRep.IsSubquotient σ
        ((bernsteinStandardRepresentedInductionFunctor i ν family I).obj ρ) ↔
      SmoothRep.IsSubquotient σ
        ((bernsteinStandardRepresentedInductionFunctor i ν family J).obj ρ') := by
  let A := bernsteinStandardRepresentativesGeometric i ν family I
  let B := bernsteinStandardRepresentativesGeometric i ν family J
  have hfull := representedSubquotient_of_associated hAssociate
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
    bernsteinSuppInvInstance3] at hwit hspec ⊢
  exact hspec hwit σ hσ

omit [LocallyOfFiniteType G.X.hom] in
set_option maxHeartbeats 20000 in
set_option backward.isDefEq.respectTransparency.types true in
/-- Renard VI.5.4 for the standard family, derived from represented VI.5.4: associated
cuspidal data have inductions with the same irreducible subquotients. -/
theorem bernsteinAssociatedSupportInvariance_of_represented
    (hAssociate :
      RepresentedParabolic.LeviSupercuspidalInductionAssociationStatement.{uF, max uF uV}) :
    BernsteinAssociatedSupportInvarianceStatement.{uF, uV} i ν family := by
  intro a b hab π
  obtain ⟨c, ⟨e⟩⟩ := hab
  have hwit := bernsteinStandardWitness_of_association i ν a.roots b.roots
    a.representation b.representation c e
  have hasc := a.isSupercuspidal i ν family
  have hbsc := b.isSupercuspidal i ν family
  have hiff := bernsteinStandardSubquotient_iff_of_witness i ν family hAssociate
    a.roots b.roots a.representation b.representation a.irreducible hasc b.irreducible hbsc hwit
  have hσa : ∀ σ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
      SmoothRep.IsSubquotient σ (bernsteinInduction i ν family a) ↔
        SmoothRep.IsSubquotient σ (bernsteinRepresentedInduction i ν family a) := fun σ =>
    ⟨fun h => h.of_iso_right (bernsteinRepresentedInductionIso i ν family a).symm,
      fun h => h.of_iso_right (bernsteinRepresentedInductionIso i ν family a)⟩
  have hσb : ∀ σ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
      SmoothRep.IsSubquotient σ (bernsteinInduction i ν family b) ↔
        SmoothRep.IsSubquotient σ (bernsteinRepresentedInduction i ν family b) := fun σ =>
    ⟨fun h => h.of_iso_right (bernsteinRepresentedInductionIso i ν family b).symm,
      fun h => h.of_iso_right (bernsteinRepresentedInductionIso i ν family b)⟩
  dsimp only [bernsteinRepresentedInduction] at hσa hσb
  dsimp only [bernsteinLeviScheme,
    bernsteinRepresentedInductionInstance3, bernsteinRepresentedInductionInstance7,
    bernsteinSuppInvInstance3, bernsteinSuppInvInstance7] at hσa hσb hiff
  constructor
  · rintro ⟨hπ, hsub⟩
    exact ⟨hπ, (hσb π).mpr ((hiff π hπ).mp ((hσa π).mp hsub))⟩
  · rintro ⟨hπ, hsub⟩
    exact ⟨hπ, (hσa π).mpr ((hiff π hπ).mpr ((hσb π).mp hsub))⟩

/-- Conditional reduction (internal): represented VI.5.4 at carriers in `Type (max uF uV)`
implies, for every standard family, that associated cuspidal data have inductions with the
same irreducible subquotients (`BernsteinAssociatedSupportInvarianceStatement`). The
conclusion is quantified exactly as the support-invariance premise of
`BernsteinCenterFunctionsReductionStatement`. -/
def BernsteinAssociatedSupportInvarianceReductionStatement : Prop :=
  RepresentedParabolic.LeviSupercuspidalInductionAssociationStatement.{uF, max uF uV} →
    ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
        [IsNonarchimedeanLocalField F]
        (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
        [LocallyOfFiniteType G.X.hom]
        (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
        (ν : cocharacterLattice T),
        letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
        letI : TopologicalSpace (rationalPoints G) := pointTopology
        ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
          (family : BernsteinStandardFamily i ν),
          BernsteinAssociatedSupportInvarianceStatement.{uF, uV} i ν family

/-- Proof of the reduction: `bernsteinAssociatedSupportInvariance_of_represented` for each
standard family. -/
theorem bernsteinAssociatedSupportInvariance_reduction :
    BernsteinAssociatedSupportInvarianceReductionStatement.{uF, uV} := by
  intro hAssociate F _ _ _ _ G _ _ T i ν
  let : TopologicalSpace (rationalPoints G) := pointTopology
  intro _ _ family
  exact bernsteinAssociatedSupportInvariance_of_represented i ν family hAssociate

end Langlands.CuspidalSupport
