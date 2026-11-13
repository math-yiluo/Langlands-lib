import Langlands.Representation.CuspidalSupport.BernsteinBlockCharacterizationReduction
import Langlands.Representation.CuspidalSupport.BernsteinRepresentedInduction
import Langlands.Representation.Exponents.LeviJacquetInductionSupercuspidalFiltrationProof
import Langlands.Representation.Exponents.LeviJacquetNonSupercuspidalReduction
import Langlands.Representation.Filtration.ActualGradedExtraction
import Langlands.Representation.Aubert.General.RationalRootAssociationCuspidalityTransport

/-! # The geometric half of the Bernstein Jacquet exclusion (Renard VI.7.2) -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

universe u v

set_option maxHeartbeats 200000 in
/-- Renard VI.5.3 (iii), constituent form: for actual rational parabolics `P = MN` and
`Q = LU` with `M` conjugate to `L`, a supercuspidal `ρ` of `M(F)`, and an irreducible
subquotient `σ` of `r_Q i_P ρ`, there are `z ∈ G(F)` and an algebraic isomorphism
`φ : L ≅ M` conjugating `L` onto `M` through `z`, such that `σ` is a subquotient of
the pullback of `ρ` along the point map of `φ`. -/
theorem leviJacquetInduction_conjugateConstituent :
    ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k] [T2Space k]
      (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
      haveI := hG.isAffineHom
      letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
      ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
        (P M N Q L U : GroupScheme (Spec (CommRingCat.of k)))
        (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
        (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
        (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
        (hmul : IsIso (subgroupMultiplication l r))
        (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
        (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
        (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
        (hmulQ : IsIso (subgroupMultiplication lQ rQ)),
        (∃ (g : rationalPoints G) (φ : M ≅ L),
            φ.hom ≫ lQ ≫ q = l ≫ p ≫ (G.innerIso g).hom) →
        haveI := hl.isConnectedReductive.isAffineHom
        letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
        haveI : LocallyCompactSpace (rationalPoints M) :=
          leviPoints_locallyCompactSpace p l hp hl
        haveI : NonarchimedeanGroup (rationalPoints M) :=
          leviPoints_nonarchimedeanGroup p l hp hl
        haveI := hlQ.isConnectedReductive.isAffineHom
        letI : TopologicalSpace (rationalPoints L) := leviPointTopology lQ hlQ
        haveI : LocallyCompactSpace (rationalPoints L) :=
          leviPoints_locallyCompactSpace q lQ hq hlQ
        haveI : NonarchimedeanGroup (rationalPoints L) :=
          leviPoints_nonarchimedeanGroup q lQ hq hlQ
        ∀ ρ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M),
          (∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
            (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
            (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
            (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
            (hmul' : IsIso (subgroupMultiplication l' r')),
            ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ)) →
          ∀ σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints L),
            σ.IsIrreducible →
            SmoothRep.IsSubquotient σ
              ((leviJacquetFunctor.{u, max u v} q lQ rQ hq hrQ hlQ hmulQ).obj
                ((leviInductionFunctor p l r hp hr hl hmul).obj ρ)) →
            ∃ (z : rationalPoints G) (φ : L ≅ M)
              (e : rationalPoints L ≃ₜ* rationalPoints M),
              φ.hom ≫ l ≫ p = lQ ≫ q ≫ (G.innerIso z).hom ∧
              (∀ x, e x = rationalPoints.map φ.hom x) ∧
              SmoothRep.IsSubquotient σ (SmoothRep.pullback e ρ) := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q L U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hconj
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  have := hlQ.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology lQ hlQ
  have : LocallyCompactSpace (rationalPoints L) := leviPoints_locallyCompactSpace q lQ hq hlQ
  have : NonarchimedeanGroup (rationalPoints L) := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  intro ρ hρ σ hσ hσX
  obtain ⟨⟨m, c, z, φ, e, -, hφ, he, s, hs⟩, -⟩ :=
    leviJacquetInductionSupercuspidalFiltration.{u, max u v} k G hG P M N Q L U
      p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hconj ρ hρ
  obtain ⟨j, hj⟩ := ObjectRepFiltration.exists_smoothGradedObject_subquotient s hσ hσX
  exact ⟨z j, φ j, e j, hφ j, he j, hj.of_iso_right (SmoothRep.mkIso (hs j).some)⟩

end Langlands.Aubert.General.RepresentedParabolic

namespace Langlands.CuspidalSupport

universe uF uV

/-- Equal radicals and Levi subgroups, with pointwise equal Levi parametrizations,
give the same transported normalized Jacquet module. -/
def pullbackNormalizedJacquetIsoOfEq
    {Γ : Type uF} [Group Γ] [TopologicalSpace Γ] [LocallyCompactSpace Γ]
    [NonarchimedeanGroup Γ] {X : Type uF} [Group X] [TopologicalSpace X]
    {N L N' L' : Subgroup Γ} (hN : N = N') (hL : L = L')
    (hNc : IsClosed (N : Set Γ)) (hLN : L ≤ Subgroup.normalizer (N : Set Γ))
    (hNc' : IsClosed (N' : Set Γ)) (hLN' : L' ≤ Subgroup.normalizer (N' : Set Γ))
    (e : X ≃ₜ* L) (e' : X ≃ₜ* L') (he : ∀ x, (e x : Γ) = (e' x : Γ))
    (V : SmoothRep.{0, uF, uV} ℂ Γ) :
    SmoothRep.pullback e ((normalizedJacquetFunctor N L hNc hLN).obj V) ≅
      SmoothRep.pullback e' ((normalizedJacquetFunctor N' L' hNc' hLN').obj V) := by
  subst hN
  subst hL
  have : e = e' := by
    ext x
    exact he x
  subst this
  exact Iso.refl _

section PointTransport

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H K : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left] [IsAffine K.X.left]
  [LocallyOfFiniteType H.X.hom]

local instance bernsteinGeomTransportTopology (M : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine M.X.left] : TopologicalSpace (GroupScheme.rationalPoints M) :=
  rationalPointTopology F M.X

/-- A point homeomorphism that agrees pointwise with the point map of an algebraic
isomorphism `φ` transports inertia equivalence exactly as `rationalIsoPullback`. -/
theorem isRationalInertiaRelated_rationalIsoPullback_of_pointwise (φ : K ≅ H)
    (e : GroupScheme.rationalPoints K ≃ₜ* GroupScheme.rationalPoints H)
    (he : ∀ x, e x = GroupScheme.rationalPoints.map φ.hom x)
    {A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints H)}
    {B : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints K)}
    (hrel : IsRationalInertiaRelated H A (SmoothRep.pullback e.symm B)) :
    IsRationalInertiaRelated H A (rationalIsoPullback φ.symm B) := by
  have hpt (x : GroupScheme.rationalPoints H) : e.symm x = rationalPointIso φ.symm x := by
    rw [ContinuousMulEquiv.symm_apply_eq, he]
    exact ((rationalPointIso φ).apply_symm_apply x).symm
  let iso : SmoothRep.pullback e.symm B ≅ rationalIsoPullback φ.symm B :=
    SmoothRep.mkIso (equivOfRepresentationEq (by
      ext x v
      change B.representation (e.symm x) v = B.representation (rationalPointIso φ.symm x) v
      rw [hpt]))
  exact hrel.trans (IsRationalInertiaRelated.of_iso iso)

end PointTransport

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinGeomExclInstance1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance bernsteinGeomExclInstance2 : T2Space F :=
  Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
local instance bernsteinGeomExclInstance3 : TopologicalSpace (rationalPoints G) := pointTopology
local instance bernsteinGeomExclInstance4 (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance bernsteinGeomExclInstance5 (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance bernsteinGeomExclInstance6 (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance bernsteinGeomExclInstance7 (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

local instance bernsteinGeomExclInstance8 (I : Finset (SimpleRoot i ν)) :
    LocallyCompactSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  bernsteinRepresentedCuspInstance7 i ν I

local instance bernsteinGeomExclInstance9 (I : Finset (SimpleRoot i ν)) :
    NonarchimedeanGroup (rationalPoints (bernsteinLeviScheme i ν I)) :=
  bernsteinRepresentedCuspInstance8 i ν I

/-- Actual represented normalized Jacquet restriction to the original standard
rational Levi. -/
def bernsteinStandardRepresentedJacquetFunctor (I : Finset (SimpleRoot i ν)) :
    SmoothRep.{0, uF, uV} ℂ (rationalPoints G) ⥤
      SmoothRep.{0, uF, uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I)) :=
  let h := bernsteinStandardRepresentativesGeometric i ν family I
  RepresentedParabolic.leviJacquetFunctor
    (Standard.parabolicHom i ν (rootSet i ν I))
    (Standard.leviToParabolic i ν (rootSet i ν I))
    (Standard.unipotentToParabolic i ν (rootSet i ν I))
    h.1 h.2.2.1 h.2.1 h.2.2.2

/-- The represented and literal standard Jacquet modules agree on the original
standard rational Levi. -/
def bernsteinStandardRepresentedJacquetIso (I : Finset (SimpleRoot i ν))
    (V : SmoothRep.{0, uF, uV} ℂ (rationalPoints G)) :
    (bernsteinStandardRepresentedJacquetFunctor i ν family I).obj V ≅
      bernsteinSchemeJacquet i ν family I V := by
  let p := Standard.parabolicHom i ν (rootSet i ν I)
  let l := Standard.leviToParabolic i ν (rootSet i ν I)
  let hgeom := bernsteinStandardRepresentativesGeometric i ν family I
  have he (x : rationalPoints (bernsteinLeviScheme i ν I)) :
      (RepresentedParabolic.leviPointsEquiv p l hgeom.1 hgeom.2.1 x :
        rationalPoints G) = (leviRationalPointHomeomorph i ν I x : rationalPoints G) := by
    rw [RepresentedParabolic.leviPointsEquiv_apply_coe,
      leviRationalPointHomeomorph_apply_coe]
    change rationalPoints.map
      (Standard.leviToParabolic i ν (rootSet i ν I) ≫
        Standard.parabolicHom i ν (rootSet i ν I)) x = _
    rw [Standard.leviToParabolic_comp]
  let r := Standard.unipotentToParabolic i ν (rootSet i ν I)
  let c := pullbackNormalizedJacquetIsoOfEq
    (Γ := rationalPoints G)
    (X := rationalPoints (bernsteinLeviScheme i ν I))
    (N := RepresentedParabolic.pointImage (r ≫ p))
    (L := RepresentedParabolic.pointImage (l ≫ p))
    (N' := unipotent i ν I) (L' := levi i ν I)
    (standardCompression_unipotentPoints i ν I) (standardCompression_leviPoints i ν I)
    (RepresentedParabolic.isClosed_pointImage_comp p r hgeom.1.isClosedSubgroup
      hgeom.2.2.1.1.isClosedSubgroup)
    (RepresentedParabolic.pointImage_le_normalizer p l r hgeom.2.2.1)
    (family.closedUnipotent I) (family.decomposition I).levi_le_normalizer
    (RepresentedParabolic.leviPointsEquiv p l hgeom.1 hgeom.2.1)
    (leviRationalPointHomeomorph i ν I) he V
  dsimp only [bernsteinStandardRepresentedJacquetFunctor,
    RepresentedParabolic.leviJacquetFunctor, RepresentedParabolic.jacquetFunctor,
    Functor.comp_obj, SmoothRep.pullbackFunctor, bernsteinSchemeJacquet]
  exact c

omit [LocallyOfFiniteType G.X.hom] in
set_option maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency.types true in
/-- Conjugate Levi case: an irreducible subquotient of the represented Jacquet
module of represented induction of a supercuspidal `τ` is a conjugate of a
subquotient of `τ`. -/
private theorem bernsteinConjugateConstituent (I J : Finset (SimpleRoot i ν))
    (τ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I)))
    (hcusp : RepresentedParabolic.IsSupercuspidal τ)
    (σ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν J)))
    (hσ : σ.IsIrreducible)
    (h1 : SmoothRep.IsSubquotient σ
      ((bernsteinStandardRepresentedJacquetFunctor i ν family J).obj
        ((bernsteinStandardRepresentedInductionFunctor i ν family I).obj τ)))
    (hconj : ∃ (g : rationalPoints G)
      (φ : bernsteinLeviScheme i ν I ≅ bernsteinLeviScheme i ν J),
      φ.hom ≫ Standard.leviToParabolic i ν (rootSet i ν J) ≫
          Standard.parabolicHom i ν (rootSet i ν J) =
        Standard.leviToParabolic i ν (rootSet i ν I) ≫
          Standard.parabolicHom i ν (rootSet i ν I) ≫ (G.innerIso g).hom) :
    ∃ (z : rationalPoints G) (φ : bernsteinLeviScheme i ν J ≅ bernsteinLeviScheme i ν I)
      (e : rationalPoints (bernsteinLeviScheme i ν J) ≃ₜ*
        rationalPoints (bernsteinLeviScheme i ν I)),
      φ.hom ≫ Standard.leviToParabolic i ν (rootSet i ν I) ≫
          Standard.parabolicHom i ν (rootSet i ν I) =
        Standard.leviToParabolic i ν (rootSet i ν J) ≫
          Standard.parabolicHom i ν (rootSet i ν J) ≫ (G.innerIso z).hom ∧
      (∀ x, e x = rationalPoints.map φ.hom x) ∧
      SmoothRep.IsSubquotient σ (SmoothRep.pullback e τ) := by
  let A := bernsteinStandardRepresentativesGeometric i ν family I
  let B := bernsteinStandardRepresentativesGeometric i ν family J
  have hfull := RepresentedParabolic.leviJacquetInduction_conjugateConstituent.{uF, uV}
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
      B.1 B.2.1 B.2.2.1 B.2.2.2 hconj
  have hspec := hfull τ hcusp σ hσ
  dsimp only [bernsteinStandardRepresentedJacquetFunctor,
    bernsteinStandardRepresentedInductionFunctor, bernsteinLeviScheme,
    RepresentedParabolic.leviPointTopology, RepresentedParabolic.leviAmbientPointTopology,
    bernsteinGeomExclInstance3, bernsteinGeomExclInstance7] at h1 hspec ⊢
  exact hspec h1

omit [LocallyOfFiniteType G.X.hom] in
set_option maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency.types true in
/-- Non-conjugate Levi case: an irreducible subquotient of the represented Jacquet
module of represented induction of a supercuspidal `τ` along a non-conjugate standard
Levi is not supercuspidal (VI.5.3 (ii), from the represented geometric lemma and
VI.5.2). -/
private theorem bernsteinNonConjugateExclusion
    (hind : RepresentedParabolic.LeviInductionNoSupercuspidalSubquotientStatement.{uF, max uF uV})
    (I J : Finset (SimpleRoot i ν))
    (τ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I)))
    (hcusp : RepresentedParabolic.IsSupercuspidal τ)
    (σ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν J)))
    (hσ : σ.IsIrreducible) (hσsc : RepresentedParabolic.IsSupercuspidal σ)
    (h1 : SmoothRep.IsSubquotient σ
      ((bernsteinStandardRepresentedJacquetFunctor i ν family J).obj
        ((bernsteinStandardRepresentedInductionFunctor i ν family I).obj τ)))
    (hconj : ¬ ∃ (g : rationalPoints G)
      (φ : bernsteinLeviScheme i ν I ≅ bernsteinLeviScheme i ν J),
      φ.hom ≫ Standard.leviToParabolic i ν (rootSet i ν J) ≫
          Standard.parabolicHom i ν (rootSet i ν J) =
        Standard.leviToParabolic i ν (rootSet i ν I) ≫
          Standard.parabolicHom i ν (rootSet i ν I) ≫ (G.innerIso g).hom) :
    False := by
  let A := bernsteinStandardRepresentativesGeometric i ν family I
  let B := bernsteinStandardRepresentativesGeometric i ν family J
  have hfull :=
    RepresentedParabolic.leviJacquetInductionNoSupercuspidal_of_geometricLemma.{uF, max uF uV}
      RepresentedParabolic.representedGeometricLemma hind
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
      B.1 B.2.1 B.2.2.1 B.2.2.2 hconj
  have hspec := hfull τ hcusp σ hσ
  dsimp only [bernsteinStandardRepresentedJacquetFunctor,
    bernsteinStandardRepresentedInductionFunctor, bernsteinLeviScheme,
    RepresentedParabolic.leviPointTopology, RepresentedParabolic.leviAmbientPointTopology,
    bernsteinGeomExclInstance3, bernsteinGeomExclInstance7] at h1 hspec hσsc
  exact hspec h1 hσsc

set_option maxHeartbeats 200000 in
/-- Conjugate Levi case, transport step: a conjugating isomorphism `φ : M_b ≅ M_a`
compatible with the two standard Levi embeddings, together with inertia equivalence
of `a.representation` with the transport of `b.representation`, makes the two
cuspidal data inertia-related. -/
private theorem bernsteinInertiaRelated_of_conjugateConstituent
    (a b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (z : rationalPoints G)
    (φ : bernsteinLeviScheme i ν b.roots ≅ bernsteinLeviScheme i ν a.roots)
    (e : rationalPoints (bernsteinLeviScheme i ν b.roots) ≃ₜ*
      rationalPoints (bernsteinLeviScheme i ν a.roots))
    (hφ : φ.hom ≫ Standard.leviToParabolic i ν (rootSet i ν a.roots) ≫
          Standard.parabolicHom i ν (rootSet i ν a.roots) =
        Standard.leviToParabolic i ν (rootSet i ν b.roots) ≫
          Standard.parabolicHom i ν (rootSet i ν b.roots) ≫ (G.innerIso z).hom)
    (he : ∀ x, e x = rationalPoints.map φ.hom x)
    (hrel : IsRationalInertiaRelated (bernsteinLeviScheme i ν a.roots) a.representation
      (SmoothRep.pullback e.symm b.representation)) :
    IsBernsteinInertiaRelated i ν family a b := by
  let c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν b.roots))
      (Standard.leviHom i ν (rootSet i ν a.roots)) :=
    ⟨z, φ, by
      rw [← Standard.leviToParabolic_comp, ← Standard.leviToParabolic_comp, Category.assoc]
      exact hφ.symm⟩
  exact ⟨c.symm, isRationalInertiaRelated_rationalIsoPullback_of_pointwise φ e he hrel⟩

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency.types true in
/-- Renard VI.7.2, geometric step of the Bernstein decomposition: if `τ` is a
supercuspidal smooth representation of the standard Levi `M_a(F)` all of whose
irreducible subquotients are inertia-related to the cuspidal datum `a`, then for every
cuspidal datum `b` not inertia-related to `a`, the representation of `b` is not a
subquotient of the normalized Jacquet module along `P_b` of `i_{P_a}^G τ`. The
non-conjugate Levi case uses Renard VI.5.2 in its represented form `hind`. -/
theorem bernsteinJacquetExclusion_of_inertiaBlock_supercuspidal
    (hind : RepresentedParabolic.LeviInductionNoSupercuspidalSubquotientStatement.{uF, max uF uV})
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (τ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν a.roots)))
    (hτ : rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots) a.representation τ)
    (hcusp : RepresentedParabolic.IsSupercuspidal τ) :
    BernsteinJacquetExclusion i ν family a
      ((normalizedInductionFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj (bernsteinLiteralLeviRep i ν a.roots τ)) := by
  intro b hab hbV
  have h0 := (isSubquotient_bernsteinSchemeJacquet_iff i ν family b.roots b.representation
    _).mpr hbV
  have h1 : SmoothRep.IsSubquotient b.representation
      ((bernsteinStandardRepresentedJacquetFunctor i ν family b.roots).obj
        ((bernsteinStandardRepresentedInductionFunctor i ν family a.roots).obj τ)) :=
    (h0.of_iso_right (bernsteinStandardRepresentedJacquetIso i ν family b.roots _).symm).of_iso_right
      ((bernsteinStandardRepresentedJacquetFunctor i ν family b.roots).mapIso
        (bernsteinStandardRepresentedInductionIso i ν family a.roots τ).symm)
  by_cases hconj : ∃ (g : rationalPoints G)
      (φ : bernsteinLeviScheme i ν a.roots ≅ bernsteinLeviScheme i ν b.roots),
      φ.hom ≫ Standard.leviToParabolic i ν (rootSet i ν b.roots) ≫
          Standard.parabolicHom i ν (rootSet i ν b.roots) =
        Standard.leviToParabolic i ν (rootSet i ν a.roots) ≫
          Standard.parabolicHom i ν (rootSet i ν a.roots) ≫ (G.innerIso g).hom
  · have hc := bernsteinConjugateConstituent.{uF, uV} i ν family a.roots b.roots τ hcusp
      b.representation b.irreducible ?h1 hconj
    case h1 => exact h1
    obtain ⟨z, φ, e, hφ, he, h2⟩ := hc
    have h3 := (SmoothRep.subquotient_pullback_right_iff e).mp h2
    have hirr : (SmoothRep.pullback e.symm b.representation).IsIrreducible :=
      (SmoothRep.isIrreducible_pullbackFunctor_obj_iff e.symm b.representation).mpr
        b.irreducible
    refine hab (bernsteinInertiaRelated_of_conjugateConstituent i ν family a b z φ e hφ he ?_)
    refine hτ (SmoothRep.pullback e.symm b.representation) ?_ ?_
    · exact hirr
    · exact h3
  · refine bernsteinNonConjugateExclusion.{uF, uV} i ν family hind a.roots b.roots τ hcusp
      b.representation b.irreducible ?_ ?_ ?_
    · exact b.isSupercuspidal i ν family
    · exact h1
    · exact hconj

set_option linter.defProp false in
/-- The geometric step of Renard VI.7.2 for one standard family, as a declaration whose
type is the implication: represented VI.5.2 gives the Bernstein Jacquet exclusion for
every supercuspidal inducing representation in the same-Levi inertia block of a
cuspidal datum. -/
def bernsteinJacquetExclusionOfInertiaBlockSupercuspidal
    (hind : RepresentedParabolic.LeviInductionNoSupercuspidalSubquotientStatement.{uF, max uF uV}) :
    ∀ (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
      (τ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν a.roots))),
      rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots) a.representation τ →
      RepresentedParabolic.IsSupercuspidal τ →
        BernsteinJacquetExclusion i ν family a
          ((normalizedInductionFunctor (family.decomposition a.roots)
            (family.closedUnipotent a.roots)).obj (bernsteinLiteralLeviRep i ν a.roots τ)) :=
  bernsteinJacquetExclusion_of_inertiaBlock_supercuspidal.{uF, uV} i ν family hind

end Langlands.CuspidalSupport
