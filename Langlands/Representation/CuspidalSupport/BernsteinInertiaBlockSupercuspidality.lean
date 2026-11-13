import Langlands.Representation.CuspidalSupport.BernsteinLeviCuspidalSplitting
import Langlands.Representation.CuspidalSupport.BernsteinJacquetInertiaExclusion
import Langlands.Representation.CuspidalSupport.BernsteinRepresentedCuspidality
import Langlands.Representation.Category.IrreducibleSubquotientExistence
import Langlands.Representation.Aubert.General.RationalRootAssociationCuspidalityTransport

/-! # Same-Levi inertia blocks of a Bernstein datum are supercuspidal -/

noncomputable section

set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinInertiaBlockCuspInstance1 : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance bernsteinInertiaBlockCuspInstance2 : T2Space F :=
  Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
local instance bernsteinInertiaBlockCuspInstance3 : TopologicalSpace (rationalPoints G) :=
  pointTopology
local instance bernsteinInertiaBlockCuspInstance4 (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance bernsteinInertiaBlockCuspInstance5 (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance bernsteinInertiaBlockCuspInstance6 (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

local instance bernsteinInertiaBlockCuspInstance7 (I : Finset (SimpleRoot i ν)) :
    LocallyCompactSpace (rationalPoints (bernsteinLeviScheme i ν I)) := by
  have := (isClosed_levi i ν I).locallyCompactSpace
  exact (leviRationalPointHomeomorph i ν I).toHomeomorph.isClosedEmbedding.locallyCompactSpace

local instance bernsteinInertiaBlockCuspInstance8 (I : Finset (SimpleRoot i ν)) :
    NonarchimedeanGroup (rationalPoints (bernsteinLeviScheme i ν I)) := by
  let e := leviRationalPointHomeomorph i ν I
  have : IsTopologicalGroup (rationalPoints (bernsteinLeviScheme i ν I)) :=
    Topology.IsInducing.isTopologicalGroup e.toMulEquiv e.toHomeomorph.isInducing
  exact NonarchimedeanGroup.nonarchimedean_of_emb e.symm.toMulEquiv.toMonoidHom
    e.symm.toHomeomorph.isOpenEmbedding

/-- Literal inside-Levi cuspidality of a representation of an actual standard
Levi implies vanishing of the Jacquet module for every proper actual
represented parabolic of that Levi. -/
theorem bernsteinLeviRep_isSupercuspidal_of_isLeviCuspidal
    (I : Finset (SimpleRoot i ν))
    (τ : SmoothRep.{0, uF, uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I)))
    (hτ : Langlands.Aubert.General.IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
      family.closedUnipotent I (family.closedLevi I) (family.leviDecomposition I)
      (bernsteinLiteralLeviRep i ν I τ)) :
    RepresentedParabolic.IsSupercuspidal τ := by
  classical
  let : Mono i.hom.hom.left := family.maximalSplitTorus.isSplitSubtorus.mono
  let hgeom := bernsteinStandardRepresentativesGeometric i ν family I
  let hL := hgeom.2.1.isConnectedReductive
  let j := standardLeviTorusFactor i ν (rootSet i ν I)
    (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
  have hj : IsMaximalSplitTorus j :=
    family.maximalSplitTorus.isMaximalSplitTorus_standardLeviTorusFactor
      i ν (rootSet i ν I) (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I))
  have hjmono := hj.isSplitSubtorus.mono
  let : Mono j.hom.hom.left := hjmono
  have hνj : IsGenericCocharacter j ν :=
    (standardLeviStandardFamilies dynamicLie standardCocharacter F G
      family.connectedReductive T i family.maximalSplitTorus ν
      family.genericCocharacter (rootSet i ν I) (rootSet_subset i ν I)
      (bernsteinLeviScheme i ν I) hL (Standard.leviHom i ν (rootSet i ν I))
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I))).2.1
  have hRoots := relativeRootSystem F (bernsteinLeviScheme i ν I) hL T j hj
  let := simpleRelativeRootFintype j hRoots hj.isSplitSubtorus.1 ν
  let hOwn := isSemidirectDecomposition_of_standardCocharacterStatement
    j ν standardCocharacter hL hj hνj
  have hUL (J : Finset (SimpleRoot j ν)) :
      IsClosed (unipotent j ν J : Set (rationalPoints (bernsteinLeviScheme i ν I))) :=
    isClosed_unipotent j ν J
  let A := bernsteinLiteralLeviRep i ν I τ
  have hc := (rationalLeviCuspidalityTransport dynamicLie standardCocharacter
    F G family.connectedReductive T i family.maximalSplitTorus ν
    family.genericCocharacter I hL family.closedUnipotent hUL
    (family.closedLevi I) (family.leviDecomposition I) hOwn A).mpr hτ
  have hc' : IsCuspidal (parabolic j ν) (levi j ν) (unipotent j ν)
      hOwn hUL τ :=
    hc.of_iso (SmoothRep.pullbackSymmIso (leviRationalPointHomeomorph i ν I).symm τ).symm
  exact RepresentedParabolic.isSupercuspidal_of_isCuspidal j ν
    parabolicDynamic smoothMaximalSplitTorusConjugacy hL hj hνj hRoots
    hOwn hUL τ hc'

variable [LocallyOfFiniteType G.X.hom]

local instance bernsteinInertiaBlockCuspInstance9 (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance

/-- Every object of the same-Levi inertia block of a Bernstein datum is
cuspidal for the literal proper standard parabolics of the Levi, given the
whole-category cuspidal/remainder decomposition (Renard VI.3.5). -/
theorem isLeviCuspidal_of_rationalInertiaBlockProperty
    (hwhole : RationalWholeCuspidalCategoryDecompositionStatement.{uF, max uF uV})
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (τ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν a.roots)))
    (hτ : rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots) a.representation τ) :
    Langlands.Aubert.General.IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
      family.closedUnipotent a.roots (family.closedLevi a.roots)
      (family.leviDecomposition a.roots) (bernsteinLiteralLeviRep i ν a.roots τ) := by
  classical
  let I := a.roots
  let e := leviRationalPointHomeomorph i ν I
  let A := bernsteinLiteralLeviRep i ν I τ
  let := (family.closedLevi I).locallyCompactSpace
  obtain ⟨Y, j, hYt, hYf, ⟨hc⟩⟩ :=
    bernsteinLeviCuspidalSplitting_of_wholeStatement i ν family hwhole I A
  let f : ∀ b, Y b ⟶ Y false := fun b => match b with
    | false => 𝟙 (Y false)
    | true => 0
  let p : A ⟶ Y false := Cofan.IsColimit.desc hc f
  have hjp : j false ≫ p = 𝟙 (Y false) := by
    change (Cofan.mk A j).inj false ≫ Cofan.IsColimit.desc hc f = _
    exact Cofan.IsColimit.fac hc f false
  have hYA : SmoothRep.IsSubquotient (Y false) A := by
    refine SmoothRep.IsSubrepresentation.isSubquotient ⟨j false, ?_⟩
    intro x y hxy
    have h := congrArg (SmoothRep.hom p) hxy
    have hx : SmoothRep.hom p (SmoothRep.hom (j false) x) = x := by
      change SmoothRep.hom (j false ≫ p) x = x
      rw [hjp]
      rfl
    have hy : SmoothRep.hom p (SmoothRep.hom (j false) y) = y := by
      change SmoothRep.hom (j false ≫ p) y = y
      rw [hjp]
      rfl
    rw [hx, hy] at h
    exact h
  have hzero : Subsingleton (Y false) := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    obtain ⟨D, hD, hDY⟩ := SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial (Y false)
    have hDA : SmoothRep.IsSubquotient D A := smoothSubquotientTransitivity ℂ _ _ _ _ hDY hYA
    let D' := SmoothRep.pullback e D
    have hD' : D'.IsIrreducible := (SmoothRep.isIrreducible_pullbackFunctor_obj_iff e D).mpr hD
    have cancelτ : SmoothRep.pullback e A ≅ τ :=
      SmoothRep.mkIso (equivOfRepresentationEq (by
        ext x v
        change τ.representation (e.symm (e x)) v = τ.representation x v
        rw [e.symm_apply_apply]))
    have hD'τ : SmoothRep.IsSubquotient D' τ := (hDA.pullback e).of_iso_right cancelτ
    have hrel := hτ D' hD' hD'τ
    have hcusp := isLeviCuspidal_bernsteinLiteralLeviRep_of_inertia i ν family I hrel a.cuspidal
    have cancelD : bernsteinLiteralLeviRep i ν I D' ≅ D := SmoothRep.pullbackSymmIso e D
    have hDn : Nontrivial D := by
      have := (Representation.irreducible_iff_isSimpleModule_asModule D.representation).mp hD
      exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (levi i ν I)) D.representation.asModule
    apply hYf D hDn hDY
    intro K
    let t := (SmoothRep.equivOfIso ((jacquetFunctor (family.leviDecomposition I K.val)
      ((family.closedUnipotent (leviIndex I K.val)).preimage continuous_subtype_val)).mapIso
        cancelD)).toLinearEquiv
    have hq := hcusp K
    exact t.symm.injective.subsingleton
  let g : ∀ b, Y b ⟶ Y true := fun b => match b with
    | false => 0
    | true => 𝟙 (Y true)
  let q : A ⟶ Y true := Cofan.IsColimit.desc hc g
  have hjq : j true ≫ q = 𝟙 (Y true) := by
    change (Cofan.mk A j).inj true ≫ Cofan.IsColimit.desc hc g = _
    exact Cofan.IsColimit.fac hc g true
  have hj0 : j false = 0 := by
    ext v
    rw [Subsingleton.elim v 0, map_zero, map_zero]
  have hqj : q ≫ j true = 𝟙 A := by
    apply Cofan.IsColimit.hom_ext hc
    intro b
    cases b
    · change j false ≫ (q ≫ j true) = j false ≫ 𝟙 A
      rw [hj0]
      simp
    · change j true ≫ (q ≫ j true) = j true ≫ 𝟙 A
      rw [← Category.assoc, hjq]
      simp
  let eA : A ≅ Y true := ⟨q, j true, hqj, hjq⟩
  intro K
  let t := (SmoothRep.equivOfIso ((jacquetFunctor (family.leviDecomposition I K.val)
    ((family.closedUnipotent (leviIndex I K.val)).preimage continuous_subtype_val)).mapIso
      eA)).toLinearEquiv
  have hq := hYt K
  exact t.injective.subsingleton

/-- Every object of the same-Levi inertia block of a Bernstein datum is
supercuspidal for every proper actual represented parabolic of its Levi,
given the whole-category decomposition (Renard VI.3.5). -/
theorem isSupercuspidal_of_rationalInertiaBlockProperty
    (hwhole : RationalWholeCuspidalCategoryDecompositionStatement.{uF, max uF uV})
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (τ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν a.roots)))
    (hτ : rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots) a.representation τ) :
    RepresentedParabolic.IsSupercuspidal τ := by
  have hc := isLeviCuspidal_of_rationalInertiaBlockProperty i ν family hwhole a τ hτ
  have h := bernsteinLeviRep_isSupercuspidal_of_isLeviCuspidal i ν family a.roots τ hc
  exact h

end Langlands.CuspidalSupport
