import Langlands.Representation.Category.SuppliedCofanComposition
import Langlands.Representation.CuspidalSupport.BernsteinSupportJacquetPresentation
import Langlands.Representation.CuspidalSupport.BernsteinRepresentedCuspidality
import Langlands.Representation.CuspidalSupport.RationalCuspidalSubquotients
import Langlands.Representation.CuspidalSupport.RationalWholeCuspidalDecompositionStatement
import Langlands.Representation.Aubert.General.InductionCoproducts
import Langlands.Representation.Aubert.General.InertiaInductionCompression
import Langlands.CategoryTheory.Renard.CategoryDecompositionSimpleClassesProof

/-! # Actual induced Levi inertia cofans for Bernstein decomposition -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

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
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinFiniteAssemblyAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance bernsteinFiniteAssemblyFieldT2 : T2Space F :=
  Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
local instance bernsteinFiniteAssemblyAmbientTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology
local instance bernsteinFiniteAssemblyLeviClosedImmersion (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance bernsteinFiniteAssemblyLeviAffine (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance bernsteinFiniteAssemblyLeviFiniteType (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance bernsteinFiniteAssemblyLeviTopology (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

local instance bernsteinFiniteAssemblyLeviLocalCompact (I : Finset (SimpleRoot i ν)) :
    LocallyCompactSpace (rationalPoints (bernsteinLeviScheme i ν I)) := by
  have := (isClosed_levi i ν I).locallyCompactSpace
  exact (leviRationalPointHomeomorph i ν I).toHomeomorph.isClosedEmbedding.locallyCompactSpace

local instance bernsteinFiniteAssemblyLeviNonarchimedean (I : Finset (SimpleRoot i ν)) :
    NonarchimedeanGroup (rationalPoints (bernsteinLeviScheme i ν I)) := by
  let e := leviRationalPointHomeomorph i ν I
  have : IsTopologicalGroup (rationalPoints (bernsteinLeviScheme i ν I)) :=
    Topology.IsInducing.isTopologicalGroup e.toMulEquiv e.toHomeomorph.isInducing
  exact NonarchimedeanGroup.nonarchimedean_of_emb e.symm.toMulEquiv.toMonoidHom
    e.symm.toHomeomorph.isOpenEmbedding

/-- The actual induced maximal split torus of an actual standard Levi. -/
abbrev bernsteinLeviTorus (I : Finset (SimpleRoot i ν)) :=
  standardLeviTorusFactor i ν (rootSet i ν I)
    (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))

include family in
omit [LocallyOfFiniteType G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- Each actual standard Levi carries its intrinsic Bernstein standard family.
All its structure follows from the published geometric theorems. -/
theorem bernsteinLeviStandardFamily (I : Finset (SimpleRoot i ν)) :
    BernsteinStandardFamily (bernsteinLeviTorus i ν I) ν := by
  have := family.maximalSplitTorus.isSplitSubtorus.mono
  let hL := (bernsteinStandardRepresentativesGeometric i ν family I).2.1.isConnectedReductive
  have hj : IsMaximalSplitTorus (bernsteinLeviTorus i ν I) :=
    family.maximalSplitTorus.isMaximalSplitTorus_standardLeviTorusFactor
      i ν (rootSet i ν I) (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I))
  have := hj.isSplitSubtorus.mono
  have hνj : IsGenericCocharacter (bernsteinLeviTorus i ν I) ν :=
    (standardLeviStandardFamilies dynamicLie standardCocharacter F G
      family.connectedReductive T i family.maximalSplitTorus ν
      family.genericCocharacter (rootSet i ν I) (rootSet_subset i ν I)
      (bernsteinLeviScheme i ν I) hL (Standard.leviHom i ν (rootSet i ν I))
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I))).2.1
  let hRoots := relativeRootSystem F (bernsteinLeviScheme i ν I) hL T
    (bernsteinLeviTorus i ν I) hj
  let := simpleRelativeRootFintype (bernsteinLeviTorus i ν I) hRoots hj.isSplitSubtorus.1 ν
  exact ⟨hL, hj, hνj, inferInstance,
    isSemidirectDecomposition_of_standardCocharacterStatement
      _ ν standardCocharacter hL hj hνj,
    fun J => isClosed_unipotent _ ν J,
    fun J => isClosed_levi _ ν J,
    isSemidirectDecomposition_in_levi _ ν standardLeviIntersection hL hj hνj⟩

/-- Actual Bernstein-labelled summands, actual legs and their coproduct
universal property at a fixed saturated-carrier vertex. -/
structure BernsteinLabelledCofanPresentation
    (W : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)) where
  index : Type ((max uF uV) + 1)
  summand : index → SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)
  leg : ∀ k, summand k ⟶ W
  isColimit : IsColimit (Cofan.mk W leg)
  label : index → BernsteinInertialClass.{uF, max uF uV} i ν family
  block : ∀ k, bernsteinSaturatedBlockProperty i ν family (label k) (summand k)

private theorem inducedCuspidalBlockLabel
    (hGeom : BernsteinInducedInertiaJacquetExclusion.{uF, uV} i ν family)
    (I : Finset (SimpleRoot i ν))
    (π D : SmoothRep.{0, uF, max uF uV} ℂ
      (rationalPoints (bernsteinLeviScheme i ν I)))
    (hπ : π.IsIrreducible)
    (hc : Langlands.Aubert.General.IsLeviCuspidal
      (parabolic i ν) (levi i ν) (unipotent i ν)
      family.closedUnipotent I (family.closedLevi I) (family.leviDecomposition I)
      (bernsteinLiteralLeviRep i ν I π))
    (hD : rationalInertiaBlockProperty (bernsteinLeviScheme i ν I) π D) :
    ∃ a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
      bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
        ((rationalInertiaInductionFunctor (bernsteinLeviScheme i ν I)
          (family.decomposition I) (family.closedUnipotent I)
          (leviRationalPointHomeomorph i ν I).symm).obj D) := by
  let a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family := ⟨I, π, hπ, hc⟩
  exact ⟨a, bernsteinJacquetExclusion_implies_block.{uF, uV} i ν family a _
    (hGeom a D hD)⟩

/-- The intrinsic cuspidal inertia decomposition of a literal cuspidal Levi
object induces an actual Bernstein-labelled coproduct. The decomposition and
arbitrary-inertia geometric exclusion remain explicit inputs. -/
def bernsteinInducedCuspidalCofan
    (hdecomp : RationalCuspidalInertiaProductDecompositionStatement.{uF, max uF uV})
    (hGeom : BernsteinInducedInertiaJacquetExclusion.{uF, uV} i ν family)
    (I : Finset (SimpleRoot i ν))
    (τ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν I))
    (hτ : Langlands.Aubert.General.IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
      family.closedUnipotent I (family.closedLevi I) (family.leviDecomposition I) τ) :
    BernsteinLabelledCofanPresentation i ν family
      ((normalizedInductionFunctor (family.decomposition I)
        (family.closedUnipotent I)).obj τ) := by
  classical
  apply Classical.choice
  let L := bernsteinLeviScheme i ν I
  let : T2Space (rationalPoints L) := rationalPoint_t2Space F L
  let j := bernsteinLeviTorus i ν I
  let fam := bernsteinLeviStandardFamily i ν family I
  let := fam.finiteSimpleRoots
  let := Fintype.ofFinite (SimpleRoot j ν)
  have := family.maximalSplitTorus.isSplitSubtorus.mono
  let := compactSpace_leftQuotient_parabolic i ν
    BruhatTits.dynamicParabolicQuotientCompact standardCocharacter
    family.connectedReductive family.maximalSplitTorus family.genericCocharacter I
  let A := SmoothRep.pullback (leviRationalPointHomeomorph i ν I) τ
  have hA : IsCuspidal (parabolic j ν) (levi j ν) (unipotent j ν)
      fam.decomposition fam.closedUnipotent A :=
    (rationalLeviCuspidalityTransport dynamicLie standardCocharacter
      F G family.connectedReductive T i family.maximalSplitTorus ν
      family.genericCocharacter I fam.connectedReductive family.closedUnipotent
      fam.closedUnipotent (family.closedLevi I) (family.leviDecomposition I)
      fam.decomposition τ).mpr hτ
  have hall := (rationalAllCuspidalSubquotientProperty_iff_isCuspidal L j ν
    standardCocharacter fam.connectedReductive fam.maximalSplitTorus fam.genericCocharacter
    fam.decomposition fam.closedUnipotent A).mpr hA
  have hsplit : IsRationalCuspidalInertiaProductDecomposition.{uF, max uF uV}
      L j ν fam.decomposition fam.closedUnipotent :=
    hdecomp F L fam.connectedReductive T j fam.maximalSplitTorus ν fam.genericCocharacter
      standardCocharacter (relativeRootSystem F L fam.connectedReductive T j fam.maximalSplitTorus)
      fam.closedUnipotent
  obtain ⟨B, legs, hB, ⟨hs⟩⟩ := hsplit.1 A
  let s := Cofan.mk A legs
  have hzero : IsZero (B none) := by
    apply (SmoothRep.isZero_iff_subsingleton _).mpr
    apply not_nontrivial_iff_subsingleton.mp
    intro hne
    have : Mono (legs none) :=
      Renard.CategoryDecompositionSimpleClassesProof.cofan_leg_mono hs none
    have hsub : SmoothRep.IsSubquotient (B none) A :=
      SmoothRep.IsSubrepresentation.isSubquotient
        ⟨legs none, (SmoothRep.mono_iff_injective _).mp inferInstance⟩
    exact hB none (B none) hne
      (SmoothRep.IsSubrepresentation.isSubquotient ⟨𝟙 _, Function.injective_id⟩)
      (hall (B none) hsub)
  let Tind := rationalInertiaInductionFunctor L
    (family.decomposition I) (family.closedUnipotent I)
    (leviRationalPointHomeomorph i ν I).symm
  have hcop (K : Type (max uF uV)) :
      PreservesColimitsOfShape (Discrete K) Tind := by
    have : PreservesColimitsOfShape (Discrete K)
        (normalizedInductionFunctor.{uF, max uF uV}
          (family.decomposition I) (family.closedUnipotent I)) :=
      normalizedInductionFunctor_preservesCoproducts.{uF, max uF uV, 0}
        (family.decomposition I) (family.closedUnipotent I)
    dsimp only [Tind, rationalInertiaInductionFunctor]
    exact comp_preservesColimitsOfShape _ _
  let inner := Langlands.Cofan.someCofan s
  have hinner : IsColimit inner := Langlands.Cofan.someCofanIsColimit s hs hzero
  have hmap : IsColimit (Cofan.mk (Tind.obj A)
      (fun c => Tind.map (legs (some c)))) :=
    SmoothRep.mapCofanIsColimit_of_carrierCoproducts Tind hcop
      (fun c => B (some c)) inner hinner
  let cancel : Tind.obj A ≅
      (normalizedInductionFunctor (family.decomposition I) (family.closedUnipotent I)).obj τ :=
    (normalizedInductionFunctor (family.decomposition I) (family.closedUnipotent I)).mapIso
      (SmoothRep.pullbackSymmIso (leviRationalPointHomeomorph i ν I) τ)
  have hlabels (c : RationalCuspidalInertiaClass.{uF, max uF uV}
      L j ν fam.decomposition fam.closedUnipotent) :
      ∃ a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
        bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
          (Tind.obj (B (some c))) := by
    obtain ⟨π, hπ, hc, hπc⟩ := c.property
    have hblock : rationalInertiaBlockProperty L π (B (some c)) := by
      intro D hD hDB
      exact (rationalIrreducibleInertiaClass_eq_iff L π D hπ hD).mp
        (hπc.trans (hB (some c) D hD hDB).symm)
    have hπlit : Langlands.Aubert.General.IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
        family.closedUnipotent I (family.closedLevi I) (family.leviDecomposition I)
        (bernsteinLiteralLeviRep i ν I π) := by
      apply (rationalLeviCuspidalityTransport dynamicLie standardCocharacter
        F G family.connectedReductive T i family.maximalSplitTorus ν
        family.genericCocharacter I fam.connectedReductive family.closedUnipotent
        fam.closedUnipotent (family.closedLevi I) (family.leviDecomposition I)
        fam.decomposition _).mp
      exact hc.of_iso (SmoothRep.pullbackSymmIso
        (leviRationalPointHomeomorph i ν I).symm π)
    exact inducedCuspidalBlockLabel i ν family hGeom I π (B (some c)) hπ hπlit hblock
  choose data hdata using hlabels
  refine ⟨⟨_, (fun c => Tind.obj (B (some c))),
    (fun c => Tind.map (legs (some c)) ≫ cancel.hom), ?_,
    (fun c => bernsteinInertialClass i ν family (data c)), hdata⟩⟩
  exact IsColimit.ofIsoColimit hmap
    (Cocone.ext cancel (by intro c; simp))

end Langlands.CuspidalSupport
