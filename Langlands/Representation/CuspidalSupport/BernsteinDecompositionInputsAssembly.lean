import Langlands.Representation.CuspidalSupport.BernsteinInertiaBlockSupercuspidality
import Langlands.Representation.CuspidalSupport.BernsteinFiniteEmbeddingAssembly
import Langlands.Representation.CuspidalSupport.BernsteinDecompositionReduction
import Langlands.Representation.CuspidalSupport.BernsteinSupportAssociationReduction
import Langlands.Representation.CuspidalSupport.BernsteinBlockCharacterizationReduction
import Langlands.Representation.CuspidalSupport.RationalCuspidalInducedEmbeddingFromWhole

/-! # Assembling the Bernstein decomposition from its named statement inputs -/

noncomputable section

set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

section Family

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinInputsAssemblyAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance bernsteinInputsAssemblyFieldT2 : T2Space F :=
  Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
local instance bernsteinInputsAssemblyTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology
local instance bernsteinInputsAssemblyLeviClosedImmersion (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance bernsteinInputsAssemblyLeviAffine (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance bernsteinInputsAssemblyLeviFiniteType (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance bernsteinInputsAssemblyLeviTopology (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

local instance bernsteinInputsAssemblyLeviLocallyCompact (I : Finset (SimpleRoot i ν)) :
    LocallyCompactSpace (rationalPoints (bernsteinLeviScheme i ν I)) := by
  have := (isClosed_levi i ν I).locallyCompactSpace
  exact (leviRationalPointHomeomorph i ν I).toHomeomorph.isClosedEmbedding.locallyCompactSpace

local instance bernsteinInputsAssemblyLeviNonarchimedean (I : Finset (SimpleRoot i ν)) :
    NonarchimedeanGroup (rationalPoints (bernsteinLeviScheme i ν I)) := by
  let e := leviRationalPointHomeomorph i ν I
  have : IsTopologicalGroup (rationalPoints (bernsteinLeviScheme i ν I)) :=
    Topology.IsInducing.isTopologicalGroup e.toMulEquiv e.toHomeomorph.isInducing
  exact NonarchimedeanGroup.nonarchimedean_of_emb e.symm.toMulEquiv.toMonoidHom
    e.symm.toHomeomorph.isOpenEmbedding

/-- The geometric exclusion step for a family follows once it is known for
supercuspidal inducing objects of the same-Levi inertia blocks: every such
inducing object is supercuspidal by the whole-category decomposition
(Renard VI.3.5). -/
theorem bernsteinInducedInertiaJacquetExclusion_of_supercuspidal
    (hwhole : RationalWholeCuspidalCategoryDecompositionStatement.{uF, max uF uV})
    (hsc : ∀ (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
      (τ : SmoothRep.{0, uF, max uF uV} ℂ
        (rationalPoints (bernsteinLeviScheme i ν a.roots))),
      rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots) a.representation τ →
      RepresentedParabolic.IsSupercuspidal τ →
        BernsteinJacquetExclusion i ν family a
          ((normalizedInductionFunctor (family.decomposition a.roots)
            (family.closedUnipotent a.roots)).obj (bernsteinLiteralLeviRep i ν a.roots τ))) :
    BernsteinInducedInertiaJacquetExclusion.{uF, uV} i ν family := by
  intro a τ hτ
  have hcusp := isSupercuspidal_of_rationalInertiaBlockProperty i ν family hwhole a τ hτ
  exact hsc a τ hτ hcusp

/-- The category decomposition of one standard family from represented VI.5.4,
the two VI.3.5 whole-category statements and the family's geometric exclusion. -/
theorem bernsteinCategoryDecomposition_of_statementInputs
    (hAssociate :
      RepresentedParabolic.LeviSupercuspidalInductionAssociationStatement.{uF, max uF uV})
    (hdecomp : RationalCuspidalInertiaProductDecompositionStatement.{uF, max uF uV})
    (hwhole : RationalWholeCuspidalCategoryDecompositionStatement.{uF, uV})
    (hGeom : BernsteinInducedInertiaJacquetExclusion.{uF, uV} i ν family) :
    Renard.IsCategoryDecomposition
      (fun c : BernsteinInertialClass.{uF, max uF uV} i ν family =>
        bernsteinBlockProperty.{uF, uV} i ν family c) :=
  bernsteinCategoryDecomposition_of_representationInputs i ν family
    (bernsteinInertialSupportUniqueness_of_represented i ν family hAssociate) hdecomp hGeom
    (rationalCuspidalInducedEmbedding_of_wholeStatement hwhole)

set_option linter.defProp false in
/-- The reduction of one family's Bernstein category decomposition to the
named statement inputs and its geometric exclusion, as a declaration whose
type is the implication. -/
def bernsteinCategoryDecompositionOfStatementInputs
    (hAssociate :
      RepresentedParabolic.LeviSupercuspidalInductionAssociationStatement.{uF, max uF uV})
    (hdecomp : RationalCuspidalInertiaProductDecompositionStatement.{uF, max uF uV})
    (hwhole : RationalWholeCuspidalCategoryDecompositionStatement.{uF, uV}) :
    BernsteinInducedInertiaJacquetExclusion.{uF, uV} i ν family →
      Renard.IsCategoryDecomposition
        (fun c : BernsteinInertialClass.{uF, max uF uV} i ν family =>
          bernsteinBlockProperty.{uF, uV} i ν family c) :=
  bernsteinCategoryDecomposition_of_statementInputs i ν family hAssociate hdecomp hwhole

end Family

end Langlands.CuspidalSupport
