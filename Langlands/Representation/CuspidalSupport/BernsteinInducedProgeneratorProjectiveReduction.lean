import Langlands.Representation.CuspidalSupport.BernsteinInducedProgeneratorStatement
import Langlands.Representation.CuspidalSupport.BernsteinRepresentedInduction
import Langlands.Representation.CuspidalSupport.BernsteinRepresentedCuspidality
import Langlands.Representation.CuspidalSupport.BernsteinBlockCoproducts
import Langlands.Representation.CuspidalSupport.RationalSummandSmallProgeneratorReduction
import Langlands.Representation.Exponents.LeviSecondAdjointnessStatement
import Langlands.Representation.Exponents.LeviInductionDualityAdjunction
import Langlands.Representation.Exponents.RepresentedCompactRestrictionSupercuspidal
import Langlands.Representation.LanglandsClassification.OppositeLeviParabolic

/-! # Projectivity of the induced Bernstein progenerator (Renard VI.10.1)

Under Bernstein's second adjointness (VI.9.6) for the standard parabolic and its opposite,
normalized induction along a standard parabolic preserves projective objects. With the
compactness of the norm-kernel restriction of a supercuspidal representation (VI.2.1, which
needs the unproved `JointSpecialCompactBasisExistenceStatement`), `Π_D` is projective in
`M(M)`, hence `Π_Ω = i_P^G(Π_D)` is projective in `M(G)` and in every Bernstein block
containing it.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

section Standard

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinProgeneratorProjInstance1 : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance bernsteinProgeneratorProjInstance2 : T2Space F :=
  Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
local instance bernsteinProgeneratorProjInstance3 : TopologicalSpace (rationalPoints G) :=
  pointTopology
local instance bernsteinProgeneratorProjInstance4 (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance bernsteinProgeneratorProjInstance5 (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance bernsteinProgeneratorProjInstance6 (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance bernsteinProgeneratorProjInstance7 (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

local instance bernsteinProgeneratorProjInstance8 (I : Finset (SimpleRoot i ν)) :
    LocallyCompactSpace (rationalPoints (bernsteinLeviScheme i ν I)) := by
  have := (isClosed_levi i ν I).locallyCompactSpace
  exact (leviRationalPointHomeomorph i ν I).toHomeomorph.isClosedEmbedding.locallyCompactSpace

local instance bernsteinProgeneratorProjInstance9 (I : Finset (SimpleRoot i ν)) :
    NonarchimedeanGroup (rationalPoints (bernsteinLeviScheme i ν I)) := by
  let e := leviRationalPointHomeomorph i ν I
  have : IsTopologicalGroup (rationalPoints (bernsteinLeviScheme i ν I)) :=
    Topology.IsInducing.isTopologicalGroup e.toMulEquiv e.toHomeomorph.isInducing
  exact NonarchimedeanGroup.nonarchimedean_of_emb e.symm.toMulEquiv.toMonoidHom
    e.symm.toHomeomorph.isOpenEmbedding

variable (family : BernsteinStandardFamily i ν)

/-- The actual opposite parabolic `P̄ = M N̄` of the standard parabolic `P = M N` of `I`,
with the same Levi `M` and `P(F) ∩ P̄(F) = M(F)`. -/
def bernsteinStandardOpposite (I : Finset (SimpleRoot i ν)) :
    RepresentedParabolic.OppositeLeviParabolicData
      (Standard.parabolicHom i ν (rootSet i ν I))
      (Standard.leviToParabolic i ν (rootSet i ν I)) :=
  RepresentedParabolic.oppositeLeviParabolic family.connectedReductive _ _
    (bernsteinStandardRepresentativesGeometric i ν family I).1
    (bernsteinStandardRepresentativesGeometric i ν family I).2.1

/-- Normalized Jacquet restriction `r_{P̄}^G` along the opposite of the standard parabolic
of `I`. -/
def bernsteinStandardOppositeJacquetFunctor (I : Finset (SimpleRoot i ν)) :
    SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I)) :=
  let O := bernsteinStandardOpposite i ν family I
  RepresentedParabolic.leviJacquetFunctor O.inclusion O.levi O.unipotent O.isParabolic
    O.isRadical O.isLevi O.multiplication

/-- Bernstein's second adjointness (VI.9.6), supplied as a premise, at the standard parabolic
of `I`: a chosen adjunction `i_P^G ⊣ r_{P̄}^G`. -/
def bernsteinStandardSecondAdjunction
    (hAdj : RepresentedParabolic.LeviSecondAdjointnessStatement.{uF, uV})
    (I : Finset (SimpleRoot i ν)) :
    bernsteinStandardRepresentedInductionFunctor.{uF, uV} i ν family I ⊣
      bernsteinStandardOppositeJacquetFunctor.{uF, uV} i ν family I :=
  let h := bernsteinStandardRepresentativesGeometric i ν family I
  let O := bernsteinStandardOpposite i ν family I
  (hAdj F G family.connectedReductive _ O.parabolic _ _ O.radical
    (Standard.parabolicHom i ν (rootSet i ν I))
    (Standard.leviToParabolic i ν (rootSet i ν I))
    (Standard.unipotentToParabolic i ν (rootSet i ν I))
    h.1 h.2.1 h.2.2.1 h.2.2.2 O.inclusion O.levi O.unipotent O.isParabolic O.isLevi
    O.isRadical O.multiplication O.levi_comp O.intersection).some

/-- The opposite Jacquet functor is a left adjoint (first adjointness), so it preserves
epimorphisms. -/
instance bernsteinStandardOppositeJacquetFunctor_preservesEpimorphisms
    (I : Finset (SimpleRoot i ν)) :
    (bernsteinStandardOppositeJacquetFunctor.{uF, uV} i ν family I).PreservesEpimorphisms :=
  let O := bernsteinStandardOpposite i ν family I
  Functor.preservesEpimorphisms_of_adjunction
    (RepresentedParabolic.leviFirstAdjointnessAdjunction.{uF, uV} O.inclusion O.levi
      O.unipotent O.isParabolic O.isLevi O.isRadical O.multiplication)

omit [LocallyOfFiniteType G.X.hom] in
/-- Under second adjointness, the represented standard induction preserves projectives. -/
theorem projective_bernsteinStandardRepresentedInduction
    (hAdj : RepresentedParabolic.LeviSecondAdjointnessStatement.{uF, uV})
    (I : Finset (SimpleRoot i ν))
    (ρ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I)))
    (hρ : Projective ρ) :
    Projective ((bernsteinStandardRepresentedInductionFunctor.{uF, uV} i ν family I).obj ρ) :=
  (bernsteinStandardSecondAdjunction i ν family hAdj I).map_projective ρ hρ

omit [LocallyOfFiniteType G.X.hom] in
/-- Under second adjointness, the literal standard normalized induction preserves
projectives. -/
theorem projective_bernsteinStandardInduction
    (hAdj : RepresentedParabolic.LeviSecondAdjointnessStatement.{uF, uV})
    (I : Finset (SimpleRoot i ν))
    (ρ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I)))
    (hρ : Projective ρ) :
    Projective ((normalizedInductionFunctor (family.decomposition I)
      (family.closedUnipotent I)).obj (bernsteinLiteralLeviRep i ν I ρ)) :=
  Projective.of_iso (bernsteinStandardRepresentedInductionIso i ν family I ρ)
    (projective_bernsteinStandardRepresentedInduction i ν family hAdj I ρ hρ)

omit [LocallyOfFiniteType G.X.hom] in
/-- Renard VI.2.1, (a) implies (c), at an actual Bernstein cuspidal datum: the restriction of
the cuspidal representation to the common norm kernel `⁰M(F)` is compact. The joint
special-compact basis existence is a premise. -/
theorem hasCompactNormKernelRestriction_bernsteinCuspidalDatum
    (hJoint : BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{uF})
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family) :
    haveI := (bernsteinStandardRepresentativesGeometric i ν family
      a.roots).2.1.isConnectedReductive.isAffineHom
    RepresentedParabolic.HasCompactNormKernelRestriction a.representation := by
  have hL := (bernsteinStandardRepresentativesGeometric i ν family a.roots).2.1.isConnectedReductive
  have := hL.isAffineHom
  exact RepresentedParabolic.compactRestriction_of_isSupercuspidal parabolicDynamic
    standardCocharacter relativeRootSystem hJoint hL a.representation
    (a.isSupercuspidal i ν family)

/-- Given the joint special-compact basis existence, `Π_D = ind_{⁰M(F)}^{M(F)} ρ₀` is
projective in `M(M)` for every subrepresentation `ρ₀` of the restriction of the cuspidal
representation of a datum to `⁰M(F)`. -/
theorem projective_rationalNormKernelSummandInduction_of_datum
    (hJoint : BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{uF})
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
      (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)))
    (j : ρ₀ ⟶ SmoothRep.restrictSubgroup
      (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)) a.representation)
    (hj : Function.Injective (SmoothRep.hom j)) :
    Projective (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀) := by
  have h0 := hasCompactNormKernelRestriction_bernsteinCuspidalDatum.{uF, uV} i ν family hJoint a
  have hc : HasCompactSmoothDualCoefficients
      (a.representation.representation.comp
        (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)).subtype) := by
    exact h0
  exact rationalNormKernelSummandInduction_projective (bernsteinLeviScheme i ν a.roots)
    a.representation ρ₀ j hc hj

/-- The projectivity of `Π_Ω = i_P^G(Π_D)` in `M(G)`, from second adjointness and the joint
special-compact basis existence. -/
theorem projective_bernsteinInducedProgenerator
    (hAdj : RepresentedParabolic.LeviSecondAdjointnessStatement.{uF, uV})
    (hJoint : BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{uF})
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
      (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)))
    (j : ρ₀ ⟶ SmoothRep.restrictSubgroup
      (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)) a.representation)
    (hj : Function.Injective (SmoothRep.hom j)) :
    Projective ((normalizedInductionFunctor (family.decomposition a.roots)
      (family.closedUnipotent a.roots)).obj
        (bernsteinLiteralLeviRep i ν a.roots
          (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀))) :=
  projective_bernsteinStandardInduction i ν family hAdj a.roots _
    (projective_rationalNormKernelSummandInduction_of_datum.{uF, uV} i ν family hJoint a ρ₀ j hj)

/-- In a Bernstein saturated block, an object projective in `M(G)` has the lifting property
against block epimorphisms. -/
theorem bernsteinSaturatedBlock_lift_of_projective
    (s : BernsteinInertialClass.{uF, max uF uV} i ν family)
    (P : BernsteinSaturatedBlock.{uF, uV} i ν family s) (hP : Projective P.obj)
    (Y Z : BernsteinSaturatedBlock.{uF, uV} i ν family s) (q : Y ⟶ Z) (hq : Epi q)
    (f : P ⟶ Z) : ∃ g : P ⟶ Y, g ≫ q = f := by
  have : (bernsteinSaturatedBlockProperty i ν family s).ι.PreservesEpimorphisms :=
    ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory _
  have : Epi q.hom := (bernsteinSaturatedBlockProperty i ν family s).ι.map_epi q
  exact ⟨ObjectProperty.homMk (Projective.factorThru f.hom q.hom),
    ObjectProperty.hom_ext _ (Projective.factorThru_comp f.hom q.hom)⟩

/-- The projectivity conjunct of the VI.10.1 Theorem, conditional on second adjointness and
the joint special-compact basis existence: whenever `Π_Ω` lies in the block of the inertial
class of `a`, it has the lifting property against block epimorphisms. -/
theorem bernsteinInducedProgenerator_lift_of_secondAdjointness
    (hAdj : RepresentedParabolic.LeviSecondAdjointnessStatement.{uF, uV})
    (hJoint : BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{uF})
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
      (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)))
    (j : ρ₀ ⟶ SmoothRep.restrictSubgroup
      (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)) a.representation)
    (hj : Function.Injective (SmoothRep.hom j))
    (hmem : bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
      ((normalizedInductionFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj
          (bernsteinLiteralLeviRep i ν a.roots
            (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀))))
    (Y Z : BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a))
    (q : Y ⟶ Z) (hq : Epi q)
    (f : (⟨_, hmem⟩ : BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a))
      ⟶ Z) :
    ∃ g : (⟨_, hmem⟩ :
        BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a)) ⟶ Y,
      g ≫ q = f :=
  bernsteinSaturatedBlock_lift_of_projective.{uF, uV} i ν family _ ⟨_, hmem⟩
    (projective_bernsteinInducedProgenerator.{uF, uV} i ν family hAdj hJoint a ρ₀ j hj)
    Y Z q hq f

end Standard

end Langlands.CuspidalSupport
