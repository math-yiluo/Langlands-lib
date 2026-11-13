import Langlands.Representation.CuspidalSupport.BernsteinCuspLeftAdjoint
import Langlands.Representation.CuspidalSupport.BernsteinCuspFunctorProperties
import Langlands.Representation.CuspidalSupport.RationalLeviSplittingFromWhole

/-! # Renard VI.7.2, second Lemma, from cuspidal splittings of the standard Levi subgroups -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

open BernsteinCuspLeftAdjoint

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinCuspAssemblyTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

set_option maxHeartbeats 1600000 in
/-- The conclusion of Renard VI.7.2, second Lemma, for one actual standard family,
when every representation of every standard Levi subgroup splits into a cuspidal
part and a part without nonzero cuspidal subquotient. -/
theorem bernsteinCuspAdjunction_of_splittings
    (hsplit : ∀ (J : Finset (SimpleRoot i ν))
      (A : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J)),
      SplitReflector.HasSplitting (cusp.{uF, max uF uV} family J) A) :
    haveI : Finite (SimpleRoot i ν) := family.finiteSimpleRoots
    let cusp : ∀ J : Finset (SimpleRoot i ν),
        ObjectProperty (SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J)) := fun J W =>
      Langlands.Aubert.General.IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
        family.closedUnipotent J (family.closedLevi J) (family.leviDecomposition J) W
    let jac : ∀ J : Finset (SimpleRoot i ν),
        SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) ⥤
          SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J) := fun J =>
      normalizedJacquetFunctor (unipotent i ν J) (levi i ν J) (family.closedUnipotent J)
        (family.decomposition J).levi_le_normalizer
    let Ifun : (∀ J : Finset (SimpleRoot i ν), (cusp J).FullSubcategory) ⥤
        SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) :=
      Functor.pi (fun J => (cusp J).ι ⋙
          normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J)) ⋙
        (piEquivalenceFunctorDiscrete (Finset (SimpleRoot i ν))
          (SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))).functor ⋙ colim
    (∀ J : Finset (SimpleRoot i ν),
      ∃ sc : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J) ⥤ (cusp J).FullSubcategory,
        Nonempty (sc ⊣ (cusp J).ι)) ∧
    ∀ sc : ∀ J : Finset (SimpleRoot i ν),
        SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J) ⥤ (cusp J).FullSubcategory,
      (∀ J, Nonempty (sc J ⊣ (cusp J).ι)) →
      let R : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) ⥤
          (∀ J : Finset (SimpleRoot i ν), (cusp J).FullSubcategory) :=
        Functor.pi' fun J => jac J ⋙ sc J
      Nonempty (R ⊣ Ifun) ∧
      (R.Faithful ∧
        (∀ {A B C : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)} (f : A ⟶ B) (g : B ⟶ C),
          SmoothRep.IsShortExact (SmoothRep.hom f) (SmoothRep.hom g) →
            ∀ J, SmoothRep.IsShortExact (SmoothRep.hom ((R.map f) J).hom)
              (SmoothRep.hom ((R.map g) J).hom)) ∧
        (∀ V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
          Module.Finite (MonoidAlgebra ℂ (rationalPoints G)) V.representation.asModule →
            ∀ J, Module.Finite (MonoidAlgebra ℂ (levi i ν J))
              ((R.obj V) J).obj.representation.asModule)) ∧
      (Ifun.Faithful ∧
        ∀ {X Y Z : ∀ J : Finset (SimpleRoot i ν), (cusp J).FullSubcategory}
          (f : X ⟶ Y) (g : Y ⟶ Z),
          (∀ J, SmoothRep.IsShortExact (SmoothRep.hom (f J).hom) (SmoothRep.hom (g J).hom)) →
            SmoothRep.IsShortExact (SmoothRep.hom (Ifun.map f)) (SmoothRep.hom (Ifun.map g))) ∧
      ∀ (adj : R ⊣ Ifun) (V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)),
        Function.Injective (SmoothRep.hom (adj.unit.app V)) := by
  intro cuspL jacL IfunL
  have hQ : ∀ J, SplitReflector.IsSplitSerre (cusp.{uF, max uF uV} family J) :=
    fun J => isSplitSerre_cusp family J (hsplit J)
  refine ⟨fun J => SplitReflector.exists_leftAdjoint (hQ J), ?_⟩
  intro sc hsc RL
  let adjJ : ∀ J, sc J ⊣ (cusp.{uF, max uF uV} family J).ι := fun J => (hsc J).some
  have hadj : Nonempty (RL ⊣ IfunL) := bernsteinCuspAdjunction_of_reflectors i ν family sc hsc
  refine ⟨hadj, ⟨bernsteinR_faithful hQ adjJ hadj.some,
    fun f g hfg J => bernsteinR_map_isShortExact hQ adjJ f g hfg J,
    fun V hV J => bernsteinR_obj_finite hQ adjJ V hV J⟩,
    ⟨bernsteinInductionFunctor_faithful i ν family,
      fun f g hfg => bernsteinInductionFunctor_map_isShortExact i ν family f g hfg⟩,
    fun adj V => bernsteinR_unit_injective hQ adjJ adj V⟩

omit [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- Renard VI.3.5 at carrier universe `uW` splits every smooth representation of
every literal standard Levi subgroup of an actual standard family. -/
theorem hasSplitting_cusp_of_wholeDecomposition.{uW}
    (hwhole : RationalWholeCuspidalCategoryDecompositionStatement.{uF, uW})
    [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
    (family : BernsteinStandardFamily i ν) (J : Finset (SimpleRoot i ν))
    (A : SmoothRep.{0, uF, uW} ℂ (levi i ν J)) :
    SplitReflector.HasSplitting (cusp.{uF, uW} family J) A := by
  have := family.maximalSplitTorus.isSplitSubtorus.mono
  have hL : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν J)) :=
    standardLeviScheme_isConnectedReductive i ν standardCocharacter
      dynamicCentralizerReductive family.connectedReductive family.maximalSplitTorus
      family.genericCocharacter J
  have hiL := family.maximalSplitTorus.isMaximalSplitTorus_standardLeviTorusFactor i ν
    (rootSet i ν J) (Standard.isRepresentedBy_leviHom i ν (rootSet i ν J))
    (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν J))
  have hRootsL := relativeRootSystem F (Standard.leviScheme i ν (rootSet i ν J)) hL T
    (standardLeviTorusFactor i ν (rootSet i ν J)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν J))) hiL
  exact hasLeviCuspidalRemainderSplitting_of_wholeStatement hwhole G
    family.connectedReductive T i family.maximalSplitTorus ν standardCocharacter
    standardLeviIntersection family.genericCocharacter family.closedUnipotent J
    (family.closedLevi J) hRootsL A

/-- Renard's cuspidal-part functor `V ↦ V_sc` on smooth representations of the
literal standard Levi `M_J`, built from the splittings supplied by Renard VI.3.5 at
carrier universe `uW`: it keeps the cuspidal summand of each representation. -/
def bernsteinCuspidalPart.{uW}
    (hwhole : RationalWholeCuspidalCategoryDecompositionStatement.{uF, uW})
    (J : Finset (SimpleRoot i ν)) :
    SmoothRep.{0, uF, uW} ℂ (levi i ν J) ⥤ (cusp.{uF, uW} family J).FullSubcategory :=
  SplitReflector.reflector (isSplitSerre_cusp family J
    (hasSplitting_cusp_of_wholeDecomposition i ν hwhole family J))

/-- The cuspidal-part functor is left adjoint to the inclusion of the cuspidal
representations of `M_J`. -/
def bernsteinCuspidalPartAdjunction.{uW}
    (hwhole : RationalWholeCuspidalCategoryDecompositionStatement.{uF, uW})
    (J : Finset (SimpleRoot i ν)) :
    bernsteinCuspidalPart i ν family hwhole J ⊣ (cusp.{uF, uW} family J).ι :=
  SplitReflector.reflectorAdjunction _

set_option maxHeartbeats 1600000 in
/-- Renard VI.7.2, second Lemma, for the actual standard family, from Renard VI.3.5
(`RationalWholeCuspidalCategoryDecompositionStatement`) at the carrier universe
`max uF uV`. -/
theorem bernsteinCuspAdjunction_of_wholeDecomposition
    (hwhole : RationalWholeCuspidalCategoryDecompositionStatement.{uF, max uF uV}) :
    BernsteinCuspAdjunctionStatement.{uF, uV} := by
  intro F _ _ _ _ G _ _ T i ν _ _ family
  exact bernsteinCuspAdjunction_of_splittings i ν family
    (hasSplitting_cusp_of_wholeDecomposition i ν hwhole family)

end Langlands.CuspidalSupport
