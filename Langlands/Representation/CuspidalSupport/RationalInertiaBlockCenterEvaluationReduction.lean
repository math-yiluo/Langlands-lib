import Langlands.Representation.CuspidalSupport.RationalBlockCenterAction
import Langlands.Representation.CuspidalSupport.RationalNormKernelSummand
import Langlands.Representation.CuspidalSupport.RationalNormKernelOrbitTwistStatement
import Langlands.Representation.CuspidalSupport.RationalSummandCenterGroupAlgebraStatement
import Langlands.Representation.CuspidalSupport.RationalInertiaBlockCenterEvaluationStatement

/-! Conditional reduction of the exact VI.4.5 central-character evaluation target. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

open Aubert.General Aubert.General.RationalPointFamily GroupScheme

/-- The representation-theoretic orbit, Hom-equivalence and endomorphism-center
statements imply the exact VI.4.5 evaluation assertion. All three inputs are
retained explicitly. -/
theorem rationalInertiaBlockCenterEvaluation_of_inputs
    (hOrbit : RationalNormKernelOrbitStatement.{uF, uV})
    (hHom : RationalSummandHomEquivalenceStatement.{uF, uV})
    (hAlg : RationalSummandCenterGroupAlgebraStatement.{uF, uV}) :
    RationalInertiaBlockCenterEvaluationStatement.{uF, uV} := by
  intro F _ _ _ _ G hG S i hi _ _ _ ν hν hStandard hRoots hU h π hπ hcusp
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
    rationalPoint_isTopologicalGroup F G
  obtain ⟨W, hW⟩ := (hOrbit F G hG π hπ).1
  let ρ := restrictionSummand (rationalCommonNormKernel G) π W
  have hρ : ρ.IsIrreducible :=
    restrictionSummand_isIrreducible (rationalCommonNormKernel G) π W hW
  let j := restrictionSummandι (rationalCommonNormKernel G) π W
  have hj : Function.Injective (SmoothRep.hom j) :=
    restrictionSummandι_injective (rationalCommonNormKernel G) π W
  obtain ⟨hmem, hEquiv⟩ := hHom F G hG S i hi ν hν hStandard hRoots hU π hπ hcusp ρ hρ j hj
  let X : RationalInertiaBlock G (rationalInertiaBaseLift G π) := ⟨_, hmem⟩
  have : (preadditiveCoyonedaObj X).IsEquivalence := hEquiv
  obtain ⟨a, ha⟩ := hAlg F G hG S i hi ν hν hStandard hRoots hU π hπ hcusp ρ hρ j hj
  let e := rationalInertiaBlockCenterFromEnd G (rationalInertiaBaseLift G π) X a
  refine ⟨e, ?_, ?_⟩
  · intro c Y
    exact rationalInertiaBlockCenterFromEnd_scalar G (rationalInertiaBaseLift G π) X a c Y
  · intro t ω hω
    apply rationalInertiaBlockCenterFromEnd_scalar_action G (rationalInertiaBaseLift G π) X a
    intro φ
    exact (ha t).2 ω φ

/-- Choose the actual VI.4.5 ring equivalence for the original data from the
three explicit representation-theoretic inputs. Its two action laws are recorded
in `rationalInertiaBlockCenterEvaluationEquivOfInputs_spec`. -/
def rationalInertiaBlockCenterEvaluationEquivOfInputs
    (hOrbit : RationalNormKernelOrbitStatement.{uF, uV})
    (hHom : RationalSummandHomEquivalenceStatement.{uF, uV})
    (hAlg : RationalSummandCenterGroupAlgebraStatement.{uF, uV}) :
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    haveI : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
      rationalPoint_isTopologicalGroup F G
    ∀ [LocallyCompactSpace (GroupScheme.rationalPoints G)]
      [NonarchimedeanGroup (GroupScheme.rationalPoints G)]
      [T2Space (GroupScheme.rationalPoints G)]
      (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{uF})
      (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (GroupScheme.rationalPoints G))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      let h := isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν
      ∀ (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
        (_hπ : π.IsIrreducible)
        (_hcusp : IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU π),
        let T : Subgroup (GroupScheme.rationalPoints G) :=
          ⨅ (ω : unramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul))
            (_ : Nonempty (rationalUnramifiedTwist G ω π ≅ π)),
            ω.val.toMonoidHom.ker
        MonoidAlgebra ℂ (T ⧸ (rationalCommonNormKernel G).subgroupOf T) ≃+*
            CatCenter (RationalInertiaBlock G (rationalInertiaBaseLift G π)) := by
  intro F _ _ _ _ G hG S i hi _ _ _ ν hν hStandard hRoots hU h π hπ hcusp
  exact Classical.choose
    (rationalInertiaBlockCenterEvaluation_of_inputs hOrbit hHom hAlg
      F G hG S i hi ν hν hStandard hRoots hU π hπ hcusp)

/-- The chosen equivalence fixes complex scalar actions on all block objects
and acts on each unramified twist by the required value `ω(t)`. -/
theorem rationalInertiaBlockCenterEvaluationEquivOfInputs_spec
    (hOrbit : RationalNormKernelOrbitStatement.{uF, uV})
    (hHom : RationalSummandHomEquivalenceStatement.{uF, uV})
    (hAlg : RationalSummandCenterGroupAlgebraStatement.{uF, uV}) :
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    haveI : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
      rationalPoint_isTopologicalGroup F G
    ∀ [LocallyCompactSpace (GroupScheme.rationalPoints G)]
      [NonarchimedeanGroup (GroupScheme.rationalPoints G)]
      [T2Space (GroupScheme.rationalPoints G)]
      (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{uF})
      (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (GroupScheme.rationalPoints G))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      let h := isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν
      ∀ (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
        (hπ : π.IsIrreducible)
        (hcusp : IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU π),
        let T : Subgroup (GroupScheme.rationalPoints G) :=
          ⨅ (ω : unramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul))
            (_ : Nonempty (rationalUnramifiedTwist G ω π ≅ π)),
            ω.val.toMonoidHom.ker
        let e := rationalInertiaBlockCenterEvaluationEquivOfInputs
          hOrbit hHom hAlg F G hG S i hi ν hν hStandard hRoots hU π hπ hcusp
        (∀ (c : ℂ) (X : RationalInertiaBlock G (rationalInertiaBaseLift G π)),
            ((e (MonoidAlgebra.single 1 c)).app X).hom = c • 𝟙 X.obj) ∧
          ∀ (t : T)
            (ω : unramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul))
            (hω : rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)
              (rationalUnramifiedTwist G ω (rationalInertiaBaseLift G π))),
            ((e (MonoidAlgebra.of ℂ _ (QuotientGroup.mk t))).app ⟨_, hω⟩).hom =
              ((ω.val (t : GroupScheme.rationalPoints G) : ℂˣ) : ℂ) •
                𝟙 (rationalUnramifiedTwist G ω (rationalInertiaBaseLift G π)) := by
  intro F _ _ _ _ G hG S i hi _ _ _ ν hν hStandard hRoots hU h π hπ hcusp
  exact Classical.choose_spec
    (rationalInertiaBlockCenterEvaluation_of_inputs hOrbit hHom hAlg
      F G hG S i hi ν hν hStandard hRoots hU π hπ hcusp)

end Langlands.CuspidalSupport
