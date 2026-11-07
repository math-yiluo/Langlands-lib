import Langlands.Representation.CuspidalSupport.RationalUniversalProgeneratorComparisonProof
import Langlands.Representation.Aubert.General.InertiaInductionCompression
import Langlands.Representation.Plancherel.UnramifiedRationalCompressionSpecialization
import Langlands.Representation.Induction.CoefficientRestriction

/-! The actual norm-kernel generator and the native universal induced model. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalNormalized

private def coefficientInflatedTwistEquiv
    {R : Type*} [CommRing R] [Algebra ℂ R]
    {L H : Type*} [Group L] [Group H]
    {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module R Y] [Module ℂ Y] [IsScalarTower ℂ R Y]
    {σ : Representation ℂ L X} {τ : Representation R L Y}
    (e : σ.Equiv (Jacquet.CoefficientRestriction.complexRepresentation τ))
    (φ : H →* L) (chi : H →* ℂˣ) :
    (Langlands.twist chi (σ.comp φ)).Equiv
      (Jacquet.CoefficientRestriction.complexRepresentation
        (Langlands.twist
          ((Units.map (algebraMap ℂ R).toMonoidHom).comp chi) (τ.comp φ))) := by
  refine Representation.Equiv.mk e.toLinearEquiv ?_
  intro h
  apply LinearMap.ext
  intro v
  change e.toLinearEquiv ((chi h : ℂ) • σ (φ h) v) =
    algebraMap ℂ R (chi h : ℂ) • τ (φ h) (e.toLinearEquiv v)
  rw [e.toLinearEquiv.map_smul, algebraMap_smul]
  exact congrArg (fun w => (chi h : ℂ) • w)
    (LinearMap.congr_fun (e.isIntertwining' (φ h)) v)

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance generatorAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance generatorAmbientTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance generatorLeviTopology : TopologicalSpace (rationalPoints M) :=
  rationalPointTopology F M.X
local instance generatorLeviTopologicalGroup : IsTopologicalGroup (rationalPoints M) :=
  rationalPoint_isTopologicalGroup F M
local instance generatorTensorAddCommGroup (E : Type*) [AddCommGroup E] [Module ℂ E] :
    AddCommGroup (RegularAlgebra r ⊗[ℂ] E) := TensorProduct.addCommGroup

variable (π : SmoothRep.{0, u, uV} ℂ (rationalPoints M))

/-- Transport the inducing representation along the canonical actual Levi
point homeomorphism, retaining its original carrier. -/
abbrev literalLeviRep : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l) :=
  (SmoothRep.pullbackFunctor (parabolicLeviPointHomeomorph r).symm).obj π

/-- The entire rational regular algebra, tensored with the unchanged original
carrier, intertwines the corresponding actual universal tensor actions. -/
def rationalUniversalTensorLeviEquiv :
    (((SmoothRep.pullbackFunctor (parabolicLeviPointHomeomorph r).symm).obj
      (CuspidalSupport.rationalUniversalTensorSmoothRep M π)).representation).Equiv
      (Jacquet.CoefficientRestriction.complexRepresentation
        (universalRepresentation r (literalLeviRep r π).representation)) := by
  let e := TensorProduct.congr (parabolicLeviRegularFunctionsEquiv r).toLinearEquiv
    (LinearEquiv.refl ℂ π)
  refine Representation.Equiv.mk e ?_
  intro m
  apply LinearMap.ext
  intro t
  change e (CuspidalSupport.rationalUniversalTensorRepresentation M π
    ((parabolicLeviPointHomeomorph r).symm m) t) =
      universalRepresentation r (literalLeviRep r π).representation m (e t)
  induction t using TensorProduct.inductionOn with
  | tmul b v =>
      change (parabolicLeviRegularFunctionsEquiv r
          (unramifiedEvaluationRegular (fun χ => (rationalNormCharacters M χ).toMul)
            ((parabolicLeviPointHomeomorph r).symm m) * b)) ⊗ₜ[ℂ]
          (π.representation ((parabolicLeviPointHomeomorph r).symm m) v) =
        (unramifiedEvaluationRegular (parabolicLeviRationalNormCharacters r) m *
          parabolicLeviRegularFunctionsEquiv r b) ⊗ₜ[ℂ]
          (π.representation ((parabolicLeviPointHomeomorph r).symm m) v)
      have he : parabolicLeviRegularFunctionsEquiv r
          (unramifiedEvaluationRegular (fun χ => (rationalNormCharacters M χ).toMul)
            ((parabolicLeviPointHomeomorph r).symm m)) =
          unramifiedEvaluationRegular (parabolicLeviRationalNormCharacters r) m := by
        simpa only [(parabolicLeviPointHomeomorph r).apply_symm_apply] using
          parabolicLeviRegularFunctionsEquiv_evaluation r
            ((parabolicLeviPointHomeomorph r).symm m)
      apply congrArg (fun c : RegularAlgebra r => c ⊗ₜ[ℂ]
        (π.representation ((parabolicLeviPointHomeomorph r).symm m) v))
      exact (map_mul (parabolicLeviRegularFunctionsEquiv r) _ b).trans
        (congrArg (fun c : RegularAlgebra r => c * parabolicLeviRegularFunctionsEquiv r b) he)
  | add s t hs ht =>
      simp only [map_add, hs, ht]
      exact ((universalRepresentation r (literalLeviRep r π).representation m).map_add
        (e s) (e t)).symm

/-- The actual full-restriction compact induction, transported to the literal
Levi, is the scalar restriction of the native universal tensor. -/
def rationalNormKernelUniversalLeviEquiv :
    (((SmoothRep.pullbackFunctor (parabolicLeviPointHomeomorph r).symm).obj
      (CuspidalSupport.rationalNormKernelCompactInduction M π)).representation).Equiv
      (Jacquet.CoefficientRestriction.complexRepresentation
        (universalRepresentation r (literalLeviRep r π).representation)) :=
  (SmoothRep.equivOfIso
    ((SmoothRep.pullbackFunctor (parabolicLeviPointHomeomorph r).symm).mapIso
      (CuspidalSupport.rationalUniversalProgeneratorComparisonIso M π))).trans
        (rationalUniversalTensorLeviEquiv r π)

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {n : U ⟶ P}
  (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
    (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
  (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))

/-- Inflation and the same positive half modulus extend the actual generator
comparison to the full parabolic inducing actions. -/
def rationalNormKernelInducingEquiv :
    (Aubert.General.inducingRepresentation h hU
      ((SmoothRep.pullbackFunctor (parabolicLeviPointHomeomorph r).symm).obj
        (CuspidalSupport.rationalNormKernelCompactInduction M π))).Equiv
      (Jacquet.CoefficientRestriction.complexRepresentation
        (inducingRepresentation r h hU (literalLeviRep r π).representation)) :=
  coefficientInflatedTwistEquiv (rationalNormKernelUniversalLeviEquiv r π)
    h.projection (HaarModulus.closedHalfCharacter _ hU _ h.le_normalizer)

local instance generatorInducedComplexModule :
    Module ℂ (Induced r h hU (literalLeviRep r π).representation) :=
  Module.compHom _ (algebraMap ℂ (RegularAlgebra r))
local instance generatorInducedComplexSMul :
    SMul ℂ (Induced r h hU (literalLeviRep r π).representation) :=
  (generatorInducedComplexModule r π h hU).toSMul

/-- The exact induction functor image of the actual norm-kernel generator is
equivalent to the native universal induced representation with only scalars
restricted. Both sides retain their actual function carriers. -/
def rationalNormKernelInducedEquiv :
    (((Aubert.General.rationalInertiaInductionFunctor M h hU
      (parabolicLeviPointHomeomorph r).symm).obj
        (CuspidalSupport.rationalNormKernelCompactInduction M π)).representation).Equiv
      (inducedComplexRepresentation r h hU (literalLeviRep r π)) :=
  Induction.coefficientSmoothInducedEquiv _ _ _
    (rationalNormKernelInducingEquiv r π h hU)

end Langlands.Plancherel.RationalNormalized
