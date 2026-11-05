import Langlands.Representation.Plancherel.UnramifiedRationalNormalizedModels
import Langlands.Representation.Plancherel.UnramifiedNormalizedNaturality

/-! Specialization to the existing normalized functors on actual rational points.

Each law is stated through a reducible `Prop` abbreviation, named like the law in
UpperCamelCase. The theorem type is then a short application, which keeps the
theorem-signature indexing done when the module is exported tractable. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalNormalized

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance specializationAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance specializationPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

local instance specializationTensorAddCommGroup (E : Type*) [AddCommGroup E] [Module ℂ E] :
    AddCommGroup (RegularAlgebra r ⊗[ℂ] E) := TensorProduct.addCommGroup

/-- Scalar evaluation on the concrete algebra of all actual rational norms. -/
abbrev evaluation (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r)) :=
  UnramifiedNormalized.evaluation (parabolicLeviRationalNormCharacters r) χ

/-- The published tensor evaluation, bundled with its actual scalar evaluation. -/
abbrev tensorEvaluation (E : Type uV) [AddCommGroup E] [Module ℂ E]
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r)) :=
  UnramifiedNormalized.tensorEvaluation (parabolicLeviRationalNormCharacters r) E χ

/-- The pure-tensor formula of the actual tensor evaluation. -/
abbrev TensorEvaluationTmul (E : Type uV) [AddCommGroup E] [Module ℂ E]
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r))
    (b : RegularAlgebra r) (v : E) : Prop :=
  tensorEvaluation r E χ (b ⊗ₜ[ℂ] v) = b.val χ • v

@[simp] theorem tensorEvaluation_tmul (E : Type uV) [AddCommGroup E] [Module ℂ E]
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r))
    (b : RegularAlgebra r) (v : E) :
    TensorEvaluationTmul r E χ b v := rfl

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {n : U ⟶ P}
  (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
    (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
  (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))

local instance inducedModule
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    Module (RegularAlgebra r) (Induced r h hU π.representation) :=
  Submodule.module _

/-- The existing complex normalized induction of the actual unramified twist. -/
abbrev complexInduced (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r)) :=
  (Aubert.General.normalizedInductionFunctor h hU).obj
    (π.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ χ))

/-- The existing normalized Jacquet functor of that complex induced model. -/
abbrev complexJacquet (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r)) :=
  (Aubert.General.normalizedJacquetFunctor (UnipotentPoints (p := p) n)
    (parabolicLeviPointSubgroup p l) hU h.levi_le_normalizer).obj
      (complexInduced r h hU π χ)

/-- Actual function-value evaluation, with the existing complex functor as target. -/
def inducedEvaluation
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r)) :
    Induced r h hU π.representation →ₛₗ[evaluation r χ] complexInduced r h hU π χ :=
  UnramifiedNormalized.inducedEvaluation (parabolicLeviRationalNormCharacters r)
    h hU π.representation χ

/-- Equivariance of function-value evaluation for right translation. -/
abbrev InducedEvaluationAction
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r))
    (g : rationalPoints G) (f : Induced r h hU π.representation) : Prop :=
  inducedEvaluation r h hU π χ (inducedRepresentation r h hU π.representation g f) =
    (complexInduced r h hU π χ).representation g (inducedEvaluation r h hU π χ f)

theorem inducedEvaluation_action
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r))
    (g : rationalPoints G) (f : Induced r h hU π.representation) :
    InducedEvaluationAction r h hU π χ g f :=
  UnramifiedNormalized.inducedEvaluation_action _ h hU π.representation χ g f

/-- Evaluation descended through the actual unipotent-relation quotient. -/
def jacquetEvaluation
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r)) :
    Jacquet r h hU π.representation →ₛₗ[evaluation r χ] complexJacquet r h hU π χ :=
  UnramifiedNormalized.quotientEvaluation (inducedRepresentation r h hU π.representation)
    (complexInduced r h hU π χ).representation (UnipotentPoints (p := p) n)
    (inducedEvaluation r h hU π χ) (inducedEvaluation_action r h hU π χ)

section Laws

variable (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
  (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r))

/-- Positive full-parabolic normalization survives tensor specialization. -/
abbrev TensorEvaluationInducingAction (q : ParabolicPoints p)
    (t : RegularAlgebra r ⊗[ℂ] π) : Prop :=
  tensorEvaluation r π χ (inducingRepresentation r h hU π.representation q t) =
    Aubert.General.inducingRepresentation h hU
      (π.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ χ)) q
        (tensorEvaluation r π χ t)

theorem tensorEvaluation_inducing_action (q : ParabolicPoints p)
    (t : RegularAlgebra r ⊗[ℂ] π) :
    TensorEvaluationInducingAction r h hU π χ q t :=
  UnramifiedNormalized.inducingEvaluation_action _ h hU π.representation χ q t

/-- The actual pointwise formula for function-value evaluation. -/
abbrev InducedEvaluationEval (f : Induced r h hU π.representation)
    (x : rationalPoints G) : Prop :=
  Induction.eval _ (Aubert.General.inducingRepresentation h hU
      (π.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ χ)))
    (inducedEvaluation r h hU π χ f) x =
      unramifiedTensorEvaluation (parabolicLeviRationalNormCharacters r) π
        (Induction.eval _ (inducingRepresentation r h hU π.representation) f x) χ

@[simp] theorem inducedEvaluation_eval (f : Induced r h hU π.representation)
    (x : rationalPoints G) :
    InducedEvaluationEval r h hU π χ f x := rfl

/-- Semilinearity of function-value evaluation along b ↦ b(χ). -/
abbrev InducedEvaluationRegularSmul (b : RegularAlgebra r)
    (f : Induced r h hU π.representation) : Prop :=
  inducedEvaluation r h hU π χ
    (@SMul.smul (RegularAlgebra r) (Induced r h hU π.representation)
      (inducedModule r h hU π).toSMul b f) =
    b.val χ • inducedEvaluation r h hU π χ f

theorem inducedEvaluation_regular_smul (b : RegularAlgebra r)
    (f : Induced r h hU π.representation) :
    InducedEvaluationRegularSmul r h hU π χ b f :=
  (inducedEvaluation r h hU π χ).map_smulₛₗ b f

/-- The specialization commutes with the actual canonical quotient maps. -/
abbrev JacquetEvaluationMk (f : Induced r h hU π.representation) : Prop :=
  jacquetEvaluation r h hU π χ
    (Langlands.Jacquet.Localization.mk (inducedRepresentation r h hU π.representation)
      (UnipotentPoints (p := p) n) 1 f) =
    Langlands.Jacquet.Localization.mk (complexInduced r h hU π χ).representation
      (UnipotentPoints (p := p) n) 1 (inducedEvaluation r h hU π χ f)

@[simp] theorem jacquetEvaluation_mk (f : Induced r h hU π.representation) :
    JacquetEvaluationMk r h hU π χ f := rfl

/-- Semilinearity of the descended evaluation along b ↦ b(χ). -/
abbrev JacquetEvaluationRegularSmul (b : RegularAlgebra r)
    (z : Jacquet r h hU π.representation) : Prop :=
  jacquetEvaluation r h hU π χ (b • z) = b.val χ • jacquetEvaluation r h hU π χ z

theorem jacquetEvaluation_regular_smul (b : RegularAlgebra r)
    (z : Jacquet r h hU π.representation) :
    JacquetEvaluationRegularSmul r h hU π χ b z :=
  (jacquetEvaluation r h hU π χ).map_smulₛₗ b z

/-- The inverse Levi normalization survives actual quotient specialization. -/
abbrev JacquetEvaluationAction (m : parabolicLeviPointSubgroup p l)
    (z : Jacquet r h hU π.representation) : Prop :=
  jacquetEvaluation r h hU π χ (jacquetRepresentation r h hU π.representation m z) =
    (complexJacquet r h hU π χ).representation m (jacquetEvaluation r h hU π χ z)

theorem jacquetEvaluation_action (m : parabolicLeviPointSubgroup p l)
    (z : Jacquet r h hU π.representation) :
    JacquetEvaluationAction r h hU π χ m z :=
  UnramifiedNormalized.quotientEvaluation_twist_action
    (inducedRepresentation r h hU π.representation)
    (complexInduced r h hU π χ).representation (UnipotentPoints (p := p) n)
    (inducedEvaluation r h hU π χ) (inducedEvaluation_action r h hU π χ)
    (parabolicLeviPointSubgroup p l) h.levi_le_normalizer
    (UnramifiedNormalized.jacquetCharacter (parabolicLeviRationalNormCharacters r)
      _ _ hU h.levi_le_normalizer).toMonoidHom
    (HaarModulus.closedInverseHalfCharacter _ hU _ h.levi_le_normalizer)
    (fun _ => rfl) m z

end Laws

section Maps

variable {π τ : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)} (φ : π ⟶ τ)

/-- The B-linear map on actual universal induced models from a coefficient map. -/
abbrev inducedMap :=
  UnramifiedNormalized.universalInducedMap (parabolicLeviRationalNormCharacters r)
    h hU (SmoothRep.hom φ)

/-- The B-linear map on their actual normalized Jacquet quotients. -/
abbrev jacquetMap :=
  UnramifiedNormalized.universalJacquetMap (parabolicLeviRationalNormCharacters r)
    h hU (SmoothRep.hom φ)

/-- Apply exactly the existing normalized induction functor to the twisted map. -/
abbrev complexInducedMap
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r)) :=
  (Aubert.General.normalizedInductionFunctor h hU).map
    ((SmoothRep.twistFunctor χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ χ)).map φ)

/-- Apply exactly the existing normalized Jacquet functor to the complex induced map. -/
abbrev complexJacquetMap
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r)) :=
  (Aubert.General.normalizedJacquetFunctor (UnipotentPoints (p := p) n)
    (parabolicLeviPointSubgroup p l) hU h.levi_le_normalizer).map
      (complexInducedMap r h hU φ χ)

/-- Coefficient naturality of actual full-induced specialization. -/
abbrev InducedEvaluationMap
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r))
    (f : Induced r h hU π.representation) : Prop :=
  inducedEvaluation r h hU τ χ (inducedMap r h hU φ f) =
    SmoothRep.hom (complexInducedMap r h hU φ χ) (inducedEvaluation r h hU π χ f)

theorem inducedEvaluation_map
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r))
    (f : Induced r h hU π.representation) :
    InducedEvaluationMap r h hU φ χ f := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact UnramifiedNormalized.tensorEvaluation_map _ (SmoothRep.hom φ)
    (Induction.eval _ (inducingRepresentation r h hU π.representation) f x) χ

/-- Coefficient naturality after descent through the actual unipotent quotient. -/
abbrev JacquetEvaluationMap
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r))
    (z : Jacquet r h hU π.representation) : Prop :=
  jacquetEvaluation r h hU τ χ (jacquetMap r h hU φ z) =
    SmoothRep.hom (complexJacquetMap r h hU φ χ) (jacquetEvaluation r h hU π χ z)

theorem jacquetEvaluation_map
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r))
    (z : Jacquet r h hU π.representation) :
    JacquetEvaluationMap r h hU φ χ z :=
  UnramifiedNormalized.quotientEvaluation_natural
    (inducedRepresentation r h hU π.representation)
    (inducedRepresentation r h hU τ.representation)
    (complexInduced r h hU π χ).representation (complexInduced r h hU τ χ).representation
    (UnipotentPoints (p := p) n)
    (inducedEvaluation r h hU π χ) (inducedEvaluation r h hU τ χ)
    (inducedEvaluation_action r h hU π χ) (inducedEvaluation_action r h hU τ χ)
    (inducedMap r h hU φ) (SmoothRep.hom (complexInducedMap r h hU φ χ))
    (inducedEvaluation_map r h hU φ χ) z

end Maps

end Langlands.Plancherel.RationalNormalized
