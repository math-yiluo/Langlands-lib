import Langlands.Representation.Plancherel.UnramifiedNormalizedTensorModels
import Langlands.Representation.Plancherel.ParabolicPointIntertwiningRegion
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Topology.Nonarchimedean.Subgroup

/-! Actual rational-point application of the normalized universal models. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalNormalized

universe u uV uW

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance ambientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance ambientPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- The literal image of the supplied parabolic at the identity test scheme. -/
abbrev ParabolicPoints (p : P ⟶ G) : Subgroup (rationalPoints G) :=
  (SubgroupFunctor.range p).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))

/-- The literal image of the supplied unipotent group in the ambient point group. -/
abbrev UnipotentPoints (n : U ⟶ P) : Subgroup (rationalPoints G) :=
  (SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))

/-- The concrete evaluation algebra on all rational-character norms of the actual Levi. -/
abbrev RegularAlgebra := unramifiedRegularFunctions (parabolicLeviRationalNormCharacters r)

/-- The actual universal tensor action on the literal Levi point subgroup. -/
abbrev universalRepresentation {E : Type uV} [AddCommGroup E] [Module ℂ E]
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) :=
  universalUnramifiedRepresentation (parabolicLeviRationalNormCharacters r) σ

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Closedness of the actual Levi and continuity of every rational norm make the
full common kernel open; no finite norm subfamily is chosen. -/
theorem isOpen_commonNormKernel :
    IsOpen (commonNormKernel (parabolicLeviRationalNormCharacters r) :
      Set (parabolicLeviPointSubgroup p l)) := by
  let := (isClosed_parabolicLeviPointSubgroup r).locallyCompactSpace
  exact (commonNormKernelTopology _ _ (parabolicLeviRationalNormCharacters r)
    (continuous_parabolicLeviRationalNormCharacters r)).1

local instance tensorAddCommGroup (E : Type*) [AddCommGroup E] [Module ℂ E] :
    AddCommGroup (RegularAlgebra r ⊗[ℂ] E) := TensorProduct.addCommGroup

/-- Smoothness of the actual universal tensor for the full rational norm family. -/
theorem isSmooth_universalRepresentation {E : Type uV} [AddCommGroup E] [Module ℂ E]
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) (hσ : IsSmooth σ) :
    IsSmooth (universalRepresentation r σ) :=
  isSmooth_universalUnramifiedRepresentation _ σ hσ (isOpen_commonNormKernel r)

/-- The universal inducing tensor as a smooth representation of the actual Levi. -/
def universalSmoothRep (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    SmoothRep (RegularAlgebra r) (parabolicLeviPointSubgroup p l) :=
  SmoothRep.of (universalRepresentation r π.representation)
    (isSmooth_universalRepresentation r π.representation π.isSmooth)

section Models

variable {n : U ⟶ P}
  (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
    (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
  (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))
  {E : Type uV} [AddCommGroup E] [Module ℂ E]

/-- Inflation by the supplied projection, normalized by the full P half-modulus. -/
abbrev inducingRepresentation (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) :=
  UnramifiedNormalized.universalInducingRepresentation
    (parabolicLeviRationalNormCharacters r) h hU σ

/-- The actual full smooth induced carrier on rational points. -/
abbrev Induced (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) :=
  UnramifiedNormalized.UniversalInduced (parabolicLeviRationalNormCharacters r) h hU σ

/-- Right translation on the actual universal rational-point model. -/
abbrev inducedRepresentation (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) :=
  UnramifiedNormalized.universalInducedRepresentation
    (parabolicLeviRationalNormCharacters r) h hU σ

/-- The actual quotient of full induced functions by the unipotent relations. -/
abbrev Jacquet (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) :=
  UnramifiedNormalized.UniversalJacquet (parabolicLeviRationalNormCharacters r) h hU σ

/-- The inverse Levi half-modulus action on that actual quotient. -/
abbrev jacquetRepresentation (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) :=
  UnramifiedNormalized.universalJacquetRepresentation
    (parabolicLeviRationalNormCharacters r) h hU σ

/-- Continuity of the supplied projection gives a smooth normalized inducing action. -/
theorem isSmooth_inducingRepresentation
    (hr : Continuous h.projection)
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) (hσ : IsSmooth σ) :
    IsSmooth (inducingRepresentation r h hU σ) :=
  (isSmooth_twist_iff _ _
    (UnramifiedNormalized.inductionCharacter (parabolicLeviRationalNormCharacters r)
      _ _ hU h.le_normalizer).isOpen_ker).mpr
    (isSmooth_comp h.projection hr (isSmooth_universalRepresentation r σ hσ))

theorem isSmooth_inducedRepresentation
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) :
    IsSmooth (inducedRepresentation r h hU σ) :=
  UnramifiedNormalized.isSmooth_universalInducedRepresentation _ h hU σ

theorem isSmooth_jacquetRepresentation
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) :
    IsSmooth (jacquetRepresentation r h hU σ) :=
  UnramifiedNormalized.isSmooth_universalJacquetRepresentation _ h hU σ

/-- The exact positive normalization on the literal full parabolic. -/
theorem induced_covariant
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E)
    (f : Induced r h hU σ) (q : ParabolicPoints p) (g : rationalPoints G) :
    Induction.eval _ (inducingRepresentation r h hU σ) f ((q : rationalPoints G) * g) =
      (UnramifiedNormalized.inductionCharacter (parabolicLeviRationalNormCharacters r)
        _ _ hU h.le_normalizer).toMonoidHom q •
        universalRepresentation r σ (h.projection q)
          (Induction.eval _ (inducingRepresentation r h hU σ) f g) :=
  UnramifiedNormalized.induced_covariant _ h hU _ f q g

@[simp] theorem induced_action
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E)
    (f : Induced r h hU σ) (g x : rationalPoints G) :
    Induction.eval _ (inducingRepresentation r h hU σ)
      (inducedRepresentation r h hU σ g f) x =
        Induction.eval _ (inducingRepresentation r h hU σ) f (x * g) := rfl

/-- Inverse-half normalized action on an actual quotient representative. -/
@[simp] theorem jacquet_action_mk
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E)
    (m : parabolicLeviPointSubgroup p l) (f : Induced r h hU σ) :
    jacquetRepresentation r h hU σ m
      (Langlands.Jacquet.Localization.mk (inducedRepresentation r h hU σ) _ 1 f) =
        (UnramifiedNormalized.jacquetCharacter (parabolicLeviRationalNormCharacters r)
          _ _ hU h.levi_le_normalizer).toMonoidHom m •
          Langlands.Jacquet.Localization.mk (inducedRepresentation r h hU σ) _ 1
            (inducedRepresentation r h hU σ m f) := rfl

end Models

end Langlands.Plancherel.RationalNormalized
