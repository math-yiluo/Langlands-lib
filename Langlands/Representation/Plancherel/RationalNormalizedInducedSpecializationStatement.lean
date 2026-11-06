import Langlands.Representation.Plancherel.UnramifiedRationalNormalizedSpecialization
import Langlands.Representation.Induction.CompactQuotientProof
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! Renard VI.8.2: the canonical scalar extension of actual induced evaluation. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

section ScalarExtension

variable {R S V W : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module S W]

/-- The scalar extension of a semilinear map, with formula z tensor v ↦ z • T v. -/
def scalarExtensionOfSemilinear (T : V →ₛₗ[algebraMap R S] W) :
    S ⊗[R] V →ₗ[S] W := by
  let b : S →ₛₗ[algebraMap R S] V →ₛₗ[algebraMap R S] W :=
    { toFun := fun z => z • T
      map_add' := fun z w => add_smul z w T
      map_smul' := fun a z => by
        rw [Algebra.smul_def, mul_smul] }
  let t : S ⊗[R] V →ₛₗ[algebraMap R S] W := TensorProduct.lift b
  refine { t.toAddHom with map_smul' := ?_ }
  intro z x
  induction x using TensorProduct.inductionOn with
  | tmul w v =>
      change (z * w) • T v = z • (w • T v)
      exact mul_smul _ _ _
  | add x y hx hy =>
      change t (z • (x + y)) = z • t (x + y)
      rw [smul_add, map_add, map_add, smul_add]
      exact congrArg₂ (fun a b : W => a + b) hx hy

@[simp] theorem scalarExtensionOfSemilinear_tmul
    (T : V →ₛₗ[algebraMap R S] W) (z : S) (v : V) :
    scalarExtensionOfSemilinear T (z ⊗ₜ[R] v) = z • T v := rfl

end ScalarExtension

namespace RationalNormalized

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance fiberAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance fiberPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

local instance fiberTensorAddCommGroup (E : Type*) [AddCommGroup E] [Module ℂ E] :
    AddCommGroup (RegularAlgebra r ⊗[ℂ] E) := TensorProduct.addCommGroup

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {n : U ⟶ P}
  (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
    (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
  (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))

local instance fiberInducedModule
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    Module (RegularAlgebra r) (Induced r h hU π.representation) := Submodule.module _

/-- The literal scalar-extension fiber, using evaluation b ↦ b(χ). -/
abbrev InducedSpecializationFiber
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r)) :=
  letI : Algebra (RegularAlgebra r) ℂ := (evaluation r χ).toAlgebra
  ℂ ⊗[RegularAlgebra r] Induced r h hU π.representation

/-- The canonical complex-linear map extending the published actual function-value
semilinear evaluation; bijectivity is not used to define it. -/
def inducedScalarExtension
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r)) :
    letI : Algebra (RegularAlgebra r) ℂ := (evaluation r χ).toAlgebra
    InducedSpecializationFiber r h hU π χ →ₗ[ℂ] complexInduced r h hU π χ := by
  letI : Algebra (RegularAlgebra r) ℂ := (evaluation r χ).toAlgebra
  exact scalarExtensionOfSemilinear (inducedEvaluation r h hU π χ)

/-- This formula fixes the map on pure tensors, hence on the full fiber. -/
abbrev InducedScalarExtensionTmul
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r))
    (z : ℂ) (f : Induced r h hU π.representation) : Prop :=
  letI : Algebra (RegularAlgebra r) ℂ := (evaluation r χ).toAlgebra
  inducedScalarExtension r h hU π χ (z ⊗ₜ[RegularAlgebra r] f) =
    z • inducedEvaluation r h hU π χ f

@[simp] theorem inducedScalarExtension_tmul
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r))
    (z : ℂ) (f : Induced r h hU π.representation) :
    InducedScalarExtensionTmul r h hU π χ z f := rfl

/-- Bijectivity is a target about the constructed scalar-extension map. -/
def InducedSpecializationBijective
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r)) : Prop :=
  Function.Bijective (inducedScalarExtension r h hU π χ)

/-- Renard VI.8.2 specialization corollary for actual rational parabolics, with
literal quotient compactness and projection continuity retained explicitly. -/
def RationalNormalizedInducedSpecializationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (M P U : GroupScheme (Spec (CommRingCat.of F))) [IsAffine M.X.left]
      (A : CommGroupScheme (Spec (CommRingCat.of F)))
      (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M)
      (r : ParabolicRootPresentation p l a) (n : U ⟶ P)
      (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
        (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
      (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G))),
      Continuous h.projection → CompactSpace (Induction.LeftQuotient (ParabolicPoints p)) →
      ∀ (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
        (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r)),
        InducedSpecializationBijective r h hU π χ

end RationalNormalized
end Langlands.Plancherel
