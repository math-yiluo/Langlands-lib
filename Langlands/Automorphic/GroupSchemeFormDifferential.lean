import Langlands.Automorphic.GroupSchemeFiniteVectorDifferential
import Langlands.Automorphic.GroupSchemeTensorForms

/-! # Actual enveloping differentiation of uniform adelic forms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

local instance formDifferentialAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

/-- Every actual enveloping operator intertwines the entire original center action. -/
def adelicCenterEnvelopingIntertwiner (a : AdelicEnvelopingAlgebra F G hsmooth) :
    Representation.IntertwiningMap (adelicCenterAction F G hsmooth hcalc).toMonoidHom
      (adelicCenterAction F G hsmooth hcalc).toMonoidHom where
  toLinearMap := actualAdelicEnvelopingAction F G hsmooth a
  isIntertwining' z := by
    change adelicEnvelopingAction F G hsmooth hcalc a *
        adelicEnvelopingAction F G hsmooth hcalc z.val =
      adelicEnvelopingAction F G hsmooth hcalc z.val *
        adelicEnvelopingAction F G hsmooth hcalc a
    rw [← map_mul, ← map_mul, (Subalgebra.mem_center_iff.mp z.property a)]

/-- One global finite center orbit remains finite after arbitrary actual differentiation. -/
theorem IsAdelicCenterFinite.envelopingAction
    (a : AdelicEnvelopingAlgebra F G hsmooth)
    {f : FinitePlotSmoothRationalFunctions F G} (hf : IsAdelicCenterFinite F G hsmooth hcalc f) :
    IsAdelicCenterFinite F G hsmooth hcalc (actualAdelicEnvelopingAction F G hsmooth a f) :=
  hf.map (adelicCenterEnvelopingIntertwiner F G hsmooth hcalc a)

/-- Restrict the actual enveloping action to the unchanged global center-finite submodule. -/
def adelicCenterFiniteEnvelopingAction :
    AdelicEnvelopingAlgebra F G hsmooth →ₐ[ℂ]
      Module.End ℂ (adelicCenterFiniteSubmodule F G hsmooth hcalc) where
  toFun a :=
    { toFun := fun f => ⟨actualAdelicEnvelopingAction F G hsmooth a f.val,
        IsAdelicCenterFinite.envelopingAction F G hsmooth hcalc a f.property⟩
      map_add' f g := Subtype.ext (map_add _ _ _)
      map_smul' z f := Subtype.ext (map_smul _ _ _) }
  map_zero' := by ext f; simp only [map_zero, LinearMap.zero_apply]; rfl
  map_one' := by ext f; simp only [map_one, Module.End.one_apply]; rfl
  map_add' := by intros; ext f; simp only [map_add, LinearMap.add_apply]; rfl
  map_mul' := by intros; ext f; simp only [map_mul, Module.End.mul_apply]; rfl
  commutes' := by intro z; ext f; simp only [AlgHom.commutes, Module.algebraMap_end_apply]; rfl

variable (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
  {N : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))
  (hG : Langlands.GroupScheme.IsConnectedReductive G)
  (hrho : Langlands.GroupScheme.IsClosedSubgroup rho)
  (hK : Langlands.CompactIwasawa.IsMaximalCompact Kinf) (hN : 0 < N)

/-- The ordinary growth condition in the uniform intersection follows from its identity derivative. -/
theorem mem_uniformAdelicAutomorphicSubrepresentation_iff
    (f : FinitePlotSmoothRationalFunctions F G) :
    f ∈ uniformAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN ↔
      IsAdelicInfiniteFinite F G Kinf f ∧ IsAdelicCenterFinite F G hsmooth hcalc f ∧
        HasAdelicUniformModerateGrowth F G rho hsmooth hcalc f := by
  change (f ∈ adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN ∧
    f ∈ adelicUniformGrowthSubmodule F G rho hsmooth hcalc hN) ↔ _
  rw [mem_adelicAutomorphicSubrepresentation, mem_adelicUniformGrowthSubmodule]
  unfold IsAdelicAutomorphicForm
  constructor
  · intro hf
    exact ⟨hf.1.1, hf.1.2.1, hf.2⟩
  · rintro ⟨hfin, hcenter, hgrowth⟩
    refine ⟨⟨hfin, hcenter, ?_⟩, hgrowth⟩
    exact (hasAdelicModerateGrowth_iff F G rho hN f.val).mpr
      ((hasAdelicUniformModerateGrowth_iff F G rho hsmooth hcalc hN f).mp hgrowth).polynomialGrowth

/-- Arbitrary actual enveloping differentiation preserves all uniform form conditions. -/
theorem actualAdelicEnvelopingAction_mem_uniformAutomorphic
    (a : AdelicEnvelopingAlgebra F G hsmooth) (f : FinitePlotSmoothRationalFunctions F G)
    (hf : f ∈ uniformAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN) :
    actualAdelicEnvelopingAction F G hsmooth a f ∈
      uniformAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN := by
  have hgrowth : HasAdelicUniformPolynomialGrowth F G rho hsmooth hcalc f := hf.2
  have hderiv : HasAdelicUniformPolynomialGrowth F G rho hsmooth hcalc
      (actualAdelicEnvelopingAction F G hsmooth a f) := hgrowth.envelopingAction a
  change (IsAdelicInfiniteFinite F G Kinf _ ∧
    IsAdelicCenterFinite F G hsmooth hcalc _ ∧ HasAdelicPolynomialGrowth F G rho _) ∧
      HasAdelicUniformPolynomialGrowth F G rho hsmooth hcalc _
  exact ⟨⟨IsAdelicInfiniteFinite.envelopingAction F G hsmooth Kinf a hf.1.1,
    IsAdelicCenterFinite.envelopingAction F G hsmooth hcalc a hf.1.2.1,
    hderiv.polynomialGrowth⟩, hderiv⟩

/-- The original actual algebra action restricted to the existing uniform form space. -/
def uniformAdelicAutomorphicEnvelopingAction :
    AdelicEnvelopingAlgebra F G hsmooth →ₐ[ℂ]
      Module.End ℂ
        (uniformAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).toSubmodule where
  toFun a :=
    { toFun := fun f => ⟨actualAdelicEnvelopingAction F G hsmooth a f.val,
        actualAdelicEnvelopingAction_mem_uniformAutomorphic
          F G hsmooth hcalc Kinf rho hG hrho hK hN a f.val f.property⟩
      map_add' f g := Subtype.ext (map_add _ _ _)
      map_smul' z f := Subtype.ext (map_smul _ _ _) }
  map_zero' := by ext f; simp only [map_zero, LinearMap.zero_apply]; rfl
  map_one' := by ext f; simp only [map_one, Module.End.one_apply]; rfl
  map_add' := by intros; ext f; simp only [map_add, LinearMap.add_apply]; rfl
  map_mul' := by intros; ext f; simp only [map_mul, Module.End.mul_apply]; rfl
  commutes' := by intro z; ext f; simp only [AlgHom.commutes, Module.algebraMap_end_apply]; rfl

@[simp]
theorem uniformAdelicAutomorphicEnvelopingAction_val
    (a : AdelicEnvelopingAlgebra F G hsmooth)
    (f : (uniformAdelicAutomorphicSubrepresentation
      F G Kinf rho hsmooth hcalc hG hrho hK hN).toSubmodule) :
    (uniformAdelicAutomorphicEnvelopingAction F G hsmooth hcalc Kinf rho hG hrho hK hN a f).val =
      actualAdelicEnvelopingAction F G hsmooth a f.val := rfl

/-- The restricted differential action commutes with the existing finite adelic action. -/
theorem uniformAdelicAutomorphicEnvelopingAction_finiteRightAction
    (a : AdelicEnvelopingAlgebra F G hsmooth) (c : FiniteAdelicGroupPoints F G)
    (f : (uniformAdelicAutomorphicSubrepresentation
      F G Kinf rho hsmooth hcalc hG hrho hK hN).toSubmodule) :
    uniformAdelicAutomorphicEnvelopingAction F G hsmooth hcalc Kinf rho hG hrho hK hN a
        ((uniformAdelicAutomorphicSubrepresentation
          F G Kinf rho hsmooth hcalc hG hrho hK hN).toRepresentation c f) =
      (uniformAdelicAutomorphicSubrepresentation
        F G Kinf rho hsmooth hcalc hG hrho hK hN).toRepresentation c
          (uniformAdelicAutomorphicEnvelopingAction
            F G hsmooth hcalc Kinf rho hG hrho hK hN a f) := by
  apply Subtype.ext
  exact finitePlotSmoothEnvelopingAction_finiteRightAction F G hsmooth hcalc a c f.val

/-- Impose the already constructed uniform growth condition on the literal tensor form space. -/
def uniformTensorAdelicAutomorphicSubrepresentation :
    Subrepresentation (finitePlotSmoothFiniteRightAction F G) :=
  tensorAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN ⊓
    adelicUniformGrowthFiniteSubrepresentation F G rho hsmooth hcalc hN

/-- Its functions are exactly uniform forms satisfying the original tensor membership condition. -/
theorem mem_uniformTensorAdelicAutomorphicSubrepresentation_iff
    (f : FinitePlotSmoothRationalFunctions F G) :
    f ∈ uniformTensorAdelicAutomorphicSubrepresentation F G hsmooth hcalc Kinf rho hG hrho hK hN ↔
      f ∈ uniformAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN ∧
        f.val ∈ tensorSmoothSubrepresentation F G := by
  change ((f ∈ adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN ∧
    f.val ∈ tensorSmoothSubrepresentation F G) ∧
      f ∈ adelicUniformGrowthSubmodule F G rho hsmooth hcalc hN) ↔
    ((f ∈ adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN ∧
      f ∈ adelicUniformGrowthSubmodule F G rho hsmooth hcalc hN) ∧
        f.val ∈ tensorSmoothSubrepresentation F G)
  tauto

/-- Actual enveloping differentiation preserves the uniform tensor form intersection. -/
theorem actualAdelicEnvelopingAction_mem_uniformTensorAutomorphic
    (a : AdelicEnvelopingAlgebra F G hsmooth) (f : FinitePlotSmoothRationalFunctions F G)
    (hf : f ∈ uniformTensorAdelicAutomorphicSubrepresentation
      F G hsmooth hcalc Kinf rho hG hrho hK hN) :
    actualAdelicEnvelopingAction F G hsmooth a f ∈
      uniformTensorAdelicAutomorphicSubrepresentation F G hsmooth hcalc Kinf rho hG hrho hK hN := by
  rw [mem_uniformTensorAdelicAutomorphicSubrepresentation_iff] at hf ⊢
  exact ⟨actualAdelicEnvelopingAction_mem_uniformAutomorphic
    F G hsmooth hcalc Kinf rho hG hrho hK hN a f hf.1,
      actualAdelicEnvelopingAction_mem_tensorSmooth F G hsmooth a f hf.2⟩

/-- The original actual enveloping algebra acts on uniform tensor automorphic forms. -/
def uniformTensorAdelicAutomorphicEnvelopingAction :
    AdelicEnvelopingAlgebra F G hsmooth →ₐ[ℂ]
      Module.End ℂ (uniformTensorAdelicAutomorphicSubrepresentation
        F G hsmooth hcalc Kinf rho hG hrho hK hN).toSubmodule where
  toFun a :=
    { toFun := fun f => ⟨actualAdelicEnvelopingAction F G hsmooth a f.val,
        actualAdelicEnvelopingAction_mem_uniformTensorAutomorphic
          F G hsmooth hcalc Kinf rho hG hrho hK hN a f.val f.property⟩
      map_add' f g := Subtype.ext (map_add _ _ _)
      map_smul' z f := Subtype.ext (map_smul _ _ _) }
  map_zero' := by ext f; simp only [map_zero, LinearMap.zero_apply]; rfl
  map_one' := by ext f; simp only [map_one, Module.End.one_apply]; rfl
  map_add' := by intros; ext f; simp only [map_add, LinearMap.add_apply]; rfl
  map_mul' := by intros; ext f; simp only [map_mul, Module.End.mul_apply]; rfl
  commutes' := by intro z; ext f; simp only [AlgHom.commutes, Module.algebraMap_end_apply]; rfl

@[simp]
theorem uniformTensorAdelicAutomorphicEnvelopingAction_val
    (a : AdelicEnvelopingAlgebra F G hsmooth)
    (f : (uniformTensorAdelicAutomorphicSubrepresentation
      F G hsmooth hcalc Kinf rho hG hrho hK hN).toSubmodule) :
    (uniformTensorAdelicAutomorphicEnvelopingAction
      F G hsmooth hcalc Kinf rho hG hrho hK hN a f).val =
        actualAdelicEnvelopingAction F G hsmooth a f.val := rfl

/-- The tensor restriction retains compatibility with the original finite adelic action. -/
theorem uniformTensorAdelicAutomorphicEnvelopingAction_finiteRightAction
    (a : AdelicEnvelopingAlgebra F G hsmooth) (c : FiniteAdelicGroupPoints F G)
    (f : (uniformTensorAdelicAutomorphicSubrepresentation
      F G hsmooth hcalc Kinf rho hG hrho hK hN).toSubmodule) :
    uniformTensorAdelicAutomorphicEnvelopingAction F G hsmooth hcalc Kinf rho hG hrho hK hN a
        ((uniformTensorAdelicAutomorphicSubrepresentation
          F G hsmooth hcalc Kinf rho hG hrho hK hN).toRepresentation c f) =
      (uniformTensorAdelicAutomorphicSubrepresentation
        F G hsmooth hcalc Kinf rho hG hrho hK hN).toRepresentation c
          (uniformTensorAdelicAutomorphicEnvelopingAction
            F G hsmooth hcalc Kinf rho hG hrho hK hN a f) := by
  apply Subtype.ext
  exact finitePlotSmoothEnvelopingAction_finiteRightAction F G hsmooth hcalc a c f.val

end Langlands.Automorphic.GroupSchemeFunctions
