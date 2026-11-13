import Langlands.GroupScheme.Descent.FiniteUnramifiedTensor
import Langlands.GroupScheme.Descent.RingTensorComponents
import Langlands.GroupScheme.Descent.FiniteGaloisTensor

/-! # Actual overlap components for a finite unramified integer extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.LocalGalois Langlands.LocalGalois.Separable
open scoped ValuativeRel TensorProduct

namespace Langlands.GroupScheme.Descent.FiniteUnramified

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

local instance : NontriviallyNormedField F := localNormedField F
local instance : IsUltrametricDist F := localNormedField_ultrametric F
local instance : CompleteSpace F := localNormedField_complete F

variable (E : IntermediateField F (SeparableClosure F))
    [FiniteDimensional F E] [IsGalois F E]

/-- The small-index form of the actual integer tensor equivalence. -/
def finiteIntegerTensorEquiv (hE : ArithmeticUnramified F E) :
    (extensionIntegers F E ⊗[baseIntegers F] extensionIntegers F E) ≃ₐ[
      extensionIntegers F E] (Fin (Module.finrank F E) → extensionIntegers F E) :=
  (integerTensorEquiv F E hE).trans
    (AlgEquiv.piCongrLeft (extensionIntegers F E)
      (fun _ : E ≃ₐ[F] E => extensionIntegers F E) (galoisIndexEquiv F E)).symm

@[simp]
theorem finiteIntegerTensorEquiv_tmul (hE : ArithmeticUnramified F E)
    (a b : extensionIntegers F E) (i : Fin (Module.finrank F E)) :
    finiteIntegerTensorEquiv F E hE (a ⊗ₜ[baseIntegers F] b) i =
      a * integerAut F E (galoisIndexEquiv F E i) b := rfl

/-- The actual finite-stage integer map. -/
abbrev integerMap :=
  RingTensor.map (baseIntegers F) (extensionIntegers F E)

/-- The finite overlap components of the actual integer map. -/
abbrev integerComponent (hE : ArithmeticUnramified F E)
    (i : Fin (Module.finrank F E)) :
    Spec (CommRingCat.of (extensionIntegers F E)) ⟶ Overlap (integerMap F E) :=
  RingTensor.component (finiteIntegerTensorEquiv F E hE) i

instance integerComponent_isIso_desc (hE : ArithmeticUnramified F E) :
    IsIso (Sigma.desc (integerComponent F E hE)) :=
  RingTensor.component_isIso_desc (finiteIntegerTensorEquiv F E hE)

@[reassoc (attr := simp)]
theorem integerComponent_fst (hE : ArithmeticUnramified F E)
    (i : Fin (Module.finrank F E)) :
    integerComponent F E hE i ≫ fst (integerMap F E) = 𝟙 _ :=
  RingTensor.component_fst _ _

@[reassoc (attr := simp)]
theorem integerComponent_snd (hE : ArithmeticUnramified F E)
    (i : Fin (Module.finrank F E)) :
    integerComponent F E hE i ≫ snd (integerMap F E) =
      Spec.map (CommRingCat.ofHom (integerAut F E (galoisIndexEquiv F E i)).toRingHom) :=
  RingTensor.component_snd _ _ (finiteIntegerTensorEquiv_tmul F E hE) i

end Langlands.GroupScheme.Descent.FiniteUnramified
