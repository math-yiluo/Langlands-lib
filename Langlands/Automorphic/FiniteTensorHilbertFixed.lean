import Langlands.Automorphic.FiniteTensorHilbertSmoothEquiv
import Langlands.Representation.Smooth.FixedVectors.Definitions
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Open-subgroup fixed vectors of actual completed tensor slices -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV
set_option autoImplicit false
set_option maxHeartbeats 20000

namespace Langlands.TensorHilbertFixedAux

universe uR uG uW uA

variable {R : Type uR} [CommRing R]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {W : Type uW} [AddCommGroup W] [Module R W]

/-- An open-subgroup fixed vector in an invariant subspace is already ambiently smooth. -/
def fixedInfSmoothEquiv (τ : Representation R G W) (S : Subrepresentation τ)
    (K : OpenSubgroup G) :
    fixedVectors (S ⊓ Langlands.smoothSubrepresentation τ).toRepresentation K.toSubgroup ≃ₗ[R]
      fixedVectors S.toRepresentation K.toSubgroup where
  toFun x := ⟨⟨x.val.val, x.val.property.1⟩,
    fun k => Subtype.ext (congrArg
      (fun z : (S ⊓ Langlands.smoothSubrepresentation τ).toSubmodule => (z : W))
      (x.property k))⟩
  invFun x := ⟨⟨x.val.val, x.val.property,
      ⟨K, fun k => congrArg (fun z : S.toSubmodule => (z : W)) (x.property k)⟩⟩,
    fun k => Subtype.ext
      (congrArg (fun z : S.toSubmodule => (z : W)) (x.property k))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem fixedInfSmoothEquiv_apply_val (τ : Representation R G W)
    (S : Subrepresentation τ) (K : OpenSubgroup G)
    (x : fixedVectors (S ⊓ Langlands.smoothSubrepresentation τ).toRepresentation K.toSubgroup) :
    (fixedInfSmoothEquiv τ S K x).val.val = x.val.val := rfl

theorem fixedInfSmoothEquiv_symm_apply_val (τ : Representation R G W)
    (S : Subrepresentation τ) (K : OpenSubgroup G)
    (x : fixedVectors S.toRepresentation K.toSubgroup) :
    ((fixedInfSmoothEquiv τ S K).symm x).val.val = x.val.val := rfl

/-- Restrict a given equivalence to smooth intersection fixed vectors, then retain
its actual ambient vector in the full invariant subspace. -/
def factorFixedEquiv {A : Type uA} [AddCommGroup A] [Module R A]
    {σ : Representation R G A} (τ : Representation R G W) (S : Subrepresentation τ)
    (e : σ.Equiv (S ⊓ Langlands.smoothSubrepresentation τ).toRepresentation)
    (K : OpenSubgroup G) :
    fixedVectors σ K.toSubgroup ≃ₗ[R] fixedVectors S.toRepresentation K.toSubgroup :=
  (fixedVectorsEquiv e K.toSubgroup).trans (fixedInfSmoothEquiv τ S K)

/-- Transport finiteness using the actual fixed-space equivalence. -/
theorem factorFixed_finite {A : Type uA} [AddCommGroup A] [Module R A]
    {σ : Representation R G A} (τ : Representation R G W) (S : Subrepresentation τ)
    (e : σ.Equiv (S ⊓ Langlands.smoothSubrepresentation τ).toRepresentation)
    (K : OpenSubgroup G) (h : Module.Finite R (fixedVectors σ K.toSubgroup)) :
    Module.Finite R (fixedVectors S.toRepresentation K.toSubgroup) :=
  (Module.Finite.equiv_iff (factorFixedEquiv τ S e K)).mp h

/-- The full invariant subspace retains the original open-fixed dimension. -/
theorem factorFixed_finrank {A : Type uA} [AddCommGroup A] [Module R A]
    {σ : Representation R G A} (τ : Representation R G W) (S : Subrepresentation τ)
    (e : σ.Equiv (S ⊓ Langlands.smoothSubrepresentation τ).toRepresentation)
    (K : OpenSubgroup G) :
    Module.finrank R (fixedVectors S.toRepresentation K.toSubgroup) =
      Module.finrank R (fixedVectors σ K.toSubgroup) :=
  (factorFixedEquiv τ S e K).finrank_eq.symm

section Normed

variable {H : Type uW} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Both fixed spaces inherit the same ambient norm on the same vectors. -/
def fixedInfSmoothIsometry (τ : Representation ℂ G H) (S : Subrepresentation τ)
    (K : OpenSubgroup G) :
    fixedVectors (S ⊓ Langlands.smoothSubrepresentation τ).toRepresentation K.toSubgroup ≃ₗᵢ[ℂ]
      fixedVectors S.toRepresentation K.toSubgroup where
  toLinearEquiv := fixedInfSmoothEquiv τ S K
  norm_map' _ := rfl

end Normed
end Langlands.TensorHilbertFixedAux

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorHilbertFixedRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertFixedContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertFixedSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertFixedFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertFixedFiniteSpaceGroup (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorHilbertFixedLocalSpaceGroup (v : FinitePlace F)
    (L : LocalRealization F n v) : AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n} (P : FiniteTensorPresentation F n ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- The full closed slice and its intrinsic smooth part have the same open-subgroup
fixed vectors, with exactly their inherited Hilbert norms. Zero tails are allowed. -/
def sliceHilbertFixedIsometry (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) (K : OpenSubgroup (FiniteLocalGL F n v)) :=
  TensorHilbertFixedAux.fixedInfSmoothIsometry
    (b.completedRepresentation.comp (localInclusion F n v).toMonoidHom)
    (P.sliceHilbertRange b v y) K

/-- Original admissible factor fixed vectors exhaust the fixed vectors of the
entire closed Hilbert slice for every open local subgroup. -/
def factorHilbertFixedEquiv (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hA : IsAdmissible (ρ v)) (K : OpenSubgroup (FiniteLocalGL F n v)) :=
  TensorHilbertFixedAux.factorFixedEquiv
    (b.completedRepresentation.comp (localInclusion F n v).toMonoidHom)
    (P.sliceHilbertRange b v y) (P.factorHilbertSmoothEquiv b v y hy hA) K

end FiniteTensorPresentation
end Langlands.Automorphic
