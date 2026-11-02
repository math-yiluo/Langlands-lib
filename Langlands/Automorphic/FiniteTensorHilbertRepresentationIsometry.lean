import Langlands.Automorphic.FiniteTensorHilbertRepresentationEquiv

/-! # Isometric realizations of actual tensor representation equivalences -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV
set_option autoImplicit false
set_option maxHeartbeats 20000

namespace Langlands.TensorRepresentationIsometryAux

universe uG uH uK

variable {G : Type uG} [Monoid G]
  {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℂ H]
  {K : Type uK} [NormedAddCommGroup K] [NormedSpace ℂ K]
  {σ : Representation ℂ G H} {τ : Representation ℂ G K}

/-- The generic injective-intertwiner range equivalence keeps a supplied
ambient norm equality on its inherited range norm. -/
theorem norm_rangeEquiv (f : σ.IntertwiningMap τ) (hf : Function.Injective f)
    (hn : ∀ x, ‖f x‖ = ‖x‖) (x : H) :
    ‖Langlands.Classification.JuxtaposedShuffle.rangeEquivOfInjective f hf x‖ = ‖x‖ :=
  hn x

/-- Add the proved norm equality to an existing linear equivalence. -/
def isometryOfNorm (e : H ≃ₗ[ℂ] K) (hn : ∀ x, ‖e x‖ = ‖x‖) : H ≃ₗᵢ[ℂ] K :=
  { e with norm_map' := hn }

/-- The existing range representation equivalence with its inherited isometric
structure, proved entirely on abstract normed carriers. -/
def rangeRepresentationIsometry (f : σ.IntertwiningMap τ) (hf : Function.Injective f)
    (hn : ∀ x, ‖f x‖ = ‖x‖) :=
  isometryOfNorm
    (Langlands.Classification.JuxtaposedShuffle.rangeEquivOfInjective f hf).toLinearEquiv
    (norm_rangeEquiv f hf hn)

end Langlands.TensorRepresentationIsometryAux

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorHilbertRepresentationIsometryRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertRepresentationIsometryContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertRepresentationIsometrySmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertRepresentationIsometryFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertRepresentationIsometryFiniteSpaceGroup (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorHilbertRepresentationIsometryLocalSpaceGroup (v : FinitePlace F) (L : LocalRealization F n v) :
    AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n} (P : FiniteTensorPresentation F n ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- The actual slice range representation equivalence with its inherited
isometric structure and identical underlying linear equivalence. -/
def sliceHilbertRepresentationIsometry (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :=
  Langlands.TensorRepresentationIsometryAux.rangeRepresentationIsometry
    (P.sliceHilbertIntertwiner b v y) (P.sliceHilbertEmbedding b v y).injective
    (P.sliceHilbertEmbedding b v y).norm_map

/-- The factor range representation equivalence with the isometric structure
from its actual factor-to-slice and slice-to-range maps. -/
def factorHilbertRepresentationIsometry (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) :=
  (P.factorSliceHilbertEquiv b v y hy).trans
    (P.sliceHilbertRepresentationIsometry b v y)

end FiniteTensorPresentation
end Langlands.Automorphic
