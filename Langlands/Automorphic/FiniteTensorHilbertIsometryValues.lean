import Langlands.Automorphic.FiniteTensorHilbertRepresentationIsometry

/-! # Forward and inverse values of tensor range isometries -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV
set_option autoImplicit false
set_option maxHeartbeats 20000

namespace Langlands.TensorRepresentationIsometryAux

universe uG uH uK uL

variable {G : Type uG} [Monoid G]
  {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℂ H]
  {K : Type uK} [NormedAddCommGroup K] [NormedSpace ℂ K]
  {L : Type uL} [NormedAddCommGroup L] [NormedSpace ℂ L]
  {σ : Representation ℂ G H} {τ : Representation ℂ G K}

/-- Forgetting the range subtype recovers the original intertwiner. -/
theorem rangeRepresentationIsometry_apply_val
    (f : σ.IntertwiningMap τ) (hf : Function.Injective f)
    (hn : ∀ x, ‖f x‖ = ‖x‖) (x : H) :
    (rangeRepresentationIsometry f hf hn x).val = f x := rfl

/-- The inverse produces the unique source vector with the prescribed ambient
range value. -/
theorem rangeRepresentationIsometry_symm_apply
    (f : σ.IntertwiningMap τ) (hf : Function.Injective f)
    (hn : ∀ x, ‖f x‖ = ‖x‖) (z : f.range) :
    f ((rangeRepresentationIsometry f hf hn).symm z) = z.val :=
  congrArg Subtype.val ((rangeRepresentationIsometry f hf hn).apply_symm_apply z)

/-- A preceding isometric equivalence leaves the ambient composite unchanged. -/
theorem rangeRepresentationIsometry_comp_apply_val
    (a : L ≃ₗᵢ[ℂ] H) (f : σ.IntertwiningMap τ) (hf : Function.Injective f)
    (hn : ∀ x, ‖f x‖ = ‖x‖) (x : L) :
    ((a.trans (rangeRepresentationIsometry f hf hn)) x).val = f (a x) :=
  rangeRepresentationIsometry_apply_val f hf hn (a x)

/-- The inverse of the composite has the prescribed ambient composite value. -/
theorem rangeRepresentationIsometry_comp_symm_apply
    (a : L ≃ₗᵢ[ℂ] H) (f : σ.IntertwiningMap τ) (hf : Function.Injective f)
    (hn : ∀ x, ‖f x‖ = ‖x‖) (z : f.range) :
    f (a ((a.trans (rangeRepresentationIsometry f hf hn)).symm z)) = z.val := by
  exact (rangeRepresentationIsometry_comp_apply_val a f hf hn _).symm.trans
    (congrArg Subtype.val
      ((a.trans (rangeRepresentationIsometry f hf hn)).apply_symm_apply z))

end Langlands.TensorRepresentationIsometryAux


namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorHilbertValuesRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertValuesContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertValuesSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertValuesFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertValuesFiniteSpaceGroup (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorHilbertValuesLocalSpaceGroup (v : FinitePlace F) (L : LocalRealization F n v) :
    AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n} (P : FiniteTensorPresentation F n ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- Recover a vector of the slice completion from the inherited actual
invariant range, by the existing range isometry's continuous inverse. -/
def sliceHilbertInverse (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :=
  (P.sliceHilbertRepresentationIsometry b v y).symm.toLinearIsometry.toContinuousLinearMap

/-- Recover a vector of the specified nonzero-tail factor completion from the
same inherited actual invariant range by the continuous inverse. -/
def factorHilbertInverse (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) :=
  (P.factorHilbertRepresentationIsometry b v y hy).symm.toLinearIsometry.toContinuousLinearMap

end FiniteTensorPresentation
end Langlands.Automorphic
