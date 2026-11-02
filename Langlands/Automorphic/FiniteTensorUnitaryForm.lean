import Langlands.Automorphic.TensorPresentation
import Langlands.Automorphic.OperatorUnitaryForm
import Langlands.Representation.Unitary.Restriction

/-! # Positive forms on actual tensor slices and their specified local factors -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorUnitaryRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorUnitaryContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorUnitarySmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorUnitaryFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance tensorUnitaryStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorUnitaryFiniteSpaceGroup (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorUnitaryLocalSpaceGroup (v : FinitePlace F) (L : LocalRealization F n v) :
    AddCommGroup L.Space := Submodule.addCommGroup _
local instance tensorUnitaryOperatorSpaceGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n} (P : FiniteTensorPresentation F n ρ E e he S)

/-- The actual inclusion of a tensor slice into the whole local form image. -/
def sliceInclusion (v : FinitePlace F) (y : LocalTensorTail (K := ℂ) F E v e) :
    (P.slice v y).representation.IntertwiningMap (S.localRepresentation v) where
  toLinearMap := Submodule.inclusion (P.slice_le v y)
  isIntertwining' _ := by
    apply LinearMap.ext
    intro f
    rfl

theorem sliceInclusion_injective
    (v : FinitePlace F) (y : LocalTensorTail (K := ℂ) F E v e) :
    Function.Injective (P.sliceInclusion v y) := by
  intro f g h
  exact Subtype.ext (congrArg (fun z : S.Space => z.val) h)

/-- Both routes retain the identical underlying automorphic form. -/
theorem inclusion_sliceInclusion
    (v : FinitePlace F) (y : LocalTensorTail (K := ℂ) F E v e)
    (f : (P.slice v y).Space) :
    S.inclusion (P.sliceInclusion v y f) = (P.slice v y).inclusion f := rfl

theorem sliceInclusion_sliceEquiv
    (v : FinitePlace F) (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) (x : V v) :
    P.sliceInclusion v y (P.sliceEquiv v y hy x) =
      P.localEquiv v (x ⊗ₜ[ℂ] y) := rfl

variable (b : Langlands.InvariantPositiveForm S.representation)

/-- Pull the supplied finite form to the genuine separated local tensor space.
No product decomposition of the form is assumed. -/
def separatedUnitaryForm (v : FinitePlace F) :
    Langlands.InvariantPositiveForm (separatedLocalRepresentation F n ρ E v e) :=
  (b.comp (localInclusion F n v).toMonoidHom).ofEquiv (P.localEquiv v)

@[simp]
theorem separatedUnitaryForm_inner (v : FinitePlace F)
    (x z : V v ⊗[ℂ] LocalTensorTail (K := ℂ) F E v e) :
    (P.separatedUnitaryForm b v).inner x z =
      b.inner (P.localEquiv v x) (P.localEquiv v z) := rfl

/-- Restrict the supplied positive form to the actual slice, including the zero slice. -/
def sliceUnitaryForm (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    Langlands.InvariantPositiveForm (P.slice v y).representation :=
  (b.comp (localInclusion F n v).toMonoidHom).comap
    (P.sliceInclusion v y) (P.sliceInclusion_injective v y)

@[simp]
theorem sliceUnitaryForm_inner
    (v : FinitePlace F) (y : LocalTensorTail (K := ℂ) F E v e)
    (f g : (P.slice v y).Space) :
    (P.sliceUnitaryForm b v y).inner f g =
      b.inner (P.sliceInclusion v y f) (P.sliceInclusion v y g) := rfl

/-- A nonzero complementary tensor gives a positive form on the specified local
factor by its genuine equivalence with the actual slice. -/
def factorUnitaryForm (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) :
    Langlands.InvariantPositiveForm (ρ v) :=
  (P.sliceUnitaryForm b v y).ofEquiv (P.sliceEquiv v y hy)

/-- The actual slice equivalence is an isometry for the constructed factor form. -/
theorem factorUnitaryForm_inner_sliceEquiv
    (v : FinitePlace F) (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) (x z : V v) :
    (P.factorUnitaryForm b v y hy).inner x z =
      (P.sliceUnitaryForm b v y).inner
        (P.sliceEquiv v y hy x) (P.sliceEquiv v y hy z) := rfl

/-- Factor coordinates evaluate the original form on actual embedded pure tensors. -/
theorem factorUnitaryForm_inner
    (v : FinitePlace F) (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) (x z : V v) :
    (P.factorUnitaryForm b v y hy).inner x z =
      b.inner (P.localEquiv v (x ⊗ₜ[ℂ] y))
        (P.localEquiv v (z ⊗ₜ[ℂ] y)) := rfl

/-- The separated form and factor form agree on the fixed-tail embedding. -/
theorem separatedUnitaryForm_inner_tmul
    (v : FinitePlace F) (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) (x z : V v) :
    (P.separatedUnitaryForm b v).inner (x ⊗ₜ[ℂ] y) (z ⊗ₜ[ℂ] y) =
      (P.factorUnitaryForm b v y hy).inner x z := rfl

theorem slice_isUnitarizable (hS : Langlands.IsUnitarizable S.representation)
    (v : FinitePlace F) (y : LocalTensorTail (K := ℂ) F E v e) :
    Langlands.IsUnitarizable (P.slice v y).representation := by
  obtain ⟨b⟩ := hS
  exact ⟨P.sliceUnitaryForm b v y⟩

include P in
theorem factor_isUnitarizable (hS : Langlands.IsUnitarizable S.representation)
    (v : FinitePlace F) (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) :
    Langlands.IsUnitarizable (ρ v) := by
  obtain ⟨b⟩ := hS
  exact ⟨P.factorUnitaryForm b v y hy⟩

end FiniteTensorPresentation

namespace OperatorRealization.UnitaryForm

variable {S : OperatorRealization F n} (b : S.UnitaryForm)
variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable (P : FiniteTensorPresentation F n ρ E e he S.toFiniteRealization)

/-- A supplied whole-operator form gives a chosen form on each faithfully
presented local factor, with its nonzero complementary tensor explicit. -/
def tensorFactorForm (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) :
    Langlands.InvariantPositiveForm (ρ v) :=
  P.factorUnitaryForm (b.finiteForm.ofEquiv S.finiteEquiv.symm) v y hy

end OperatorRealization.UnitaryForm
end Langlands.Automorphic
