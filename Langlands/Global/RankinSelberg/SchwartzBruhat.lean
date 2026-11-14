import Langlands.Global.RankinSelberg.WhittakerIntegrals
import Langlands.Global.Adelic
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! # The adelic Schwartz–Bruhat space of row vectors and its Fourier transform

The space `S(𝔸^n)` of Schwartz–Bruhat functions on row vectors `𝔸^n = M_(1,n)(𝔸)`,
defined as in Getz–Hahn §C.3 as the span of products `Φ_∞(x_∞) Φ_f(x_f)` of a Schwartz
function of the archimedean coordinates and a locally constant compactly supported
function of the finite coordinates; the span of restricted pure tensors
`Φ_∞ ⊗ ⊗_(v ∈ S) Φ_v ⊗ ⊗_(v ∉ S) 1_(𝒪_v^n)`; the condition that a function is the
characteristic function of `𝒪_v^n` at every finite place outside `S`; and the Fourier
transform `Φ̂(x) = ∫ Φ(y) ψ(y ᵗx) dy` for the covolume-one Haar measure. See the paired
Markdown for sources and normalizations.
-/

noncomputable section
universe u
open NumberField MeasureTheory
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

variable (F : Type u) [Field F] [NumberField F]

/-- Adelic row vectors `𝔸^n = M_(1,n)(𝔸)`. -/
abbrev RowVector (n : ℕ) := Matrix (Fin 1) (Fin n) (Adeles F)

/-- The archimedean coordinates `x_∞ ∈ (ℝ^(r₁) × ℂ^(r₂))^n` of a row vector, through
Mathlib's ring isomorphism of the infinite adeles with the mixed space. -/
def archimedeanCoordinates (n : ℕ) (x : RowVector F n) :
    Fin n → mixedEmbedding.mixedSpace F :=
  fun j => InfiniteAdeleRing.ringEquiv_mixedSpace F (x 0 j).1

/-- The finite coordinates `x_f ∈ (𝔸_f)^n` of a row vector. -/
def finiteCoordinates (n : ℕ) (x : RowVector F n) : Fin n → FiniteAdeles F :=
  fun j => (x 0 j).2

/-- The local coordinates `x_v ∈ F_v^n` of a row vector at a finite place `v`. -/
def localCoordinates (n : ℕ) (v : FinitePlace F) (x : RowVector F n) :
    Fin n → FiniteCompletion F v :=
  fun j => finiteProjection F v (x 0 j)

/-- Row vectors whose local coordinates lie in `𝒪_v^n` at every finite place `v ∉ S`. -/
def integralOutside (n : ℕ) (S : Finset (FinitePlace F)) : Set (RowVector F n) :=
  {x | ∀ v ∉ S, ∀ j, localCoordinates F n v x j ∈ v.adicCompletionIntegers F}

open scoped Classical in
/-- `Φ = Φ_∞ ⊗ Φ_f`: `Φ(x) = Φ_∞(x_∞) Φ_f(x_f)` for a Schwartz function `Φ_∞` on the
archimedean coordinates and a locally constant compactly supported function `Φ_f` on
`(𝔸_f)^n`. -/
def IsPureSchwartzBruhat (n : ℕ) (Φ : RowVector F n → ℂ) : Prop :=
  ∃ (Φinf : SchwartzMap (Fin n → mixedEmbedding.mixedSpace F) ℂ)
    (Φfin : (Fin n → FiniteAdeles F) → ℂ),
    IsLocallyConstant Φfin ∧ HasCompactSupport Φfin ∧
      Φ = fun x => Φinf (archimedeanCoordinates F n x) * Φfin (finiteCoordinates F n x)

/-- The Schwartz–Bruhat space `S(𝔸^n) = S(F_∞^n) ⊗ C_c^∞(𝔸_f^n)`: the complex span of the
pure tensors `Φ_∞ ⊗ Φ_f`. -/
def schwartzBruhat (n : ℕ) : Submodule ℂ (RowVector F n → ℂ) :=
  Submodule.span ℂ {Φ | IsPureSchwartzBruhat F n Φ}

open scoped Classical in
/-- `Φ = Φ_∞ ⊗ ⊗_(v ∈ S) Φ_v ⊗ ⊗_(v ∉ S) 1_(𝒪_v^n)` for a finite set `S` of finite
places, a Schwartz function `Φ_∞` and locally constant compactly supported `Φ_v` on
`F_v^n`. -/
def IsRestrictedPureSchwartzBruhat (n : ℕ) (Φ : RowVector F n → ℂ) : Prop :=
  ∃ (Φinf : SchwartzMap (Fin n → mixedEmbedding.mixedSpace F) ℂ)
    (S : Finset (FinitePlace F))
    (Φloc : (v : FinitePlace F) → (Fin n → FiniteCompletion F v) → ℂ),
    (∀ v ∈ S, IsLocallyConstant (Φloc v) ∧ HasCompactSupport (Φloc v)) ∧
      Φ = (integralOutside F n S).indicator fun x =>
        Φinf (archimedeanCoordinates F n x) * ∏ v ∈ S, Φloc v (localCoordinates F n v x)

/-- The restricted tensor product `S(F_∞^n) ⊗ ⊗'_v C_c^∞(F_v^n)` with respect to the
characteristic functions `1_(𝒪_v^n)`, realized as the complex span of the restricted pure
tensors. -/
def restrictedSchwartzBruhat (n : ℕ) : Submodule ℂ (RowVector F n → ℂ) :=
  Submodule.span ℂ {Φ | IsRestrictedPureSchwartzBruhat F n Φ}

/-- `Φ` is `1_(𝒪_v^n)` at every finite place outside `S`: it vanishes off
`integralOutside F n S`, and on that set its value depends only on the infinite
coordinates and the local coordinates at the places of `S`. -/
def IsStandardOutside (n : ℕ) (S : Finset (FinitePlace F)) (Φ : RowVector F n → ℂ) :
    Prop :=
  (∀ x, x ∉ integralOutside F n S → Φ x = 0) ∧
    ∀ x y, x ∈ integralOutside F n S → y ∈ integralOutside F n S →
      (∀ j, (x 0 j).1 = (y 0 j).1) →
      (∀ v ∈ S, localCoordinates F n v x = localCoordinates F n v y) → Φ x = Φ y

/-- The Fourier transform `Φ̂(x) = ∫_(𝔸^n) Φ(y) ψ(y ᵗx) dy` with respect to the additive
character `ψ`, for the Haar measure `rectangleMeasure F 1 n` on `𝔸^n` giving
`F^n \ 𝔸^n` volume one. -/
def fourierTransform (n : ℕ) (ψ : AddChar (Adeles F) ℂ) (Φ : RowVector F n → ℂ)
    (x : RowVector F n) : ℂ :=
  ∫ y, Φ y * ψ (∑ j, y 0 j * x 0 j) ∂rectangleMeasure F 1 n

end Langlands.Global.RankinSelbergGlobal
