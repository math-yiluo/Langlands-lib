import Langlands.Global.Factors.CuspidalPairEisensteinOpenCell
import Langlands.Global.RankinSelberg.PartialWhittakerIntegrals

/-! # Partial open-cell integrals of a cuspidal-pair Eisenstein series

For a finite set `S` of finite places, this module defines functions on `GL_(r+t+2)(𝔸)` that
are spherical at every finite place outside `S`, sections built from cusp forms spherical
outside `S`, the set `U_S` of adelic `(t + 1) × (r + 1)` matrices whose
entries are integral at every finite place outside `S`, the integrand of the open-cell
integral, and the partial open-cell integral `I_S(φ, s)`: the open-cell integral restricted
to `U_S`. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.Global.CuspidalPairEisenstein

open MeasureTheory NumberField Automorphic AdelicBlockParabolic AdelicBlockDeterminantCharacter
  PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F] (r t : ℕ)

/-- A function on `GL_(r+t+2)(𝔸)` is spherical outside `S` if it is right invariant under
`GL_(r+t+2)(𝒪_v)`, embedded at the place `v`, for every finite place `v ∉ S`. -/
def IsSphericalOutside (S : Finset (FinitePlace F)) (φ : AdelicGL F (r + t + 2) → ℂ) : Prop :=
  ∀ v ∉ S, ∀ k ∈ FiniteAdelicGL.localIntegral F (r + t + 2) v, ∀ g : AdelicGL F (r + t + 2),
    φ (g * AdelicGL.ofFinite F (r + t + 2) (FiniteAdelicGL.localInclusion F (r + t + 2) v k)) =
      φ g

/-- The set `U_S` of adelic `(t + 1) × (r + 1)` matrices whose entries have integral component
at every finite place `v ∉ S`. No condition is imposed at the places of `S` or at the
archimedean places. -/
def integralOutside (S : Finset (FinitePlace F)) :
    Set (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :=
  {Y | ∀ v ∉ S, ∀ i j, finiteProjection F v (Y i j) ∈ v.adicCompletionIntegers F}

variable {F r t}

/-- A section built from cusp forms spherical outside `S`: `φ` is spherical outside `S`, and
for every `k` in the standard maximal compact subgroup its normalized Levi slice
`m ↦ δ_P(m)^(-1/2) φ(m k)` is a finite linear combination of products `x(m₁) y(m₂)` of a cusp
form `x` of `T` and a cusp form `y` of the contragredient realization `dualRealization T'`,
both fixed by `GL(𝒪_v)` at every finite place `v ∉ S`. -/
def IsSphericalSectionOutside [CompactSpace (AdeleQuotient F)]
    (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t)
    (S : Finset (FinitePlace F)) (φ : AdelicGL F (r + t + 2) → ℂ) : Prop :=
  IsSphericalOutside F r t S φ ∧
  ∀ k : standardCompact F (r + t + 2),
    (fun m : FullLevi F (blockShape r t) =>
      ((leviHalfCharacter F (blockShape r t) m : ℂˣ) : ℂ)⁻¹ *
        φ ((blockShape r t).leviEmbedding (Adeles F) m * k.val)) ∈
      Submodule.span ℂ (Set.range fun v :
          {x : T.Space // RankinSelbergGlobal.IsSphericalOutside F T S x} ×
            {y : (dualRealization T').Space //
              RankinSelbergGlobal.IsSphericalOutside F (dualRealization T') S y} =>
        fun m : FullLevi F (blockShape r t) =>
          ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous v.1.1)
            (m (0 : Fin 2)) *
          ContinuousRationalFunctions.evaluate F (t + 1)
            ((dualRealization T').realization.toContinuous v.2.1) (m (1 : Fin 2)))

/-- The integrand `W_M(φ_s)(w u'(Y)) conj(ψ_N(u'(Y)))` of the open-cell integral
`openCellIntegral`, as a function of the adelic matrix `Y`. -/
def openCellIntegrand (ψ : AddChar (Adeles F) ℂ) (φ : AdelicGL F (r + t + 2) → ℂ) (s : ℂ)
    (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) : ℂ :=
  leviWhittaker F r t ψ (fun g => φ g * heightPower F r t s g)
      (openCellWeyl F r t * openCellUnipotent F r t Y) *
    starRingEnd ℂ (ψ (∑ i : Fin (r + t + 1),
      (openCellUnipotent F r t Y : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F))
        i.castSucc i.succ))

/-- The open-cell integral is the integral of `openCellIntegrand` for `openCellHaar`. -/
theorem openCellIntegral_eq_integral (ψ : AddChar (Adeles F) ℂ)
    (φ : AdelicGL F (r + t + 2) → ℂ) (s : ℂ) :
    openCellIntegral ψ φ s =
      letI : MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := borel _
      ∫ Y, openCellIntegrand ψ φ s Y ∂(openCellHaar F r t) :=
  rfl

/-- The partial open-cell integral `I_S(φ, s)`: the integral of `openCellIntegrand` over
`integralOutside F r t S` for `openCellHaar`. -/
def partialOpenCellIntegral (ψ : AddChar (Adeles F) ℂ) (S : Finset (FinitePlace F))
    (φ : AdelicGL F (r + t + 2) → ℂ) (s : ℂ) : ℂ :=
  letI : MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := borel _
  ∫ Y in integralOutside F r t S, openCellIntegrand ψ φ s Y ∂(openCellHaar F r t)

end Langlands.Global.CuspidalPairEisenstein
