import Langlands.Global.RankinSelberg.PartialIntegralExhaustion
import Langlands.Representation.Whittaker.Iwasawa

/-! # One-place Iwasawa cell decomposition of the Whittaker quotient measure

At a finite place `v ∉ S`, the classes `N_m(𝔸) g` with no condition at `v` split into the
cells `g_v ∈ N_m(F_v) ϖ^λ GL_m(𝒪_v)`, `λ ∈ ℤ^m`. Left translation by the `v`-component
`ϖ^λ` carries the classes with `g_v ∈ N_m(F_v) GL_m(𝒪_v)` onto the cell of `λ` and
multiplies the quotient measure by the modulus `δ_B(ϖ^λ)`. See the paired Markdown for
the source and normalizations.
-/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance cellSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance cellSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

/-- `ι_v(h)`: the actual adelic point with component `h ∈ GL_m(F_v)` at the finite place
`v`, and the identity matrix at every other finite place and at the infinite places. -/
def localPoint (m : ℕ) (v : FinitePlace F) (h : FiniteLocalGL F m v) : Points F m :=
  (GeneralLinearGroupPoints.adelicEquiv F m).symm
    (AdelicGL.ofFinite F m (FiniteAdelicGL.localInclusion F m v h))

/-- The exponent `∑_(i<j) (λ_i - λ_j)`. For a uniformizer `ϖ` of `F_v` and residue
cardinality `q_v`, `δ_B(ϖ^λ)⁻¹ = q_v ^ modulusExponent λ`, where `δ_B` is the modulus
character of the upper triangular Borel subgroup. -/
def modulusExponent {m : ℕ} (lam : Fin m → ℤ) : ℤ :=
  ∑ i : Fin m, ∑ j ∈ Finset.Ioi i, (lam i - lam j)

open Classical in
/-- **One-place Iwasawa cell decomposition of `N_m(𝔸) \ GL_m(𝔸)`**. This is a global
one-place form, made for the Library, of the local formula `dh = dn δ_B⁻¹(ϖ^J) dk` on
`N_m \ GL_m = ⊔_J N_m ϖ^J K_m` (Cogdell, Fields lectures 2003, Lecture 7 §3, p.57). That
local formula is the unramified computation used in Cogdell 2004, §4.1, p.220.

Let `S` be a finite set of finite places, `v ∉ S` a finite place, `ϖ` a uniformizer of
`F_v`, and `f` integrable on `N_m(𝔸) \ GL_m(𝔸)` for `whittakerQuotientMeasure`. For
`λ ∈ ℤ^m` write `f_λ(N_m(𝔸) g) = f(N_m(𝔸) ι_v(ϖ^λ) g)`. Then every `f_λ` is integrable
on the classes with `g_w ∈ N_m(F_w) GL_m(𝒪_w)` at every finite `w ∉ S`, and
`∑_λ q_v^(∑_(i<j)(λ_i-λ_j)) ∫_(U_S) f_λ = ∫_(U_(S∪{v})) f`, the sum converging
unconditionally, where `U_S` denotes those classes and `q_v = N(v)`. -/
def WhittakerCellDecompositionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (m : ℕ) (S : Finset (FinitePlace F))
    (v : FinitePlace F), v ∉ S →
  ∀ ϖ : (FiniteCompletion F v)ˣ,
    GeneralLinear.Iwasawa.IsUniformizingElement
      (Valued.v : Valuation (FiniteCompletion F v) (WithZero (Multiplicative ℤ))) ϖ →
  ∀ f : WhittakerQuotient F m → ℂ, Integrable f (whittakerQuotientMeasure F m) →
    let shift : (Fin m → ℤ) → WhittakerQuotient F m → WhittakerQuotient F m :=
      fun lam q => LeftCosetSpace.mk (unipotentAdelic F m)
        (localPoint F m v (GeneralLinear.Iwasawa.torus ϖ lam) * q.out)
    (∀ lam : Fin m → ℤ, IntegrableOn (fun q => f (shift lam q))
      (unipotentIntegralClasses F m S) (whittakerQuotientMeasure F m)) ∧
    HasSum (fun lam : Fin m → ℤ =>
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ modulusExponent lam *
          ∫ q in unipotentIntegralClasses F m S, f (shift lam q)
            ∂whittakerQuotientMeasure F m)
      (∫ q in unipotentIntegralClasses F m (insert v S), f q
        ∂whittakerQuotientMeasure F m)

end Langlands.Global.RankinSelbergGlobal
