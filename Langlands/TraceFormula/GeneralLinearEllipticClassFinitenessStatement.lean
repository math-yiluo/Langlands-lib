import Langlands.Global.FiniteAdelicGL.LocalFactor
import Langlands.JacquetLanglands.RegularElliptic

/-!
# Finiteness of the rational classes meeting a compact set that is regular elliptic at a place

The statement behind the geometric side of the simple trace formula for `GL_n` over a number
field: if a compact subset `Ω` of `GL_n(𝔸_K)` has regular elliptic component at one finite
place, then the rational elements whose adelic conjugacy class meets `Ω` are regular elliptic
and lie in finitely many `GL_n(K)`-conjugacy classes.
-/

namespace Langlands.TraceFormula

open Langlands.Global Langlands.JacquetLanglands

universe u

/-- Let `K` be a number field, `n` a natural number, `v` a finite place of `K` and `Ω` a compact
subset of `GL_n(𝔸_K)` whose component at `v` consists of regular elliptic elements of
`GL_n(K_v)`. Then there is a finite set `R` of elements of `GL_n(K)` such that every
`γ ∈ GL_n(K)` with `x⁻¹ γ x ∈ Ω` for some `x ∈ GL_n(𝔸_K)` is regular elliptic and is
`GL_n(K)`-conjugate to an element of `R`. -/
def GeneralLinearEllipticClassFinitenessStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ) (v : FinitePlace K)
    (Ω : Set (AdelicGL K n)), IsCompact Ω →
    (∀ ω ∈ Ω, IsRegularElliptic
      (FiniteAdelicGL.localProjection K n v (AdelicGL.finite K n ω))) →
    ∃ R : Finset (RationalGL K n),
      ∀ γ : RationalGL K n,
        (∃ x : AdelicGL K n, x⁻¹ * AdelicGL.rational K n γ * x ∈ Ω) →
          IsRegularElliptic γ ∧ ∃ r ∈ R, ∃ y : RationalGL K n, y⁻¹ * γ * y = r

end Langlands.TraceFormula
