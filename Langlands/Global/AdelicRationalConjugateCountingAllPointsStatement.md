# Counting rational points in adelic conjugates of compact sets, at every adelic point

Module `Langlands.Global.AdelicRationalConjugateCountingAllPointsStatement` states
`AdelicRationalConjugateCountingAllPointsStatement` and proves that it implies the Library's
`AdelicRationalConjugateCountingStatement` (module `AdelicRationalConjugateCounting`). It does not
prove `AdelicRationalConjugateCountingAllPointsStatement`.

| Declaration | Kind | Source |
| --- | --- | --- |
| `AdelicRationalConjugateCountingAllPointsStatement` | statement | Mœglin–Waldspurger I.2.4, Lemma (a)(i) |
| `adelicRationalConjugateCounting_of_allPoints` | theorem (proved) | internal |

## Statement

`AdelicRationalConjugateCountingAllPointsStatement.{u}`: let `F : Type u` be a number field, `G`
an affine group scheme over `F` and `rho : MatrixRepresentation G (Fin n)` with `0 < n` and
`IsClosedSubgroup rho`. There is `d : ℕ` such that for every compact `C ⊆ G(𝔸)` there is a real
`B ≥ 0` such that for every `x ∈ G(𝔸)` the set

`P = G(F) ∩ x C x⁻¹` (`(rationalSubgroup F G : Set _) ∩ ((fun y => x * y * x⁻¹) '' C)`)

is finite and `#P ≤ B · ‖x‖^d`, where `‖x‖ = RepresentationGrowth.adelicHeight F G rho x`. The
exponent `d` is chosen before `C`. The point `x` is arbitrary: unlike
`AdelicRationalConjugateCountingStatement`, its finite component is not required to lie in a
given compact subset of `G(𝔸_f)`.

`adelicRationalConjugateCounting_of_allPoints` derives `AdelicRationalConjugateCountingStatement`
from it, using the same `d` and, for each compact `K ⊆ G(𝔸_f)` and `C`, the same `B`; the
hypothesis on the finite component of `x` is not used.

## Source

C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series*, Cambridge
University Press 1995, registered as `moeglin-waldspurger-1995-spectral-decomposition`, chapter
file `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`, I.2.4, Lemma (a)(i), printed
p. 25 (PDF p. 8), and its proof, printed p. 26 (PDF p. 9): there is `r > 0` and for every compact
`C ⊆ G(𝔸)` a constant `c > 0` such that `∑_{γ ∈ G(F)} 1_C(x⁻¹ γ y) ≤ c ‖x‖^r` for all
`x, y ∈ G(𝔸)`. The proof bounds the sum by `#(G(F) ∩ x C C⁻¹ x⁻¹)` and states that the
definition of the norm reduces the bound of this number by `c ‖x‖^r` to the case `G = GL_n`.

## Provenance (derived)

For `y = x`, `1_C(x⁻¹ γ x) = 1` exactly when `γ ∈ x C x⁻¹`, so the sum of (a)(i) is `#P`, and the
bound of (a)(i) gives both the finiteness of `P` and the bound on its cardinality. The height
`‖·‖` of Mœglin–Waldspurger (I.2.2) is the normalized product over all places of the maximum of
the absolute values of the entries of `rho(x)` and `rho(x)⁻¹`, which is
`RepresentationGrowth.adelicSourceNorm`. The height used here,
`adelicHeight = n^s · adelicSourceNorm` with `s = ∑_{v | ∞} mult v`
(`adelicHeight_eq_scalar_mul_sourceNorm`), is at least `1` for `n > 0`
(`one_le_adelicHeight`). So a bound `c ‖x‖^r` with real `r > 0` gives a bound
`B · adelicHeight(x)^d` with `d = ⌈r⌉` and `B = c`, and conversely. The order of quantifiers,
`d` before `C` and `B` after `C`, is that of the source.
