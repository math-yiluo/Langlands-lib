# Finite tensor expansions of continuous translation-finite functions

The theorem `Langlands.RankinSelberg.finiteFunctionTensor.{uG}` proves the
existing proposition
`Langlands.RankinSelberg.FiniteFunctionTensorStatement.{uG}`, imported from
`Langlands.Representation.RankinSelberg.FiniteFunctionTensorStatement`.
It applies to every monoid `G : Type uG` with an arbitrary topology and
every natural number `r`. No continuity of multiplication is required.

For every continuous complex function `η` on `Fin r → G` whose complex
left-translation span is finite-dimensional, it supplies a natural number
`N`, coefficients `c : Fin N → ℂ`, and functions
`f : Fin N → Fin r → G → ℂ` with

```text
η a = ∑ j : Fin N, c j * ∏ i : Fin r, f j i (a i).
```

Every factor is continuous and has finite-dimensional complex span of the
translates `a ↦ f j i (b * a)`. The same convention, with pointwise
multiplication, defines the hypothesis on `η`. The finite family is chosen
from `η` before evaluating at `a`; there is no Schwartz test function or
spectral parameter in the theorem.

## Implemented proof

The auxiliary declarations are private to this proof module.
`TensorFinite` abbreviates the conjunction of continuity and the exact
finite-dimensional translation-span condition. `tensorFiniteSubmodule`
proves these functions form a complex submodule of all functions: the
translation span of a sum lies in the sum of the two original spans, and
the span of a scalar multiple lies in the original span. Zero is included.
Continuity is preserved by these operations.

`tensorFinite_restrict` proves a general slice lemma. Suppose `s, q : X → M`
are maps between monoids, `s` is continuous, and for each `b : X` there is
`t : M` such that `s (b * a) = t * q a` for all `a`. Then the translation
span of `η ∘ s` lies in the image of the translation span of `η` under the
linear restriction map `v ↦ v ∘ q`. Finite generation of the original span,
and hence finite-dimensionality, passes to this image and its submodules.
Only continuity of `s`, not of `q` or multiplication, is used.

The specializations `tensorFinite_head` and `tensorFinite_tail` insert a
fixed tail or head into a tuple using `Fin.cons`. For a fixed tail `y`, the
head slice is `x ↦ η (Fin.cons x y)`, with restriction map
`x ↦ Fin.cons x 1` and translate parameter `Fin.cons b y`. For a fixed
head `x`, the tail slice is `y ↦ η (Fin.cons x y)`, with restriction map
`y ↦ Fin.cons 1 y` and translate parameter `Fin.cons x b`. The needed
identities use only the monoid unit laws. Fixed-coordinate insertion is
continuous in the product topology.

`tensorFinite_split` constructs a decomposition

```text
η (Fin.cons x y) = ∑ i : Fin n, f i x * g i y,
```

with both `f i` and `g i` continuous and translation-finite. Let `S` be the
complex span of all head slices, with `y` varying. Each such slice is the
restriction of the translate of `η` by `Fin.cons 1 y`, so `S` lies in the
image of the original finite-dimensional translation span. Thus `S` is
finite-dimensional. The head-slice lemma and linear closure also show that
every member of `S` is continuous and translation-finite.

For `x : G`, evaluation at `x` is a linear functional `ev x` on `S`.
These functionals separate points: a function vanishing at every point is
zero. The Mathlib lemma
`FiniteDimensional.mem_span_of_iInf_ker_le_ker` then puts every functional
on `S` in the span of these evaluations. Define a linear map from the dual
of `S` to tail functions by

```text
coeff ℓ y = ℓ (the head slice at y).
```

The image `coeff (ev x)` is precisely the tail slice at `x`, already known
to be continuous and translation-finite. Applying the linear map to the
span of evaluations shows the same properties for `coeff ℓ` for every
functional `ℓ`. In particular, choose the finite basis `Module.finBasis`
of `S`, use its members as the functions `f i`, and apply `coeff` to its
coordinate functionals to obtain `g i`. Evaluating the basis expansion
`Basis.sum_repr` gives the displayed head–tail identity. This step uses
only algebraic duality; no topology on a finite-dimensional dual or
continuity of translated functions is assumed.

The public theorem inducts on `r`. For `r = 0`, use one summand with
coefficient equal to the value of `η` on the unique empty tuple. The empty
product equals one, and there are no factor conditions to check. For the
successor step, apply `tensorFinite_split`, apply the induction hypothesis
to every tail coefficient `g i`, and distribute the sums. Prepend `f i` to
each resulting tuple of factors using `Fin.cons`. The finite dependent
sum of their index sets is reindexed by `Fintype.equivFin` to produce the
required `Fin N` family. The proof imposes no nonzero-function or
positive-dimension hypothesis, so the zero function and zero-dimensional
slice spaces are covered as well.

## Provenance and scope

This is an internal algebraic proof of the Library's stated generalization
of the finite-function tensor reduction in H. Jacquet, I. I.
Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg Convolutions* (1983),
printed p. 392 between (5) and (6), registered as
`jpss-1983-rankin-selberg`. That passage writes finite functions on the
p-adic torus as finite sums of products of one-variable finite functions.
The definition by continuity and finite-dimensional translation span is
recalled in H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika,
*Automorphic Forms on GL(3) I* (1979), printed p. 181 immediately before
Proposition (2.2), registered as `jps-1979-gl3-i`. The retained original
passages were checked for this proof. Their exact source files and hashes
are recorded in the unchanged statement's companion Markdown.

The arbitrary monoid and arbitrary topology formulation, the explicit
scalar coefficients, and the treatment of empty tuples are internal
extensions rather than verbatim claims from those sources. This theorem
establishes only the finite tensor expansion. It proves no
Schwartz–Bruhat decomposition, integrability, Fubini theorem, Mellin
continuation, or denominator statement.
