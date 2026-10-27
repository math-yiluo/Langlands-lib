# Closed submodules of finite products of a Noetherian Banach algebra

Author: Worker 737. The proof adapts Worker 56's published proof of
`isClosed_ideal_of_noetherian_banach` in
`Langlands.Geometry.Analytic.ClosedIdealsBanach` from ideals to submodules.

Let `K` be a nontrivially normed field and let `A` be a complete normed
commutative `K`-algebra whose underlying ring is Noetherian. The theorem
`isClosed_submodule_pi_of_noetherian_banach` proves that every
`A`-submodule `S` of the finite product `Fin m → A` is closed for the
product norm. No completeness of `K`, ultrametric hypothesis, nonzero
`m`, or nonzero `A` is required.

## Proof

The topological closure `N` of `S` is a closed `A`-submodule of the
complete space `Fin m → A`, hence complete. Since `A` is Noetherian, the
finite product is a Noetherian `A`-module, so `N` has a finite generating
family `b : Fin n → N`. The linear-combination map from `Fin n → A` onto
`N` is continuous and surjective. The Banach open mapping theorem gives
a constant `D` such that every element of `N` has coefficients of norm at
most `D` times its norm.

Each generator `b i` is approximated by an element `y i` of `S`. The error
`b i - y i` is lifted to a coefficient vector `r i` of norm less than
`1 / (2 (n + 1))`. The coefficient map `c ↦ ∑ c i • r i` is a continuous
linear operator `F` on `Fin n → A` with operator norm less than one, so
Mathlib's geometric-series construction makes `1 - F` a unit. Applying the
generator map after `1 - F` gives `∑ c i • y i`, which lies in `S`.
Since `1 - F` is surjective, every element of `N` lies in `S`. Hence
`S` equals its closure and is closed.

The argument is the one used for ideals in `ClosedIdealsBanach`, whose
Markdown records its source as the closure argument of Proposition 2.3.4
in the retained Berkovich-course notes. Here the ambient module is a finite
product of copies of `A` instead of `A` itself. This module is
infrastructure for
`Langlands.Geometry.Analytic.StrictTestDomain.FiniteRationalTensorComparisonProof`,
where it shows that the kernel of a coefficient map is closed. That proof
handles trivially valued coefficient fields separately.
