# Finite type after a reproducing smoothing operator

`Langlands.Analysis.Meromorphic.ReproducingFredholmFiniteTypeStatement`, proved
by `reproducingFredholmFiniteType`, is an analytic transfer on supplied data.
On an open set of a finite-dimensional complex manifold let `A(s) : B →L[ℂ] C`
and `T(s) : B →L[ℂ] B` be weakly holomorphic, with `B` a complex Hilbert space
and `C` a complex normed space. At `s₀` assume `D A(s₀) − 1` is compact for
some continuous linear `D`. Let `V` be a complex topological module with
continuous addition and continuous multiplication by each fixed scalar, and
with a supplied family of continuous linear forms that separates points. Set
`S(s) = ∑ᵢ bᵢ(s) Kᵢ : B →L[ℂ] V` for a finite index type, fixed continuous
linear `Kᵢ`, and holomorphic scalars `bᵢ`. Assume
`S(s₀)x = 0 ⇒ T(s₀)x = 0`. Then the subsets

> `S(s) { x | A(s)x = 0, T(s)x = x } ⊆ V`

are of finite type on an open neighbourhood of `s₀` in the given parameter
set. The result only requires the implication relating the two realizations
at the base point, not an embedding of the entire smoothing codomain into `B`.

## Implemented proof

- Augment the Hilbert-domain family to `F(s) = (A(s), 1 − T(s))`. Testing
  against a functional on `C × B` reduces weak holomorphy to testing against
  its restrictions to the two factors. Compose `D` with the first projection:
  the compact remainder for `F(s₀)` is unchanged. Apply
  `exactFiberFredholmCriterion` to obtain `ℓ(s) : ℂⁿ →L[ℂ] B` whose ranges
  contain the kernels, with range exactly `ker F(s₀)` at the base point.
- Put `Λ(s) = S(s) ℓ(s)`. The lemma `IsHolomorphicOperatorFamilyOn.finset_smul_comp`
  tests a finite sum of this form against a functional `ψ`. Each summand is
  the product of `bᵢ(s)` with the scalar test of `ℓ(s)` by `ψ ∘ Kᵢ`, hence
  holomorphic. No operator-norm topology on maps into `V` is used.
- At `s₀`, if `Λ(s₀)c = 0`, put `x = ℓ(s₀)c`. The vanishing implication
  gives `T(s₀)x = 0`; since `x ∈ ker F(s₀)`, the reproducing equation gives
  `T(s₀)x = x`. Thus `x = 0`, so `c = 0` by injectivity of `ℓ(s₀)`.
- `IsHolomorphicOperatorFamilyOn.exists_open_injective` proves that this
  injectivity persists. Choose finitely many tests from the given family by
  covering the compact unit sphere in `ℂⁿ` at `s₀` by their open nonvanishing
  sets. These tests give an injective map to a finite product of copies of
  `ℂ` at `s₀`, since a nonzero vector in the kernel could be normalized to the
  sphere. The tested family is norm-continuous: its values on the standard
  basis are finite tuples of continuous scalar functions, and
  `ContinuousLinearEquiv.piRing` identifies maps with these basis images.
  The open locus of injectivity of the tested family
  (`ContinuousLinearMap.isOpen_injective`) supplies the neighbourhood for
  `Λ`. The proof also applies when `n = 0`.
- A joint solution `x` belongs to `range ℓ(s)`; hence `S(s)x` belongs to
  `range Λ(s)`. This supplies all the clauses of `IsFiniteTypeOn` on the
  smaller neighbourhood.

## Provenance and scope

Derived from the Fredholm lemma and Corollary 3.4 in Bernstein–Lapid,
*On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc.
37 (2024), 187–234, §3.4 (pp.194–195), for use at the smoothing step of §7.6
(pp.219–220). Registered source: `bernstein-lapid-2024-meromorphic-continuation-eisenstein`.
The paper uses an approximate-identity modification of its smoothing operator
at that step; this proof instead includes the reproducing equation before the
Fredholm step and uses the exact base fiber. It does not establish the actual
adelic realizations, their boundedness and agreement, or that all solutions of
`Ξ_main` admit the required weighted Hilbert realizations.
