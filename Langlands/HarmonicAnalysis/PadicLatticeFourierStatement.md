# Plus-sign Fourier integral of a p-adic lattice coset

Worker 741 authored this focused proposition definition.
`Langlands.HarmonicAnalysis.PadicLatticeFourierStatement.{u}` has implicit
parameters `{p : ℕ}` and `[Fact p.Prime]`, followed by explicit parameters
`(F : Langlands.PadicField.{u} p)` and `(T : F.TopologicalData)`. It returns
`Prop` for an arbitrary field universe `u` and every supplied `T`. The module
imports only [Conductor](Conductor.md), which supplies the valuation lattices
and the additive conductor. Through it, the module also gets the harmonic
objects of [Basic](Basic.md). This module defines a proposition. It proves
nothing.

## Installed structure

The proposition installs `T.topology`, `T.valuativeRel` and `T.localField`.
It then installs the Borel measurable space `borel F.Carrier` of that topology,
together with its `BorelSpace` certificate. The topological-ring structure that
`fourierIntegral` needs comes from the supplied local-field data. This is the
same setup as
[the self-dual existence statement](PadicSelfDualMeasureExistsStatement.md),
minus the uniform structure, which nothing here uses. No total disconnectedness,
self-duality or other analytic hypothesis is added.

## Quantifiers and local bindings

The statement quantifies over:

- every actual `ψ : UnitaryAdditiveCharacter F.Carrier`, a continuous
  nontrivial unit-circle character;
- every `μ : AdditiveHaarMeasure F.Carrier`, a regular additive Haar measure
  with no normalization;
- every level `m : ℤ`;
- every centre `a : F.Carrier` and every argument `y : F.Carrier`.

It then binds the coset and its raw characteristic function:

```text
C          := {x | x - a ∈ T.additiveLattice m}
indicatorC := C.indicator (fun _ => (1 : ℂ))
```

Write `L_k` for `T.additiveLattice k`. It is the set of `x` with
`T.discreteValuation x ≤ WithZero.exp k`. By
`mem_additiveLattice_iff_div_mem_integers` in Conductor, `L_k` is exactly the
fractional ideal `π^(-k) O` for the chosen uniformizer `π` and the actual
integer ring `O`. The lattices grow with `k` (`additiveLattice_mono`). So `C` is
the coset `a + π^(-m) O`. `indicatorC` is an ordinary function `F.Carrier → ℂ`.
It is not a new bundled test-function type, and it is not wrapped as
`SchwartzBruhat`.

## Conclusion

Let `n = T.additiveConductor ψ`. This is Tate's `n(ψ)`, the largest integer
with `ψ` trivial on `π^(-n) O` (`additiveConductor_spec`). The proposition is
the conjunction of two parts.

1. Convergence of the plus-sign Fourier integrand at `y`:

   ```text
   Integrable (fun x => ψ.complex (x * y) * indicatorC x) μ.measure
   ```

2. The exact value of the raw Bochner Fourier integral at `y`:

   ```text
   fourierIntegral ψ μ indicatorC y =
     ((μ.measure (L_m : Set F.Carrier)).toReal : ℂ) *
       ψ.complex (a * y) *
       (L_(n - m) : Set F.Carrier).indicator (fun _ => (1 : ℂ)) y
   ```

`fourierIntegral ψ μ f y` is, by definition in Basic,
`∫ x, ψ.complex (x * y) * f x ∂μ.measure`. So part 1 is integrability of
exactly the integrand of part 2. Part 2 is therefore a statement about a
convergent integral, not about Mathlib's value `0` for nonintegrable functions.
Both parts hold for every `y` (the quantifier is `∀ y`), so neither is an
almost-everywhere statement.

In words: the transform is `μ(π^(-m) O)` times the plus-sign phase `ψ(a*y)`
on the dual lattice `π^(-(n-m)) O`, and zero off it. The dual-lattice level is
`n - m`. The phase is `ψ(a*y)`, not `ψ(-a*y)`. For `m = 0` and `a = 0`, this
is the familiar formula: the transform of the characteristic function of `O`
is `μ(O)` times the characteristic function of `π^(-n) O`.

The measure is converted with `ENNReal.toReal`. This loses nothing: `L_m` is
compact and open, so `0 < μ(L_m) < ∞`. Proving this finiteness is part of the
future proof; it is not a hypothesis here.

## Scope

The statement holds for every Haar measure. It has no `IsSelfDual` or
`SelfDualMeasureExists` hypothesis, and it gives no self-dual volume. It
contains no scalar-ratio or self-dual normalization formula. So it neither uses
nor contradicts the published Tate fixed-Haar scalar-ratio correction recorded
in [Local Fourier inversion and Haar normalization](../LocalFactor/Harmonic/Statement.md).

It does not assert any of the following:

- Fourier inversion, or a formula for the Fourier square;
- that the Fourier transform maps `SchwartzBruhat` to itself;
- that a general test function decomposes into lattice cosets;
- the larger `PadicFourierDualityStatement`;
- any local-factor functional equation.

## Expected proof route (not part of this artifact)

A later proof task can argue as follows.

- Translate by `x = a + t`, using that additive Haar measure is
  translation invariant. Then `ψ(xy) = ψ(ay) ψ(ty)`, so the integral is
  `ψ(ay)` times `∫_(L_m) ψ(ty) dμ(t)`.
- Character orthogonality on the compact open subgroup `L_m` gives `μ(L_m)` if
  `t ↦ ψ(ty)` is trivial on `L_m`, and `0` otherwise.
- `t ↦ ψ(ty)` is trivial on `L_m` exactly when `y ∈ L_(n-m)`. This follows
  from the accepted conductor API: `additiveTrivialAt_iff_le_conductor`,
  `mul_mem_additiveLattice_iff` and `integer_annihilator_iff_mem_additiveLattice`
  in `Langlands.PadicField.TopologicalData`.
- Compactness and openness of the lattices follow from `T.isCompact_integers`,
  `T.isOpen_integers` and scaling by `π^(-m)`.
- Integrability holds because the integrand is bounded and measurable with
  support in the compact set `C`.

## Derived provenance and original sources

This is an internal derived prerequisite. It is not a verbatim source theorem.
It takes formula (2) in the proof of Weil's Proposition 2 and specializes it to
one coset in dimension one. The formula is then written in the Library's
lattice, conductor and Fourier conventions.

- André Weil, *Basic Number Theory*, second edition, Springer, 1973.
  Registered source `weil-1973-basic-number-theory`, file
  `/home/taskhub/central-library/Weil--Basic number theory (book, 2nd edition)--1973.pdf`,
  SHA256 `32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
  - Chapter VII §2, Proposition 2, printed p.107 / PDF p.124, formula (2):
    for an arbitrary Haar measure `α` and a lattice `M`,
    `Φ*(e*) = Σ_i Φ(e_i) ⟨e_i, e*⟩ ∫_M ⟨e, e*⟩ dα(e)`.
    The text adds that the last integral vanishes unless `e* ∈ M_*`.
  - Corollary 1 there is the case of one lattice `L`, deduced from (2). It
    says that the transform of the characteristic function of `L` is `α(L)`
    times the characteristic function of the dual lattice `L_*`.
  - Taking a single coset `a + M` with `M = π^(-m) O` gives the displayed
    formula. The transform at the start of Chapter VII §2 (printed p.104 /
    PDF p.121) has the same plus sign.
  - Chapter II §5, Theorem 3 and its corollary, printed pp.40–41 /
    PDF pp.57–58, identify `K` with its dual through `⟨x, y⟩ = χ(xy)`.
  - Definition 4 there, printed p.41 / PDF p.58, defines the order of `χ` as
    the largest `ν` with `χ` trivial on `P^(-ν)`. This is the Library's
    `additiveConductor`.
  - Proposition 12, printed p.42 / PDF p.59, says that the dual lattice of
    `P^k` is `P^(-k-ν)`. With `P^k = π^(-m) O`, this is
    `π^(-(ν-m)) O = L_(n-m)`.
- John Tate, *Number theoretic background*, Corvallis Part II (1979).
  Registered source `tate-1979-number-theoretic-background`, file
  `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`,
  SHA256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
  - §3.2, printed p.13 / PDF p.22, fixes the Fourier transform
    `f^(y) = ∫ f(x) ψ(xy) dx` for an arbitrary Haar measure `dx`.
  - (3.2.6) there defines `n(ψ)` as the largest `n` with `ψ(π^(-n) O) = 1`.

Worker 741 read Weil PDF pp.57–59 and 121–125, viewing a rendered image of
PDF p.124 for formula (2), and Tate PDF pp.21–22. No errata file for either
source was present in the public notes or the literature collection. The bundled
character, the raw `Set.indicator` formulation, the `toReal` measure
coefficient and the explicit integrability conjunct are derived Lean
packaging, not source notation.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0 and
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
