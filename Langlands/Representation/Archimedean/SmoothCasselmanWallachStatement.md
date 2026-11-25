# Casselman–Wallach extension on genuine smooth vectors

The declarations are in `Langlands.Archimedean`. The module defines two interfaces and states, but does not prove, a Banach smooth-vector specialization of the Casselman–Wallach lifting theorem.

## Interfaces

For the matrix model over `F : Type` with `RCLike F`, write `D(R)` for `DerivativeSmoothVectors (matrixModel F n) R` and `R∞` for its transported action. The carrier of the bounded-operator representation `R` can be any complex normed space. `smoothKFinite F n R` is the submodule of `D(R)` whose vectors have finite-dimensional complex orbit span under `Matrix.unitaryGroup (Fin n) F` acting through `Unitary.toUnits`. This generalizes the definition of `smoothHilbertKFinite` in [SmoothHilbert](SmoothHilbert.md), giving the same submodule when an inner product supplies the normed-space structure.

For a complex vector space `V` with compact action `ρ` and a complex Lie algebra action `π` of `ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) F`, `IsSmoothGKIntertwiner F n R ρ π f` asks that a complex-linear map `f : V → D(R)` satisfy

- `f(ρ(k)v) = R∞(Unitary.toUnits k)(f(v))` for every compact element `k` and `v : V`;
- `f(π(1 ⊗ X)v) = dR(X)(f(v))` for every real matrix direction `X` and `v : V`, where `dR(X)` is the genuine `DerivativeSmoothVectors.operator`.

The predicate does not itself assert any irreducibility, admissibility, continuity of `f`, or independent compatibility axioms on `ρ` and `π`.

## Statement and source comparison

`RealSmoothCasselmanWallachExtensionStatement.{uV,uE₁,uE₂}` is a `Prop` with free carrier universes. For `n = r + 1` and `F = ℝ`, assume `IsIrreducibleGKModule ρ π` and `IsAdmissibleGKModule ρ`, jointly continuous actions `R₁` and `R₂` on complex Banach spaces, a linear equivalence `e : V ≃ₗ[ℂ] smoothKFinite ℝ n R₁`, and a linear map `f : V →ₗ[ℂ] D(R₂)`. Require `IsSmoothGKIntertwiner` for both the inclusion after `e` and the map `f`. The conclusion is existence of `T : D(R₁) →L[ℂ] D(R₂)` with `T(R₁∞(g)y) = R₂∞(g)(T(y))` for every `g` and `y`, and `T(e(v)) = f(v)` for every `v`, using the inclusion of `smoothKFinite ℝ n R₁`. Continuity is in the two genuine word-derivative topologies. The statement does not require `R₂` to be admissible, or either Banach space to be Hilbert.

This is a derived statement using Bernstein–Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, arXiv:0812.1684v3, registered as `bernstein-kroetz-2014-smooth-frechet-globalizations-arxiv-v3` (SHA256 `f5f2e79d87532c9ac46389d7eb1606e0301eac0ba7c7972ab628e278e091ca3e`), Theorem 10.6 and §10.4 (p.45) and Proposition 11.2 (pp.46–47). The theorem gives uniqueness of smooth Fréchet moderate-growth globalization in the form of goodness of the Harish-Chandra module; the proposition lifts a map into the compact-finite vectors of a smooth Schwartz-algebra representation to a continuous group map. In the proposed specialization, `e` gives the whole compact-finite module on the source, whose genuine actions must be shown to yield the source's Harish-Chandra module structure. Compact equivariance sends each finite-dimensional compact orbit span in `V` into a finite-dimensional compact orbit span, so `f` has the required target compact finiteness. A proof via Bernstein–Krötz must still compare `D(R₁)` with the unique globalization and place `D(R₂)` in the smooth Schwartz-algebra category, including the relevant topology, smoothness and growth comparisons. The Lean statement records the application of the lifting theorem, not those comparisons or a general categorical equivalence.

For the Hilbert comparison see also Getz–Hahn, *An Introduction to Automorphic Representations*, `getz-hahn-2024-automorphic-representations` (SHA256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`), §4.4, especially Theorem 4.4.14 (printed p.120, PDF p.135), with `getz-hahn-2024-errata-2026-10` (SHA256 `e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`), p.1. Here the compact-finite subspace of the smooth carrier, not the full smooth carrier, is identified with `V`. The extension statement is used in [SmoothHilbertTransposePairingReduction](SmoothHilbertTransposePairingReduction.md) with the continuous complex dual as the second Banach carrier.
