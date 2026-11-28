# Existence of `β`-extensions for a maximal order

Module: `Langlands.BushnellKutzko.MaximalOrderBetaExtensionStatement`.

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open
subgroups* (1993):
- Theorem (5.2.2)(i), printed p. 166 (PDF p. 178);
- Definition (5.2.1) of `β`-extensions, printed p. 166;
- Theorem (5.2.3)(i), printed p. 167 (PDF p. 179), with (5.2.4), printed pp. 167–169;
- Proposition (5.2.7), printed p. 170 (PDF p. 182), whose proof runs to printed p. 175 and uses
  Proposition (7.2.11), printed p. 219 (PDF p. 231).

## Statement

`MaximalOrderBetaExtensionStatement` quantifies over:
- a nonarchimedean local field `F` and an `F`-vector space `V`, each in its own universe;
- an additive character `ψ_F` with the conductor fixed by `IsBKAdditiveCharacter`;
- a simple stratum `[𝔄, n, 0, β]` in `End_F(V)` and a defining-sequence choice;
- `θ ∈ C(𝔄, 0, β)`;
- a representation `η` of `J¹(β, 𝔄)` lying over `θ` (`IsHeisenbergRepresentation`), on a space in
  a third universe.

The stratum is required to satisfy one further condition: the period of the lattice chain of
`𝔄` equals `elementRamificationIndex F β`, the ramification index `e(E|F)` of `E = F[β]`. By
BK93 (1.2.4), the period of the `𝔬_E`-lattice chain underlying `𝔅 = 𝔄 ∩ End_E(V)` is
`e(𝔄|𝔬_F) / e(E|F)`. So the condition says that this period is `1`, that is, `𝔅` is a maximal
hereditary `𝔬_E`-order (the situation of `𝔅_M` in BK93 (5.1.12) and (5.2.3)).

The conclusion: `η` has a `β`-extension (`IsBetaExtension`, BK93 (5.2.1)) on a space `ℂ^d`.
That is, there is a finite-dimensional smooth representation `κ` of `J(β, 𝔄)` whose restriction
to `J¹(β, 𝔄)` is equivalent to `η` and which is intertwined by every element of `B^×`, the
centralizer of `β`.

## Relation to the source

In BK93 this is the case `𝔅 = 𝔅_M` of Theorem (5.2.2)(i). For maximal `𝔅`, the source obtains
it as follows. (5.2.4) constructs an extension `κ_M` of `η` (a statement of (5.2.3)(i)), and
(5.2.7) shows that `κ_M` is intertwined by `B^×`. The proof of (5.2.7) for the maximal order
occupies printed pp. 170–175: the Cartan form (5.2.8) of `y ∈ B^×`, the block orders (5.2.9),
Lemmas (5.2.10)–(5.2.11), the relations (5.2.12)–(5.2.13), and Proposition (7.2.11) on the
Iwahori decomposition relative to a subordinate `E`-decomposition of `V`. The general case of
(5.2.2)(i) is reduced to this one in the source through (5.2.5) and the first paragraph of the
proof of (5.2.7). This statement contains only the maximal case.
