# Matched generators of finite modules over a split square

`Langlands.Analytic.BoundedAlgHom.SplitSquareModuleGenerationStatement` is an
unproved proposition definition. It is an intermediate statement for the proof
of `Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescentStatement`,
not an axiom.

## Statement

Data:

- a normed field `K` (no ultrametric or completeness assumption);
- normed commutative `K`-algebras `A`, `A₁`, `A₂`, `A₁₂`, all in one universe,
  where `A₁` and `A₂` are complete;
- bounded `K`-algebra maps `p₁ : A → A₁`, `p₂ : A → A₂`, `r₁ : A₁ → A₁₂`,
  `r₂ : A₂ → A₁₂` that form a `BoundedAlgHom.SplitSquare` (the Library
  structure of `SplitSquareIdealDescent`: the square commutes, compatible pairs
  glue, `r₂` has dense range, and every element `h` of `A₁₂` splits as
  `r₁ h₁ + r₂ h₂` with `‖h₁‖, ‖h₂‖ ≤ bound · ‖h‖`). Only the existence of such
  a structure is assumed.
- an `A₁`-module `M₁`, an `A₂`-module `M₂` and an `A₁₂`-module `M₁₂` (in a
  common universe), with additive maps `u₁ : M₁ → M₁₂` and `u₂ : M₂ → M₁₂`
  that are semilinear along `r₁` and `r₂`: `u₁ (a • m) = r₁ a • u₁ m` and
  `u₂ (a • m) = r₂ a • u₂ m`.

Hypotheses: `M₁` is finitely generated over `A₁`, `M₂` is finitely generated
over `A₂`, and each of the images `u₁(M₁)` and `u₂(M₂)` spans `M₁₂` over
`A₁₂`.

Conclusion: there are `n : ℕ`, `x : Fin n → M₁` and `y : Fin n → M₂` with
`u₁ (x k) = u₂ (y k)` for every `k`, such that the `x k` span `M₁` over `A₁`
and the `y k` span `M₂` over `A₂`.

No norms on the modules are involved, and the gluing and commutativity fields
of the split square are carried along but not needed for the conclusion.

## Provenance

This is the module-generation half of the Cartan-type gluing lemma used in the
proof of Kiehl's Theorem A for coherent modules on affinoid spaces: over a
binary cover whose overlap algebra splits boundedly and is approximated by one
side, finitely many matched local sections generate both sides. Kiehl's theorem
in the generality needed here (arbitrary complete non-Archimedean `K`, possibly
trivially valued, and non-strict affinoid algebras) is stated in Berkovich,
*Étale cohomology for non-Archimedean analytic spaces* (1993), Kiehl's Theorem
and Remark 1.2.1(ii), printed p.15 / PDF p.12 (registered source
`berkovich-1993-etale-cohomology`), and in Berkovich, *Spectral theory and
analytic geometry over non-Archimedean fields* (1990), Proposition 2.3.1,
printed p.33 / PDF p.47 (registered source
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`),
which deduces it from Kiehl's original *Theorem A und Theorem B in der
nichtarchimedischen Funktionentheorie* (cited there as [Ki2], not registered
here).

The abstract formulation over the Library's `SplitSquare` structure is a
derived internal statement. The intended proof is the classical matrix
argument: choose generators of both modules, express each family in terms of
the other over `A₁₂`, use density of `r₂` to make the resulting transition
matrix close to the identity, factor it as `r₂(E₂) · r₁(E₁)` with invertible
matrices over the complete algebras `A₂` and `A₁` by iterating the bounded
splitting, and finally adjoin matched corrections of the generators of `M₂`
obtained by splitting their coefficients.
