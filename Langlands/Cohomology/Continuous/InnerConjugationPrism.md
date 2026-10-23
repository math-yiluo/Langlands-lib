# The continuous degree-two inner-conjugation prism

This module defines one explicit construction on Mathlib's homogeneous continuous cochains. It takes a compact topological group `G`, a topological representation `A : TopRep k G` and an element `t : G`. It sends each homogeneous continuous two-cochain `f` to the homogeneous continuous one-cochain

  `innerConjugationPrism A t f : (x, y) ↦ f(x, x t, y t) - f(x, y, y t)`.

The module proves only that this is a well-defined homogeneous one-cochain and that it satisfies the displayed pointwise formula. It proves no differential identity, homotopy or cohomological statement.

## Cochains in Mathlib

Mathlib's `TopRep.homogeneousCochains A` (in `Mathlib.RepresentationTheory.Homological.ContCohomology.Basic`) is the complex of `G`-invariants of the resolution `TopRep.resolutionX A`. Its terms are `resolutionX A 0 = A` and `resolutionX A (n + 1) = (resolutionX A n).coind₁`. For a representation `π` on `V`, Mathlib's `ContRepresentation.coind₁ π` has carrier `C(G, V)` with the compact-open topology and the action `(g • F) x = π g (F (g⁻¹ * x))`. So an element `f` of `(homogeneousCochains A).X 2` is a nested continuous map `f.1 : C(G, C(G, C(G, A)))`. Each currying level is continuous for the compact-open topology, and `f.1` is invariant. Unwinding the action through the three levels, invariance reads pointwise

  `A.ρ g (f.1 (g⁻¹ * x) (g⁻¹ * y) (g⁻¹ * z)) = f.1 x y z` for all `g x y z : G`.

Likewise, an element of `(homogeneousCochains A).X 1` is an invariant element of `C(G, C(G, A))`.

## Declarations

- `innerConjugationPrismMap A t F : C(G, C(G, A))` is defined for any nested continuous map `F : C(G, C(G, C(G, A)))`, without assuming invariance. Mathlib's `ContinuousMap.uncurry`, applied twice, turns `F` into `F.uncurry.uncurry : C((G × G) × G, A)`; each application needs `LocallyCompactSpace G` (see below). This map is composed with the continuous substitutions `(x, y) ↦ ((x, x * t), y * t)` and `(x, y) ↦ ((x, y), y * t)` from `G × G`, whose continuity is proved by `fun_prop`. The two results are subtracted pointwise in `C(G × G, A)`, and `ContinuousMap.curry` turns the difference back into a nested map. Currying needs no hypotheses.
- `innerConjugationPrismMap_apply` (`@[simp]`, proved by `rfl`): `innerConjugationPrismMap A t F x y = F x (x * t) (y * t) - F x y (y * t)`.
- `innerConjugationPrismMap_mem_invariants A t f`: for `f : (homogeneousCochains A).X 2`, the map `innerConjugationPrismMap A t f.1` lies in `(TopRep.resolutionX A 2).ρ.invariants`. The proof evaluates `f.property g` at `(x, y, z)` to get the pointwise invariance above. Then for each `g` it computes `A.ρ g (s (g⁻¹ * x) (g⁻¹ * y))`, where `s` is the prism map. This equals `A.ρ g (f.1 (g⁻¹ * x) (g⁻¹ * x * t) (g⁻¹ * y * t)) - A.ρ g (f.1 (g⁻¹ * x) (g⁻¹ * y) (g⁻¹ * y * t))`, because `A.ρ g` is additive. Reassociating `g⁻¹ * x * t = g⁻¹ * (x * t)` and `g⁻¹ * y * t = g⁻¹ * (y * t)` and applying the invariance of `f` twice gives `s x y`. The invariance is diagonal: the same `g⁻¹` multiplies every variable on the left, while `t` multiplies on the right, so the two commute.
- `innerConjugationPrism A t f : (TopRep.homogeneousCochains A).X 1` packages `innerConjugationPrismMap A t f.1` with this invariance proof.
- `innerConjugationPrism_coe` (`rfl`): its underlying nested map is `innerConjugationPrismMap A t f.1`.
- `innerConjugationPrism_apply` (`rfl`), the formula theorem the task requires:
  `(innerConjugationPrism A t f).1 x y = f.1 x (x * t) (y * t) - f.1 x y (y * t)`.
  It is not tagged `@[simp]`, because `simp` does not index a lemma whose left side is the subtype coercion out of `(homogeneousCochains A).X 1`. Use it with `rw` (or the `@[simp]` lemma `innerConjugationPrismMap_apply` after `innerConjugationPrism_coe`).

## Hypotheses, universes and generality

The variables are `k : Type u` with `[Ring k] [TopologicalSpace k]`, `G : Type v` with `[Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]`, and `A : TopRep.{max v w} k G`, for independent universes `u v w`. The coefficients are an arbitrary topological representation; no commutativity, completeness, discreteness or finiteness is assumed. The carrier universe `max v w` is the form in which Mathlib's resolution `TopRep.resolutionX` (iterated `coind₁`, with carrier `C(G, -)`) and its cochains are available. This matches `Langlands.Cohomology.Continuous.InnerConjugation`. The Library's `CochainComparison` helpers are not used, because they require a common universe and a commutative ring.

Local compactness of `G` is the only topological input beyond the group structure, and the construction uses it only through `ContinuousMap.uncurry`. Mathlib supplies it by instance search: a compact space is weakly locally compact; a topological group is regular, hence R₁ (`IsTopologicalGroup.regularSpace`); and a weakly locally compact R₁ space is locally compact (`WeaklyLocallyCompactSpace.locallyCompactSpace`). The task contract lists `[T2Space G]` among the hypotheses, but nothing in the construction uses it, and Lean's unused-variable linter flags it. The module therefore omits it. Every declaration applies unchanged to compact Hausdorff `G`, where the extra instance is simply not needed.

## Provenance

This is a derived construction with no literature source. Its formula was chosen as the degree-two input to the proof in task `61e10fd6-fb8b-4939-b80c-ad8ef090626f` (Worker 134). That task proves the Library statement `Langlands.Continuous.InnerConjugationH2Triviality`, which says the inner-conjugation map `innerConjugationMap A a 2` of `Langlands.Cohomology.Continuous.InnerConjugation` is the identity on `continuousCohomology 2 A`, and its proof uses `t = a⁻¹`. Serre's *Local Fields* (literature ID `serre-1979-local-fields`, Chapter VII, §5, Proposition 3, printed page 116) states that the inner-conjugation automorphisms `σ_t` are the identity. This module does not formalize that proposition or any part of its proof, and the prism formula is not quoted from Serre. Shape of the formula: it has the two terms `f(x, x t, y t)` and `- f(x, y, y t)`, which insert one right-translated variable `x_i t` and right-translate all later variables, with alternating signs. That is the familiar prism pattern for a homotopy between the identity and right translation by `t`. This is motivation only: the module states no homotopy property, and its only mathematical claims are the well-definedness (continuity and invariance) and the pointwise formula above.
