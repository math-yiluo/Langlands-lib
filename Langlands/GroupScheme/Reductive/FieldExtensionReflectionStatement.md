# Statement: connected reductivity and pseudo-reductivity under arbitrary field extension

Worker 3483.

This module defines three propositions and proves none of them:

- `Langlands.GroupScheme.ConnectedReductiveFieldExtensionIffStatement.{u}`;
- `Langlands.GroupScheme.PseudoReductiveFieldReflectionStatement.{u}`;
- `Langlands.GroupScheme.FieldExtensionReflectionStatement.{u}`, the conjunction of the
  first two.

The package is the proof target; its two components are named so that either can be used
separately. The only import is [`Reductive.Basic`](Basic.md), which defines
`IsConnectedReductive` and `IsPseudoReductive`. The module adds no other definitions,
theorems or axioms.

## Quantifiers and base change

The universe `u` is arbitrary. Each component quantifies over every pair of fields
`k K : Type u`, every `Algebra k K`, and every group scheme
`G : GroupScheme (Spec (CommRingCat.of k))`. There is no condition on the extension: it may
be transcendental, inseparable or infinite. There is no condition on `G` either: smoothness,
affineness, connectedness and finite type are not inputs. Write

```text
b   = Spec.map (CommRingCat.ofHom (algebraMap k K)) : Spec K ⟶ Spec k,
G_K = (GroupScheme.baseChange b).obj G,
```

the pullback of `G` along `b` with the induced group law. These abbreviate the terms
written inline in Lean.

## The two components

1. `ConnectedReductiveFieldExtensionIffStatement`:
   `IsConnectedReductive G ↔ IsConnectedReductive G_K`. The published predicate
   `IsConnectedReductive` says that the group is smooth, affine and connected over its base
   field and that its base change to an algebraic closure (`AlgebraicClosure`) has trivial
   unipotent radical.
2. `PseudoReductiveFieldReflectionStatement`:
   `IsPseudoReductive G_K → IsPseudoReductive G`. The published predicate
   `IsPseudoReductive` says that the group is smooth, affine and connected over its base
   field and that `HasTrivialUnipotentRadical` holds over that field itself: every smooth
   connected unipotent closed subgroup with normal image is trivial.

The second component is one direction only. The converse fails in general:
Conrad–Gabber–Prasad, Example 1.1.3, printed p.4 (PDF p.30), gives over every imperfect
field a pseudo-reductive group `R_{k'/k}(GL_1)` that is not reductive, so its base change
to an algebraic closure is not pseudo-reductive.

## Sources and provenance

**Component 1** is J. S. Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, Proposition 19.13, printed p.400 (PDF p.416):

> PROPOSITION 19.13. Let G be an algebraic group variety over k, and let k' be a field
> containing k. Then G is reductive if and only if G_{k'} is reductive.

with proof "similar to that of Proposition 19.5". Milne's reductive groups are connected:
6.46, printed p.135 (PDF p.151), "A connected group variety over a field k is said to be
reductive if G_{k^a} is reductive, i.e., if its geometric unipotent radical R_u(G_{k^a})
is trivial." This is `IsConnectedReductive`.

Milne's `G` is an algebraic group variety (smooth and of finite type), while the Lean
statement allows any group scheme `G`. For the forward direction, `IsConnectedReductive G`
already makes `G` smooth and affine, so nothing is added. For the backward direction, the
hypothesis `IsConnectedReductive G_K` must give the smoothness, affineness and
connectedness of `G` itself. These properties descend along `Spec K → Spec k`, which is
faithfully flat and quasi-compact; the Library proves this descent (see "Relation to the
Library"). So the Lean form states Milne's equivalence without assuming that `G` is a group
variety.

**Component 2** is derived from Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd
edition (2015), source ID `conrad-gabber-prasad-2015-pseudo-reductive`:

- Definition 1.1.1, printed p.3 (PDF p.29): "Let k be a field, G a smooth affine k-group.
  The k-unipotent radical R_{u,k}(G) (resp. k-radical R_k(G)) is the maximal smooth
  connected unipotent (resp. solvable) normal k-subgroup of G. A pseudo-reductive k-group
  is a smooth connected affine k-group G such that R_{u,k}(G) = 1." This is
  `IsPseudoReductive`: the radical is trivial exactly when every smooth connected
  unipotent normal closed `k`-subgroup is trivial.
- Proof of Proposition 1.1.9, printed p.9 (PDF p.35): "Since R_{u,k}(G)_K ⊆ R_{u,K}(G_K)
  in general, to prove the equality as in (1) it suffices to prove an inequality of
  dimensions in the opposite direction when k = k_s." Here `G` is a smooth connected
  affine `k`-group and `K/k` is a field extension.

If `G_K` is pseudo-reductive, then `R_{u,K}(G_K) = 1`, so `R_{u,k}(G)_K = 1` by the quoted
inclusion and `R_{u,k}(G) = 1`. Together with the descent of smoothness, affineness and
connectedness from `G_K` to `G`, this is component 2. CGP state this inclusion inside a
proof and do not state the reflection as a numbered result, hence "derived". Proposition
1.1.9(1), printed p.8 (PDF p.34), states the equivalence "G is pseudo-reductive over k if
and only if G_K is pseudo-reductive over K" for **separable** `K/k`; the Library records
that in `SeparableAlgebraicUnipotentRadicalStatement` (separable algebraic `K/k`) and
`PseudoReductiveSeparableExtensionStatement` (ascent). Component 2 is the direction that
holds for every extension.

## Relation to the Library

- `ConnectedReductiveFieldExtensionStatement` in
  [`Reductive.FieldExtensionStatement`](FieldExtensionStatement.md) is the forward direction
  of component 1 for every extension. `ConnectedReductiveAlgebraicExtensionReflectionStatement`
  in [`Reductive.AlgebraicExtensionReflectionStatement`](AlgebraicExtensionReflectionStatement.md)
  is the backward direction for algebraic extensions only. No published proposition
  declaration states the backward direction, or the equivalence, for every extension.
- The published theorems `IsConnectedReductive.of_fieldExtension` and
  `HasTrivialUnipotentRadical.of_fieldExtension` (module
  `Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof`) and the descent results
  `smooth_of_baseChange`, `connectedSpace_of_baseChange`
  (`Langlands.GroupScheme.Rational.UnipotentRadicalProperties`) and
  `Langlands.AlgebraicGeometry.fieldExtensionAffineDescent`
  (`Langlands.AlgebraicGeometry.FieldExtensionAffineDescentProof`) contain the mathematics
  of both components. They are theorems with hypotheses, not named closed propositions.
  The family 3 ledger records both components as missing only a named statement and its
  wrapper theorem.
- `SemisimpleFieldReflectionStatement` in
  [`Reductive.SemisimpleFieldReflectionStatement`](SemisimpleFieldReflectionStatement.md) is
  the analogue for semisimplicity.

This module proves none of these relations.
