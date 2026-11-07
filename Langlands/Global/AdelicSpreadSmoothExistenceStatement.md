# Compatible smooth arithmetic models of a field morphism

Author: Worker 208.

This statement isolates the compatible-model step in the first and third
paragraphs of the proof of Conrad's Theorem 4.5, printed p.12 of *Weil and
Grothendieck approaches to adelic points* (December 31, 2011). Its general
spreading source is Theorem 3.4(1),(2) and Remark 3.5, printed pp.5–6.
The registered source is `conrad-2011-weil-grothendieck-adelic-points`,
PDF SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
This module states propositions and supplies no proofs.

## Exact objects and conclusions

The two `SpreadMorphismPropertyExistenceStatement` definitions are proposition
templates, parameterized by a property `P` of actual scheme morphisms. They
make no assertion that every property can be spread.

Each template quantifies over two separated finite-type schemes `Y`, `W`
over the original field, a morphism `g : Y ⟶ W` over that field, an initial
finite set `S`, and the hypothesis `P g.left`. Finite type is expressed as
local finite type and quasi-compactness of each structure morphism.
The conclusion supplies a finite set `T` containing `S`, actual separated
finite-type models `M`, `N` over the original ring of outside-`T` integers,
generic-fibre isomorphisms `e`, `f` to `Y`, `W`, and a model morphism
`gm : M ⟶ N` satisfying `P gm.left`.

The generic-fibre compatibility is an equality of actual morphisms:

```text
(generic-fibre pullback of gm) ≫ f.hom = e.hom ≫ g.
```

The pullback uses `Spec.map` of the literal inclusion of the original
integer subring into the original field. Neither the field nor its
integer rings are replaced by abstract isomorphic objects. The models
may be nonaffine; no model is an input.

For each arithmetic branch, `SpreadSmoothExistenceStatement` asserts this
existence template for smoothness, and, for every fixed natural number
`d`, for the conjunction of smoothness and
`NonemptyGeometricallyConnectedPureDimensionFibers d`. In the second
clause a single pair of models and a single model morphism satisfy both
properties. No single finite level is required to work for every morphism
or every dimension.

The fibre predicate is the published predicate on every actual
residue-field fibre of the model morphism. It requires explicit
nonemptiness, geometric connectedness over that residue field, and
dimension `d` for every irreducible component with its subspace topology.
It implies surjectivity of the model morphism. This clause starts with
the same full fibre predicate on `g`; it does not choose a dimension or
decompose the original target. The smoothness-only clause needs no
surjectivity, nonemptiness, connectedness or dimension hypothesis.

`AdelicSpreadSmoothExistenceStatement` is the conjunction of the two
arithmetic branches in an arbitrary common universe.

## Source relation and derived scope

The function-field branch retains the actual `FunctionField k F` and
compatible `k` and `RatFunc k` actions, with `k` any perfect field.
The number-field branch retains every number field and its actual finite
places. The output level contains the prescribed initial finite set,
which may be empty. Infinite number-field places impose no integer-ring
condition, so they do not appear in this finite-place index.

The source's proof of Theorem 4.5 first chooses compatible smooth
surjective models with geometrically connected fibres and later reduces
to a common fibre dimension. The second clause states the fixed-dimension
compatible existence step after that reduction. The first clause is the
smoothness specialization of Theorem 3.4, without the extra fibre
hypotheses needed for Theorem 4.5.

The derivation uses existence of separated arithmetic models for each
field scheme, descent of the given morphism, and eventual detection of
the specified properties at a common enlargement. The original integer
rings are noetherian, so these finite-type models are finitely presented.
The published arithmetic colimits justify the extension to empty
initial sets and arbitrary perfect function-field constants; the
argument does not require finite constants or separability over the
chosen rational-function field. These scope extensions and the
property-template packaging are derived content.

This statement supplies compatible models and the generic-fibre square.
The connected-component dimension reduction, Lang–Weil estimates,
integral-point lifting and the adelic openness theorem remain separate
obligations.
