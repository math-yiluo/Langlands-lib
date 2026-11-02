# Finite sums of finite étale subgroup images

This is an internal deduction from the Library's actual categorical products
of group schemes, the finite-limit geometry of finite étale covers, and
`Langlands.GroupScheme.FiniteEtaleImage`. It provides the finite sum subgroup
needed when a finite family of integral endomorphisms is restricted to torsion.
There is no external literature assertion or geometric existence axiom.

For an arbitrary base scheme `S : Scheme.{u}`, a finite indexing type
`I : Type u` with its `Fintype` structure, and finite étale group schemes
`G i`, `finiteEtale_pi` proves that their categorical product is finite étale
over `S`. The source groups need not be commutative for this assertion.
The accompanying instances expose its finite and étale structure morphism.

The proof first establishes `coverProperty_isClosedUnderFiniteProducts`.
The existing closure of finite étale covers under terminal objects and
pullbacks gives finite limits in their full subcategory, preserved by the
inclusion into `Over S`. Closure under isomorphisms follows by composing a
finite étale structure morphism with the inverse scheme isomorphism.
Preservation of finite limits then gives closure under finite products.
The previously published `GroupScheme.piIsLimit` supplies the limiting fan
on the underlying object of the actual group-scheme product. Applying this
closure property to that fan proves the claimed geometry.

Let `H` be a commutative finite étale group scheme and
`f i : G i ⟶ H` a family of actual group-scheme homomorphisms. `sumMap f`
is the homomorphism

\[
  \prod_{i:I}G_i \longrightarrow H,\qquad
  (x_i)_i\longmapsto\sum_i f_i(x_i).
\]

In Lean, Hom groups in `Grp (Over S)` use multiplicative notation for the
pointwise group law, so this is `∏ i, Pi.π G i ≫ f i`. Multiplication in
this expression means addition in the commutative target; it is not
composition of endomorphisms. The definition of `sumMap` itself needs
commutativity of the target and the finite indexing type, with no finite
étale hypotheses.

`image f` is `FiniteEtaleImage.image (sumMap f)`, hence an actual finite
étale commutative group scheme over `S`. Its `inclusion f` into `H` is
both an open and a closed immersion. Its `projection f` from the product
is a finite étale surjective homomorphism, and projection followed by
inclusion is `sumMap f`. These properties are inherited from the imported
image construction. In particular, this uses an actual open subscheme
with the ambient structure sheaf, including its possible nilpotents.

For the factorization and vanishing results, assume each `G i` is also
commutative. `coordinate i` inserts the identity on coordinate `i` and
the trivial homomorphism on the other coordinates. Its composite with
`sumMap f` equals `f i` (`coordinate_sumMap`): precomposition distributes
over the finite pointwise product, and all but one factor are trivial.
`component f i` is this coordinate insertion followed by the projection
onto `image f`. The theorem `component_inclusion` proves

\[
  \operatorname{component}_i\ ;\ \operatorname{inclusion}=f_i.
\]

For any commutative group scheme `J` over `S` and any homomorphism
`g : H ⟶ J`, `inclusion_comp_eq_one_iff` proves that `g` kills `image f`
exactly when every `f i ≫ g` is trivial. No finiteness or étaleness
assumption is imposed on `J`. One direction uses the component
factorizations. Conversely, composition with `g` distributes over the
finite pointwise product, so `sumMap f ≫ g` is trivial; the imported
surjective-image criterion implies the result on `image f`. The numeral
`1` in the Lean formula is the trivial group-scheme homomorphism.

The construction includes an empty indexing type and arbitrary base
schemes, without reducedness, connectedness, or field assumptions.
It does not yet restrict endomorphisms to an abelian scheme's torsion,
construct a quotient abelian scheme, integralize a rational ring action,
or prove CM representability.
