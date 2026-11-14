# Algebraic boundedness under ground-field restriction

`FieldRestrictedRootFiltrationBoundedStatement` and its proof
`fieldRestrictedRootFiltrationBounded` express descent of algebraic bounds on
actual root filtrations. They hold at arbitrary universe and arbitrary real
depth.

Let `K/k` be any extension of fields with compatible valuative relations,
and assume `IsValuativelyCofinal k K`: every extension element is dominated
by the image of some nonzero base element. Let `G` be a smooth affine group
scheme over `k`, let `S` be a split torus, and let `i : S.toGrp ⟶ G`. For
any actual upper root-function family, nonzero character `a` of `S`, and
real depth `r`, boundedness of its upper filtration at the base-changed
character implies boundedness of the filtration of the field-restricted
family at `a` and the same depth `r`. No root-datum valuation or torus
maximality assumption is needed.

The proof uses the published exact preimage formula
`rootFiltration_fieldRestrict`. The supporting lemma
`isAlgebraicallyBounded_preimage_rationalExtend` first identifies the actual
rational extension map with `geometricRationalPoint`, by the published
rational-point comparison. The image of the preimage of a bounded set is a
subset of that set, and so is bounded. The published cofinal descent theorem
then bounds every original regular function over the prescribed base relation.

The accompanying `HenselianSeparableValuedBounds` pair constructs the required
compatible cofinal relation for any separable extension of a henselian field
equipped with a compatible surjective integer valuation. Its additive order is
the normalized henselian separable additive valuation already used in the
quasi-split apartment construction. This supplies cofinality without assuming
that the base field is complete or has finite residue field.

The provenance is internal: the statement and proof combine the existing
field-restriction identity, the actual point-map comparison, monotonicity of
algebraic boundedness, and cofinal descent. Upper-filtration boundedness remains
an explicit premise. These results do not construct bounded apartments or prove
the unconditional maximal-unramified target.
