# Concatenation of actual segment-product data

Author: Worker 494.

This internal construction starts with an ordered outer shape `D` and an actual
segment-product datum `a k` of rank `D.size k` at each outer slot. It concatenates
all supplied occurrences and their actual blocks in the consecutive order of
`finSigmaFinEquiv`. The resulting datum has the total outer rank, and its shape
is the canonical flattening of the shapes of the inner data.

The complete block list is the flattening of the list of complete inner block
lists. The segment list has the corresponding formula. The finite-list lemma
proves this using the consecutive dependent-fiber numbering, splitting its last
outer slot, and applying induction to the preceding slots. Concatenation inherits
the strong segment-socle property whenever every supplied inner datum has it.

`concatenateInducedEquiv` uses the exact canonical flattened coordinate identity
and the independently proved closed ordered regrouping theorem. Each recovered
refinement datum equals its original supplied inner datum by complete block-list
equality. Induction of these actual factor equivalences, followed by inversion
of the regrouping map, gives an actual representation equivalence from the outer
product of the supplied inner products to the concatenated flat product.

The provenance is internal finite-list bookkeeping and composition of the
published flattening and actual refinement constructions. The input inner data
remain arbitrary supplied actual data; no segment socle, commutation, linked
reduction or classification result is proved. The field and segment carrier
universes are independent, the field prime and supplied topology are arbitrary,
and the total rank and outer length may be zero.
