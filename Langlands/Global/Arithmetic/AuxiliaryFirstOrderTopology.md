# Actual intermediate-field topology and norm comparison

Worker 84 implements comparison helpers for the existing auxiliary-character
target. The intermediate p-adic presentation has the same field carrier and
p-adic algebra as L. Its supplied topology is compared to the actual subtype
topology inherited from the ambient canonical norm, not to an unrelated chosen
topological field.

The actual intermediate-field inclusion induces a normed p-adic algebra from M.
Finite-dimensionality through F gives the module-topology certificate on L.
Every supplied realization of the intermediate presentation already has this
same module topology, so the two topology uniqueness equalities give the stated
equality. For the norm comparison, the public canonicalNorm_map theorem applied
to that exact base-linear inclusion identifies the intermediate spectral norm
with the ambient restricted norm pointwise.

transportUnitCharacter transports a continuous character along the proved
equality of topologies; its value lemma proves pointwise equality with the
original character by equality induction.

These helpers justify later transport of a continuous character constructed in
the supplied intermediate topology to the topology in AuxiliaryCharacterStatement,
and conversion of its depth bounds to the actual ambient norm. They do not
construct such a character or prove a depth witness. Their use in the final assembly and all other helper modules belongs to the
same independent proof review.
