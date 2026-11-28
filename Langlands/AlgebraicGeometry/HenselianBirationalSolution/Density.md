# Density in the fibres

A set `W` is `FibreGenerizationDense` over a morphism if each point admits a
generization in `W` with the same image in the base. To lift such a generization
after base change, `exists_generization_of_isPullback` passes to the scheme fibre,
where the base change is along a residue-field extension. That extension is flat,
so the induced morphism of fibres is generalizing.

The other lemmas preserve density by enlarging the set, intersecting with a
fibrewise dense open, and taking the inverse image by an open immersion over the
base. These are the fibrewise density operations used in the associativity
calculation of BLR, *Néron Models*, §5.3 Lemma 1, p. 120.
