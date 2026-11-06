# Duality and actual common-closure induction

This internal algebraic unit specializes the proved continuous exact induction
identities to the actual common-closure Weil subgroups. Unfolding induction
exposes exact induction after restriction along the nested subgroup
equivalence. Contragredients commute with both operations. The norm characters
on both fields restrict the same base-field norm, so the continuous twisting
projection formula also applies. Consequently the norm-twisted contragredient
commutes with the actual common-closure induction map.

The trace-character identity uses the published evaluation formula and
additivity of the actual field trace. All character scaling uses the canonical
field topologies and their supplied local-field structures.

For a supplied system, the defect of an induced degree-zero element equals its
defect over the larger field with trace-pulled character. The proof applies the
system's degree-zero induction law separately to the element and to its
norm-twisted contragredient, which has the same zero dimension. The trace
identity aligns their inverse additive characters. The measures on both fields
are arbitrary; the transport theorem uses no Fourier inversion premise.

The integer-linear map `induceDualityKernel` restricts actual induction to the
intersection of the degree-zero submodule and the larger field's duality
kernel, with values in the smaller field's duality kernel. Its well-definedness
is precisely the proved defect transport identity.

No abelian epsilon identity, generation theorem, or unconditional functional
equation is asserted by these identities.
