# The actual torsion-scheme trivialization from a supplied full level

This internal construction uses a supplied ordered full level, the enumeration
in `FullLevelEnumeration`, and the published theorem `torsionFiniteEtale`.
It constructs no new full level and uses no generic numerical torsion-rank
theorem.

At positive level invertible on the base, every enumerated torsion section
is an open immersion. The private section lemma follows from the open
diagonal of a locally finite type unramified morphism and the base-change
criterion for cancellation of a morphism property under postcomposition.
The composite of the section with the torsion structure map is the identity.

The enumerated sections cover the underlying torsion scheme: for each point,
pass to the algebraic closure of its residue field and apply the geometric
enumeration bijection. Distinct coefficient tuples have disjoint images.
Indeed, a common point would give a geometric point in both open images;
the open-immersion lifting property factors this geometric point through
both sections. Uniqueness of its coefficient tuple then identifies the two
indices.

`torsionCoproductMap` is the actual scheme map from the coproduct of copies
of the base indexed by `Fin (2*g) → ZMod n`. Its restriction to each
component is the corresponding actual torsion section. For a full level,
the disjoint open images make this map an open immersion and the covering
argument makes it surjective, hence an isomorphism.
`FullLevel.torsionCoproductIso` packages this as an isomorphism in `Over S`,
with the coproduct structure map induced by the identity on each copy of
the base.

All bases and morphisms are the existing actual schemes; reducedness,
connectedness and noetherianity assumptions are unnecessary. The result is
an isomorphism of schemes over the base. A group structure on the
coproduct is not packaged here. This does not prove rigidity of the
original abelian-scheme automorphism, a projective embedding or ordinary
moduli representability.
