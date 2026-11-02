# Conjugating the cocharacter-annihilator centralizer

This internal auxiliary development transports annihilator centralizers and
deduces standard-Levi conjugation under explicit finiteness and
standard-cocharacter existence hypotheses. It does not prove the general
`StandardLeviConjugationStatement` unconditionally.

For a commutative group scheme `T` over an arbitrary field `k : Type u`,
`cocharacterAnnihilator T J` is the integer submodule of all cocharacters
whose lattice pairing with every character in `J` is zero. It is defined as
the intersection of the kernels of those pairing functionals.
`mem_cocharacterAnnihilator` gives exactly this membership criterion.
For an automorphism `σ` and character subsets satisfying
`characterAut σ '' J' = J`, `cocharacterAut_mem_annihilator_iff` says that
postcomposition by `σ.hom` carries an annihilator member for `J'` to an
annihilator member for `J`, and conversely. This follows from the invariant
pairing and `annihilates_image_iff` in `StandardLeviRootTransport`.

`cocharacterAnnihilatorCentralizer_eq_comap` uses the actual normalizer
point `n` and its automorphism `normalizingAut i n`. It assumes a
monomorphic inclusion `i` and actual character-set transport
`weylAction i n '' J' = J`. Its conclusion is

```text
cocharacterAnnihilatorCentralizer i J' =
  (cocharacterAnnihilatorCentralizer i J).comap (G.innerIso n).hom.
```

The proof identifies the composite of each transported cocharacter with
`i` as the original composite followed by inner conjugation, using
`groupHom_cocharacterAut_comp`. The published
`Dynamic.centralizer_eq_comap_of_iso` transports its dynamic centralizer.
Pairing invariance transports the annihilation predicate, while
surjectivity of `cocharacterAut` reindexes the full intersection in the
other direction. Subgroup-functor and subgroup extensionality establish
the equality on every test scheme. This theorem requires neither
splitness nor finiteness, standard-cocharacter existence, genericity or
reductivity.

`standardLevi_eq_comap_of_finite_of_exists` additionally assumes an affine
ambient group, finitely many simple roots and a standard cocharacter for
each of `J` and `J'`. It rewrites both standard Levis with
`standardLevi_eq_cocharacterAnnihilatorCentralizer` from
`StandardLeviAnnihilator`, then applies the generic transport theorem.
The rewrite uses the positive integer shift and centralizing-cocharacter
submodule proved in that imported module; this file adds no structural
proof to it.

`standardLevi_eq_comap_of_rootSubset_image` assumes that `T` is split and
replaces the actual character-set transport premise with the exact
encoded-root-set premise in the public target. Membership of `J` and
`J'` in the relative roots follows from their standard-cocharacter
witnesses. The theorem then invokes
`weylAction_image_eq_of_relativeWeylAction_image_eq`. The encoded subsets
are sets of individual roots in the rational root span, not their linear
spans. The quotient is the actual `relativeWeylGroup i`, by the full
`centralizerPoints i`.

All results retain the field universe `u` and equality on every test
scheme. The proofs impose no characteristic restriction and allow empty
root sets and subsets. Finiteness of the simple roots and existence of
the two required standard cocharacters remain explicit in the
standard-Levi results. This file does not prove either of those
structural inputs or the separate lift-independence clause.

The provenance is internal: intersections of kernels, integer pairing
invariance, transport of dynamic centralizers, and the explicitly
conditional annihilator reduction in the named imported module. No
external source is claimed as an additional proof input.
