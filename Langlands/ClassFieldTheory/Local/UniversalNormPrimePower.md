# Prime-power divisibility of actual universal norms

This derived support unit defines `Langlands.LocalClassField.universalNormSubgroup
K` for any field `K : Type u`. Its elements are exactly the units that lie in
`normSubgroup K E` for every actual intermediate field
`E : IntermediateField K (AlgebraicClosure K)` with finite-dimensional and abelian
Galois instances. The construction uses the actual determinant norm. Closure
under the unit group operations follows pointwise from the norm subgroups.
No topology or local-field hypothesis enters this definition.

`exists_not_norm_of_cyclic_coordinate` works over any actual `PadicField F` of
arbitrary universe, with a finite Galois extension `L` in that same universe.
It assumes a multiplicative equivalence from `Gal(L/F.Carrier)` to the additive
cyclic group `ZMod n`, written multiplicatively, where `n` is nonzero, and that
the extension degree is greater than one. Its conclusion is a base unit outside
the actual norm subgroup. There is no supplied reciprocity or norm-index law.

The proof uses `localInvariantFamily unramifiedH2Exhaustion p`, its proved
relative-image law, and `InvariantFamily.relativeZModEquiv` to identify actual
relative H² with `ZMod` of the extension degree. The inverse image of `1` is
nonzero because that degree exceeds one. Surjectivity of the cyclic carry-class
map supplies a unit representing this class. The cyclic-class norm criterion
then shows that the unit is not a norm.

`universalNorm_is_prime_power` assumes that `q` is prime, that the base contains
a specified unit whose field value is a primitive `q`th root of unity, and that
`a` lies in every actual finite abelian intermediate norm subgroup. It concludes
`∃ c : F.Carrierˣ, c ^ q = a`. Its universal-norm assumption is written out
explicitly with the same quantifiers as the subgroup definition, for direct use
by consumers. The residue characteristic and `q` may coincide; the field is an
actual finite extension of `Q_p` throughout.

For the proof, assume `a` is not a `q`th power of a unit. Any field root would be
nonzero, so the prime-binomial irreducibility criterion applies. The actual
radical field of `a` is thus finite abelian of degree `q`. The preceding theorem
produces a unit `b` that is not a norm from it. A `q`th power in the base is the
norm of its base root included in this degree-`q` extension, by the determinant
norm formula on base scalars. Hence `b` is not a `q`th power either, and its
radical field is also finite abelian. Universality of `a` makes it a norm from
that second field. `radicalField_norm_iff` then makes `b` a norm from the first,
contradicting its choice.

The mathematical provenance is Serre, *Local Fields* (1979), XIV §2, the corollary
to Proposition 7 on printed page 209: with the roots of unity in the base, the
intersection of cyclic norm groups is the group of powers. This unit implements
the prime-order direction needed for separation. It derives norm-quotient
nontriviality from the already proved local relative invariant, and uses the
explicit carry-class norm symmetry rather than introducing a Hilbert symbol.
It does not assert unrestricted divisibility without roots of unity, preservation
of universality for a chosen root, or unconditional norm separation. Those remain
separate arithmetic and topological obligations.
