# Bounded configurations with free and finite character groups

The namespace `Langlands.Algebra.MixedLatticeConfiguration` extends
the published free-lattice configuration argument to
`Λ = (r → ℤ) × F`, where `r` and `F` are finite for the bounded
configuration theorem and `F` is an additive commutative group.
This is an internal construction for multiplicative-type subgroup
charts, adapted from `LatticeConfigurationBound`; it has no claimed
direct counterpart in the literature.

`combination S φ` is the additive map from integer coefficients on a
finite set `S` to the sum of the coefficients times their prescribed
values under `φ`. For an arbitrary additive commutative group,
`exists_hom_of_relations` says that prescribed values on a finite
generating set extend to an endomorphism if they preserve all integer
relations. The proof factors the combination map through the
surjective combination map for the original generators.

`mred r F m : Λ →+ (r → ZMod m) × F` reduces the free coordinates
modulo `m` and keeps the finite component. It is surjective for every
`m`. An element reducing to zero is zero when the sum of the absolute
values of its free coordinates is less than `m`; the finite
component is already zero because it is retained by reduction.
`mbox r F n` is the product of the free-coordinate box of radius `n`
and all of `F`.

`exists_bound r F n` supplies a uniform lower bound on `m` such that
any map from a generating subset of this box into the same box
extends to an endomorphism of `Λ`, provided its reduction agrees
with an endomorphism of `(r → ZMod m) × F` on that subset.
There are finitely many subsets and maps of the box. For every bad
configuration, choose a relation that is not preserved. Take a bound
larger than the free-coordinate sizes of all such chosen relation
images. Compatibility modulo a larger `m` forces the chosen image
to reduce to zero, and the small-coordinate lemma then makes it zero,
contradicting its choice.

Finally, `exists_mred_comp` and `exists_mred_equiv` descend an
endomorphism or automorphism of `Λ` to the reduced group when
`∀ x : F, m • x = 0`. This annihilation hypothesis is explicit and
essential to these two results; it is not needed by `exists_bound`.
An element in the kernel of reduction is an `m`-multiple of a vector
with zero finite component. Its image still reduces to zero since
`m` annihilates `F`, so the quotient factorization exists. Applying
this to an automorphism and its inverse gives mutually inverse
induced endomorphisms.
