# Descent of homomorphisms along small étale covering families

This internal derived module descends compatible actual group-scheme maps along
an arbitrary small étale covering family. Compatibility compares their values on
every test with equal original-source projection, including different cover
members. Neither the base nor either group scheme is assumed affine.

`effectiveFamily` constructs an effective epimorphic family structure from the
single effective epimorphism out of the coproduct. Étale maps are stable under
coproducts; joint surjectivity gives a surjective étale coproduct map, which is
an effective epimorphism by the published fppf result. Pullbacks of the scheme
coproduct injections decompose each scheme over that coproduct, giving the
remaining hypothesis of the general effective-family construction.

Apply this construction to the cover pulled back along the source group scheme.
`underlying` descends the actual local scheme maps, and `underlying_fac` records
their exact recovery. Cover restrictions detect equality, so the descended map
retains its base map. `pullback_overHom` gives exact recovery in the slice.

The pointwise product of the cover slice categories has its cartesian monoidal
structure. The family of given group homomorphisms is a homomorphism between the
restricted group objects. Since restriction is faithful and monoidal, it reflects
the unit and multiplication laws. Thus `hom` is the actual descended group-scheme
homomorphism, uniquely characterized by its cover restrictions.

`iso` glues supplied actual local isomorphisms when both their forward and
inverse maps satisfy the all-test compatibility condition. Restricting their
composites proves the two global inverse identities. `baseChange_iso` records
exact recovery of every supplied local isomorphism. All constructions are in an
arbitrary universe and allow empty covering members and empty bases.

The provenance is internal: the module combines published effective epimorphism,
scheme coproduct decomposition, and faithful monoidal reflection results. It
introduces no new geometric assumptions or external literature claims.
