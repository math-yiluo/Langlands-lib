# Isomorphisms of supplied families and their full-level parameters

For a scheme `S`, supplied abelian schemes `A, B` over `S`, and an actual
isomorphism `e : A ≅ B`, this internal construction gives an actual
isomorphism over `S`
`fullLevelParameterIso g n hn hunit e` between their full-level parameter
schemes. Here `g, n` are natural numbers, `hn : 0 < n`, and `hunit`
says that `n` is invertible in the global sections of `S`. The conclusion
does not require a relative-dimension hypothesis or the existence of
any full level.

The construction begins with `torsionTupleIsoHomEquiv`: for every actual
test scheme `T` over `S`, it transports maps into the ordered-tuple
parameter by the original linear torsion equivalence
`levelIsoLinear e T n` on each coordinate in `Fin (2 * g)`.
`torsionTupleIsoHomEquiv_apply` records this coordinate formula.
The comparison commutes with every actual test-scheme morphism
(`torsionTupleIsoHomEquiv_comp`) and respects identity and composition
of actual family isomorphisms.

The decoded ordered sections agree through the actual family
isomorphism pulled back to `T`:
`torsionTupleIsoHomEquiv_sections` identifies the transported tuple with
`mapTuple ((baseChange T.hom).mapIso e).hom` applied to the original
decoded tuple. Its proof uses `sectionTupleBaseChangeEquiv_mapIso`,
checked on actual underlying section maps and the first projections of
the scheme pullbacks. Transporting the prescribed geometric-fibre
bases through this isomorphism preserves fullness. Applying its inverse
and cancelling the actual section maps proves the converse, giving
`isFull_torsionTupleIsoHomEquiv_iff`.

Restricting this equivalence to the subtype of full tuples and using
the existing classification by maps into the full-level parameter
defines `fullLevelParameterIsoHomEquiv`. Its inclusion formula retains
the tuple comparison exactly. Its naturality theorem quantifies over
every actual test-scheme map, and its sections theorem retains the same
ordered-section formula. It also respects identity and composition of
family isomorphisms.

Mathlib's `Yoneda.ext` constructs the actual parameter isomorphism from
these natural Hom equivalences. `fullLevelParameterIso_hom_comp` proves
that postcomposition with its forward morphism on every test scheme is
exactly `fullLevelParameterIsoHomEquiv`.
`fullLevelParameterIso_hom_sections` records the resulting formula for
the classified ordered sections.
`fullLevelParameterIso_refl` and `fullLevelParameterIso_trans` identify
identity and composite parameter isomorphisms with those induced by the
identity and composite family isomorphisms.

The provenance is internal: this module combines the actual tuple and
full-level parameter classifications, actual isomorphism transport on
torsion, pullback of abelian schemes, and the categorical Yoneda lemma.
No numerical torsion rank, level existence, automorphism rigidity,
quotient construction, or ambient moduli existence is asserted.
