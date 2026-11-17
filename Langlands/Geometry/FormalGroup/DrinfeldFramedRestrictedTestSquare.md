# Actual original framing squares on a restricted base-change test

This internal unit retains the given original framing square on a test algebra
over a new Nilp quotient, viewed as a test over the old quotient and then
typed with its actual new scalar structure. It uses the existing all-test
framing condition and equality of scalar structures; it makes no new
literature assertion.

`QuasiIsogeny.CommutingSquare.reAlgebra` transports all four actual full-order
rational maps and their proved equation through equality of coefficient scalar
structures. Equality elimination retains the original square at reflexivity.
The four projection equations identify each resulting map with the existing
actual quasi-isogeny scalar transport.

`Comparison.originalSquareOnRestrictedTest` takes a specified actual original
framed comparison and a Nilp morphism. The new quotient test algebra restricts
along the actual induced quotient scalar map. On any specified original
reduced comparison chart whose generator is invertible on that restricted
test, the existing framing condition supplies exactly the original rational
square. The constructor packages its given refined framings, actual reduced
comparison chart map and residue-forced identity-frame map. The proved test
scalar equality transports this entire square to the new scalar structure on
the same test ring.

No framing condition for an extended comparison is assumed or asserted. This
is the transported original square to be pasted with the independently
constructed base-change framing and target comparison squares. Both actual
rational inverse maps of every edge are retained. No point-evaluation
criterion, extra original chart choice or frame automorphism is used.

The generic transport allows separate ring and rational-field universes,
arbitrary finite coordinate types and the existing domain/fraction-field
hypotheses. The specialized construction retains the local field,
finite-dimensional central division algebra, embedded field, coefficient and
residue fields, fixed height-certified frame and Nilp objects in universes
`{v,u}`. Covers may be infinite and coefficient maps may merge generators.
Preservation of the extended comparison square and class functoriality remain
further constructions.
