# Normalized real parameters on actual split tori

This construction uses the actual commutative group scheme, its character and
cocharacter lattices, and the perfect real pairing of `RealTorusSpace`.
Its valuation is a transparent abbreviation of `centralizerValuation` at the
identity, using the proved split-torus comparison.

The implementation evaluates a complex character on the intrinsic
`CocharacterUniformizer.latticeSection`, takes the normalized modulus
`-log ‖χ‖ / log q`, extends that additive functional from the cocharacter lattice
to its real tensor product, and applies `characterDualEquiv.symm`. This definition
exists for every character; the eventual all-point formula requires its open
kernel and the split-torus compact-unit argument.

The source is Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, source ID
`renard-2026-representations-groupes-reductifs-padiques`, V.2.3 and V.2.5
(printed pp.105–107/PDF pp.111–113), and V.3.19–V.3.20
(printed pp.115–116/PDF pp.121–122). The fixed positive valuation and the
exponential convention `q^(-s)` give the normalized parameter used here.
The raw natural logarithm in the later printed formula differs by `-log q`.
Accordingly `rawLogRealPart` is separately named and defined to be that scalar
multiple of `normalizedRealPart`. Their equality is definitional, and the
section-point log-modulus theorem checks the precise factor algebraically.
The two parameters are never identified.

The auxiliary scalar extension and section functional are internal derived
constructions. The implemented proofs evaluate the perfect-pairing equivalence
on pure tensors. Multiplicativity of the complex norm and additivity of
`normLog` give the product law; the trivial and inverse laws follow from the
same computation. No smoothness, unramifiedness or positive-rank assumption is
needed for these algebraic laws.
