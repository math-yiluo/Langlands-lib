# Compact compatible Čech systems and actual derived sections

This internal module connects `compactCompatibleCechSystem` to the actual
ordinary quasi-étale cohomology and to the published compact comparison
statement. Two mathematical inputs remain explicit: finite representable
presentations in every degree of every selected compatible cover's actual
presheaf nerve, and positive Hom exactness for restricted injective
equivariant coefficients.

The field, analytic category, and coefficient universes are exactly those
of the comparison target: the ring and modules lie in
`Type (max u (v + 1) uL)`, with arbitrary `uL`. The ordinary site's local
smallness, module sheafification, and enough injectives come from the
established analytic instances. In particular no equality between the
analytic site's morphism universe and the coefficient universe is imposed.
The module takes local smallness, module sheafification, enough injectives,
and `WEqualsLocallyBijective` as instance parameters; the first three have
the established analytic constructions. The local-bijectivity instance
is the explicit hypothesis already used by compatible-cover coefficient
lifting and is retained here.

`compactLiftSectionsIso` uses the free-sheaf adjunction and the
shrunken Yoneda equivalence to identify linear Hom from the free
representable of a compact basis object with its sections functor.
Coefficient morphisms preserve this equivalence, giving the natural
isomorphism. `compactLiftSectionsDerivedIso` applies right derivation
to its two directions; preservation of identity and composition proves
that they remain inverse in every degree.

Given the finite nerve presentations, the compatible-cover system is an
exact augmented finite test system with local coefficient lifting.
Its dimension-shifting theorem sends the positive Hom exactness input
to vanishing of higher derived linear Hom at every basis object.
The derived natural isomorphism transfers this vanishing to actual
`sectionsDerived`. `compactCompatibleSectionsZeroIso` records the
resulting isomorphism of the higher cohomology module with zero.

For a compact space with continuous action, its identity is in
`CompactLiftBasis`. Applying the vanishing theorem to this object
and to a restricted injective equivariant sheaf proves
`QuasiEtaleRestrictedInjectivesAcyclicStatement` under the specified
Hom exactness hypothesis. The last theorem applies the previously
proved reduction from restricted-injective acyclicity to the actual
comparison map being an isomorphism in every degree.

This is a derived adapter, not an unconditional proof of the comparison.
It parallels the generic `FiniteCechSections` construction, while
working directly in the full analytic universe range required here.
Neither the finite presentations nor restricted-injective Hom
exactness is inferred from injectivity in the ordinary sheaf category.
The provenance is internal, using only the existing free-representable,
finite test-system, and comparison-reduction constructions.
