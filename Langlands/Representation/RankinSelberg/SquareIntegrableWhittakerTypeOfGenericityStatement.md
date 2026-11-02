# Full Whittaker type conditional on square-integrable genericity

Author: Worker 192.

`Langlands.RankinSelberg.SquareIntegrableWhittakerTypeOfGenericityStatement`
is a closed, `Prop`-valued definition of an internal adapter statement.
It assumes
`Classification.SquareIntegrableGenericity.{uF,uV} F F.canonicalTopologicalData`
for the specified p-adic field. It does not prove that assumption.

For every prime `p`, field `F : PadicField.{uF} p`, continuous nontrivial
unitary additive character `ψ` for the canonical field topology, and positive
rank `n + 1`, the statement concerns an actual complex representation `π` on
any algebraic carrier `V : Type uV`. The field and carrier universes are
independent. It assumes irreducibility and the existing analytic
`F.canonicalTopologicalData.IsSquareIntegrable π` predicate. Its conclusion
is the full existing
`RankinSelberg.IsOfWhittakerType n (Whittaker.standardCharacter ψ n) π`
on the same carrier and action, with the positive standard character.

That conclusion comprises admissibility, finite generation over the complex
group algebra, and a complex-linear equivalence between the entire
character-equivariant functional space and `ℂ`. There is no finite-dimensional
carrier hypothesis or topology on the representation carrier. Rank one is
included. The square-integrability predicate retains its smooth-dual
coefficients and universal Borel Haar quantifier on the central quotient.

The provenance is internal assembly of published Library interfaces. The
intended proof obtains admissibility from square-integrability and
unitarizability from `Langlands.glSquareIntegrableUnitarity`. It bundles the
original action as a smooth representation, uses `SmoothRep.universeLift`
to reach the carrier universe `max uF uV` required by the assumed genericity
statement, and transports irreducibility, square-integrability and
unitarizability along the actual representation equivalence. After applying
the explicit genericity input, `Whittaker.isGeneric_iff_of_equiv` returns
genericity to the original carrier. The published
`RankinSelberg.isOfWhittakerType_of_isGeneric` then supplies the full
Whittaker-type conclusion using multiplicity one and the existing algebraic
functional-space construction.

This module states that implication only. It proves neither the implication
nor square-integrable genericity, and supplies no closed pole-freeness
theorem. Its conditional input remains necessary until genericity is proved
separately. No original literature assertion is introduced here.
