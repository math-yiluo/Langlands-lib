# Exact quotient images along prescribed incident cocharacter rays

This internal supporting result combines the prescribed-cocharacter lower
bound and the conditional prescribed-ray upper bound. Its remaining premise is
`UnramifiedRootPositiveReductionStatement`. All declarations have arbitrary
universe `u`.

Let C and E be actual maximal-unramified building and zero data for a
nonarchimedean local field F. Supply relative component model data D whose
neutral model is characterized by the zero fixer at an apartment point x,
and a reductive quotient Q of its actual special fibre. Use the chosen closed
split integral apartment torus in that neutral model. Every cocharacter of
its residue torus selects a positive ray parameter such that the facet at x
is a face of the facet at the ray point. For every actual smooth source
zero-fixer model with geometrically connected fibres characterized at that
ray point, and every supplied generic-identity comparison to D.neutral,
the actual schematic image after Q.projection equals the prescribed dynamic
parabolic on every residue-scheme test.

The lower bound is first obtained in the full special fibre from the published
incident-cocharacter containment theorem. To pass it through the quotient,
the implementation uses smoothness of the represented radical and the fppf
quotient to prove that Q.projection is smooth. Its surjectivity is part of the
actual fppf quotient predicate. The dynamic parabolic therefore has the
prescribed quotient parabolic as its actual fppf image.

A private general lemma contains that fppf image in the schematic image of
the composite comparison. The schematically dominant projection to the first
schematic image allows its inclusion followed by the quotient to factor into
the schematic image of the composite. This gives ordinary-image containment.
The target is a represented subgroup and hence fppf local, so actual local
lifts give containment of the entire fppf image. This argument does not require
the original comparison to be pointwise surjective.

The upper bound uses the chosen integral apartment torus in the source model
and the conditional prescribed-ray theorem. The two containments prove the
equality. `HasPrescribedIncidentQuotientImageEquality` packages the conclusion,
and `hasPrescribedIncidentQuotientImageEquality` proves it.

The result retains the positive-reduction premise and supplies neither source
model nor comparison existence. It does not assert that every parabolic is
obtained from a cocharacter of the fixed torus, or prove the host descended
facet–parabolic order bijection. The provenance is the imported Library
interfaces and the supporting bounds; no new original-literature assertion
is made.
