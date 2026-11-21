# Isogeny factorizations of complete ample linear systems

`CompleteLinearSystemIsogenyStatement` applies to the complete generating
system of an ample line bundle on an abelian variety over an algebraically
closed field. If its projective map factors through a finite flat surjection
to another abelian variety over the field, the surjection is an isomorphism.
`isIso_of_completeLinearSystem_factors` proves the statement.

The factored map is proper because the source is proper over the field and
projective space is separated. Its fibres are finite because the composite is
finite and the first map is surjective. Pull back the ample projective twist
along this finite map. The further pullback of the resulting ample bundle
identifies with the original bundle through `linearSystemTwistIso`. That
identification sends the further pullbacks of the projective coordinates to
the original basis of sections. It gives surjectivity of section pullback, and
faithful flatness gives injectivity. The published isogeny dimension formula
then makes the finite flat surjection an isomorphism.

This auxiliary lemma adapts Mumford's quotient dimension comparison to a
supplied factorization of the complete linear-system map. It applies to finite
flat surjections in every characteristic. Mumford, *Abelian Varieties*, §17,
printed pp. 164–165 (PDF p. 87 of `mumford-abelian-varieties-full-scan`).
