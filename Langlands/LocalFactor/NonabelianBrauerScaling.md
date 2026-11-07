# Additive-character scaling before nonabelian descent

This derived support unit evaluates the determinant of the actual virtual class
of a finite Brauer presentation and proves Deligne's additive-character scaling
identity for its actual abelian epsilon evaluation. It works for every prime,
every actual p-adic field in universe `uF`, every independent representation
universe `uV`, and every supplied normalized common-closure reciprocity family.
It assumes no nonabelian local-constant assignment.

`determinantEvaluation` applies the existing determinant character on the
continuous exact Grothendieck group to `virtualPresentation` and a supplied Weil
element. It is integer linear with values in `Additive ℂˣ`: addition denotes
multiplication of nonzero complex values. The single-generator formula records
the determinant of that actual induced character difference to its integer power.

The proof first lifts the published fixed-Haar additive-character scaling law
to `abelianEpsilonUnit`. In `abelianEpsilonRatio_scale`, the identical normalized
absolute-value correction cancels between numerator and denominator, leaving the
ratio of the two field-character values at the scalar.

For a nested generator, `generatorValue_scale` uses the actual trace identity
to pass the base scalar through the actual field inclusion.
`determinant_generatorClass` applies the proved Gallagher determinant formula,
its degree-zero exact-induction consequence, and the transfer/inclusion square
of the supplied normalized reciprocity family. The determinant on the difference
of two character lines is exactly their value ratio. A Weil lift exists for
every field unit because the supplied reciprocity components are equivalences.

`evaluationMap_scale` combines these facts on single generators and extends
them by integer linearity to all finitely supported presentations. If
`presentationMap z = 0`, the determinant of its actual virtual class is one;
`evaluationMap_scale_of_presentationMap_eq_zero` therefore proves that the epsilon
product of this relation is unchanged when the additive character is scaled.
This is an invariance theorem. It does not prove that the product of a relation
is one, that evaluation descends to the exact quotient, or that a nonabelian
system exists.

The source motivation is Deligne, *Les constantes des equations fonctionnelles
des fonctions L* (1973), section 4.2 and Lemma 4.3, printed page 536 / retained
PDF page 36. The implemented proof follows that lemma's character-ratio,
trace, transfer and determinant argument, using published actual-object
constructions and the separately constructed Brauer presentation. No quotient
by characters, trace replacement, semisimplicity assumption or chosen
nonabelian system enters this result.
