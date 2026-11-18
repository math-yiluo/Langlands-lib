# Bijectivity of the actual common-Levi unitary comparison

`comparisonEquivOfInjective` packages an injective intertwiner of the actual
common-Levi coefficient fibers as an equivalence. It takes one point of the
genuine generic locus and admissibility of the inducing twist at the
parameter of the given intertwiner. The underlying map of the equivalence is
the given intertwiner.

Admissibility of each actual coefficient fiber follows from admissibility of
normalized induction with compact quotient, admissibility of the smooth
contragredient, and admissibility of the external product. The compact
quotients use the given Iwasawa factorizations.

Transport to the fixed compact carriers turns the generic comparison into an
equivalence of representations. At any parameter, intersect the open
stabilizer of a target vector with the supplied compact product group. The
two compact actions on this intersection agree with the actions at the
generic point on their respective carriers. The generic equivalence therefore
identifies the dimensions of the two fixed spaces. Both spaces are finite
dimensional by admissibility. The given injective intertwiner restricts to a
surjection of the fixed spaces, giving a preimage of the original vector.

`comparison_bijective_of_preservesFormalDegreeForm` applies this argument to
an actual unitary comparison family. Square integrability gives
admissibility of the twist, and preservation of the specified positive
inverse-formal-degree form gives injectivity.

This is a derived step for the unitary comparison in Waldspurger's Lemma
V.3.1, printed p. 295 / PDF p. 61 (`waldspurger-2003-plancherel`). The
argument uses the generic comparison from formula (1) and finite-dimensional
fixed spaces to obtain surjectivity of the form-preserving extension.
