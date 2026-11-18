# Polynomial growth of the original orbit constant terms

This internal adapter supplies the shifted-chamber growth input for the
positive constant-term decay assembly. It uses the actual original inducing
representation, central quotient measure, full unitary orbit, smooth section,
constant term, and ambient and target-Levi Xi functions. The field and
representation-carrier universes remain independent.

`HasRationalOrbitConstantTermPolynomialBounds` means that every original
smooth orbit section has `HasRationalConstantTermPolynomialBound` for its
actual full constant term at the supplied matrix height. The threshold,
constant and natural degree may depend on the section. Within that estimate
they are chosen before every orbit parameter and every point of the full
minimal-Levi shifted closed chamber.

The implemented theorem composes three proved interfaces. The preceding
full-minimal-Levi Xi comparison supplies an ambient-Xi upper estimate by
the target-Levi Xi, the exact constant-term half modulus and a height
polynomial. Worker 658's unchanged original-orbit coefficient theorem gives
one global coefficient constant from the original simultaneous basis,
source-Levi Cartan cover and central square integrability. The exact
`RationalOrbitConstantTermThresholdStatement` identifies the original
coefficient with the half modulus times its actual constant term on a single
shifted closed chamber. The generic polynomial-bound adapter cancels this
nonzero half modulus and multiplies the two bound constants.

This theorem retains the separately owned `RationalXiUpperBoundStatement`
and the exact full-chamber threshold statement as explicit intermediate
inputs. It also retains the Borel-space compatibility of the displayed
central quotient needed by the reused original coefficient theorem.
Neither a fixed-ray asymptotic formula nor the current supporting reductions
discharges the full-chamber threshold or removes this measure compatibility.
Consequently this unit does not prove the published unconditional positive
constant-term decay target.

Provenance is internal composition of the displayed Library and supporting
interfaces. Its source context is Waldspurger (2003), Lemma VI.2.3 and proof,
printed pp.299–301, where the uniform threshold and the Xi estimates give
polynomial control of the full constant term before the positive-part
exponential estimate. Registered source: `waldspurger-2003-plancherel`,
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
