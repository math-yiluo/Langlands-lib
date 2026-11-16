# Semilocal inner forms from four geometric prerequisites

This internal composition constructs an actual isomorphism between any two
quasi-split étale inner forms of a reductive group over a semilocal ring, under
four explicit global statement proofs:

- `RelativeQuasiSplitInnerFormExistenceStatement`;
- `RelativeAdjointQuotientExistenceStatement`;
- `RelativeUnipotentRadicalFiltrationStatement`;
- `RelativeBorelAdjointTorusWeilPresentationStatement`.

The companion theorem
`reductiveSemilocalQuasiSplitInnerFormStatement_of_geometricPrerequisites`
has exactly `ReductiveSemilocalQuasiSplitInnerFormStatement.{u}` as its conclusion.
All four statements remain hypotheses. This module supplies no proofs of them
and does not prove the unconditional target.

The construction works in every universe `u`, for every commutative ring `R`
with finitely many maximal ideals. Its original group `F` is reductive. Its
specified map `qF : F ⟶ Fad` is an fppf quotient by the full centre, and its
specified action restricts to conjugation along `qF`. The two target groups
need only quasi-splitness and étale innerness relative to that action.

The model hypothesis supplies one quasi-split inner anchor `G`, a Borel `B`
in `G`, and an actual closed fibrewise maximal torus in `G` whose range lies
in `B`. The existing represented-subgroup factorization gives its actual
homomorphism into `B`, preserving the composite torus inclusion. Quotient
existence then supplies an affine full-centre quotient of `G`. The existing
inner-action constructor gives its compatible conjugation action.

`adjointBorelExtensionData` constructs the actual Borel stabilizer and torus
quotient, the sectioned Borel retraction with its original radical, and the
factorization of the full centre. The supplied Weil statement yields a chosen
finite étale algebra, finite and projective as an `R`-module, together with an
actual presentation of this torus quotient as `WeilGm`. The radical filtration
hypothesis supplies a finite vector-bundle series for the original Borel
radical. Closed subgroup inclusions into affine groups give the remaining
affineness and monicity hypotheses of the existing comparison construction.

`SectionedQuotientExtension.quasiSplitInnerFormsIsoOfSemilocal` now compares
the two target forms through this single anchor. Its published Picard-vanishing
input for finite algebras over semilocal rings discharges the coefficient
Picard condition. Classical choice from a nonempty isomorphism type handles
the existential model and quotient choices. The companion theorem obtains
existence directly from the model statement and uniqueness from this actual
isomorphism.

The provenance is internal: this module composes the named statement
interfaces with the represented-subgroup, inner-action, adjoint Borel
extension, Weil-presentation and sectioned inner-descent APIs. It claims no
new external structural theorem. Its purpose is to identify a sufficient set
of four geometric proof obligations for the unchanged target and discharge
all extra manually supplied geometry from the earlier conditional comparison.
