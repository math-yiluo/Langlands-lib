# Determinant polarization and the parabolic scheme reduction

This internal reduction works in every universe `u` and retains the actual
coherent dual of the parabolic Lie determinant on the original parabolic
presheaf. It assumes the following three separate geometric propositions:

- `RelativeParabolicEtaleLocalFiniteTypesStatement.{u}`;
- `FiniteAffineParabolicDeterminantDualAmpleStatement.{u}`;
- `PolarizedSmoothProperEtaleDescentStatement.{u, u + 1}`.

The finite-type premise supplies an affine étale neighbourhood of every base
point and a finite family of actual relative parabolics with uniform field
types. Lifting its finite index type to universe `u` preserves the uniqueness
condition and gives the existing finite quotient representing model. The
positivity premise makes its precise coherent universal determinant dual
ample. The universal base-change comparison transports this to the restriction
of the original group's coherent determinant dual on the same model.

On a compact base, compactness extracts finitely many of these neighbourhoods.
Their finite coproduct is affine, and their étale maps give a single étale
surjection. The existing coproduct construction assembles their smooth proper
models. The coproduct universal ampleness theorem proves that the restriction
of the same original coherent determinant dual is ample on this assembled
model. This supplies the line bundle and ampleness fields of
`AffineEtaleCoverModel.Polarization`.

`polarizedAffineEtaleCoverModel` chooses a covering model from the proved
existence statement and returns it together with its polarization as a dependent
pair. Its line-bundle field is explicitly the original coherent determinant
dual, and the chosen existence witness supplies its ampleness. This is a
construction under the finite-type and positivity premises on a compact base;
it does not require the descent premise.

Finally, the existing affine polarized-descent reduction descends these models
on each affine open of an arbitrary base and glues them in the Zariski topology.
The resulting conditional theorem has exactly the unchanged conclusion
`RelativeParabolicSchemeStatement.{u}`. No noetherian, splitting or
constant-rank hypothesis is added. Compactness is required only for the
intermediate cover construction and holds on the affine opens used by the
final reduction.

The construction derives from the existing local quotient models, coherent
universal comparisons, finite coproduct ampleness and polarized-descent
interface. Each of the three geometric propositions remains an explicit
premise. This module proves their implication to the host target and supplies
neither an unconditional proof of those premises nor an unconditional proof of
the target.
