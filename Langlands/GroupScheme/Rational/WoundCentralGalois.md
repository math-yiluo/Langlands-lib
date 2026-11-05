# Central additive lines over algebraic Galois extensions of wound groups

This internal result combines the published finite coefficient-model and
central Galois norm constructions. It is a prerequisite for separable
invariance of woundness. It does not state the whole invariance theorem.

`WoundCentralGaloisStatement` packages the obstruction at arbitrary
universe `u`; `woundCentralGalois` proves it. The directly usable helper is
`HasConstantAffineLineMaps.not_isCentral_of_mono_galois`.

For a group with only constant ground-field affine-line morphisms, every
actual central homomorphism from the standard additive line over a finite
Galois extension has zero input tangent in every ground-field coordinate
direction. If an input tangent were nonzero, the scalar-weighted central
norm would give an actual ground-field additive-line homomorphism with a
nonzero tangent. Affine-line constancy forces that homomorphism to be zero,
which makes its tangent zero and gives a contradiction.

Consequently an arbitrary algebraic Galois extension cannot create a
central monomorphic standard additive line when the original group is
affine and locally of finite type. Choose the coordinate direction one;
monicity makes its tangent nonzero. The finite Galois coefficient model
preserves both full centrality and that nonzero tangent, so the preceding
finite-extension argument contradicts its existence. Monicity of the
finite model is not needed.

All centrality assertions quantify over all relative scheme tests, and
all scalar extensions are the actual group-scheme pullbacks. There is no
smoothness, connectedness, unipotence, perfectness, field-infinitude or
characteristic hypothesis. Only the finite norm argument requires finite
degree; the final obstruction permits infinite algebraic Galois extensions.
