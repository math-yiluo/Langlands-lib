# Arithmetic consequences of the dimension-one norm criterion

This module introduces the internal field property
`Langlands.FieldTheory.HasTrivialFiniteRelativeH2 K`. It asserts that for
every finite Galois extension `L/K` in the same universe, the actual relative
second cohomology `Langlands.ClassFieldTheory.Local.relativeCohomology K L 2`
is a subsingleton. The coefficient representation is the actual action of
`Gal(L/K)` on `Additive Lˣ`, as defined in the published local cohomology
module. This property does not assert vanishing for group schemes or the
existence of a Borel subgroup.

The elementary theorem
`HasDimensionLEOne.finite_separable_extension` proves that the existing
norm criterion survives finite separable extension. For a finite separable
tower `K → E → F`, the proof equips `F` with the composite `K`-algebra
structure. Transitivity of finite dimensionality and separability makes
`F` an allowed test field in `HasDimensionLEOne K`. Applying that property
to `F` and the given finite Galois extension `L/F` gives exactly the
required determinant norm surjectivity. No transitivity of norms is needed.

The theorem `HasDimensionLEOne.trivial_finite_relative_h2` applies the
published theorem
`Langlands.ClassFieldTheory.Local.finiteNormH2Vanishing`. For each
intermediate field `E` of finite Galois `L/K`, finiteness and separability
of `E/K` and Galoisness of `L/E` permit direct application of
`HasDimensionLEOne K` to the determinant norm `Lˣ → Eˣ`. This supplies the
whole norm family required by that theorem. The cohomology definition and
its finite-norm vanishing proof are reused without modification.

The predicate and bridges are derived internal interfaces for the
norm-to-cohomology portion of Steinberg's theorem. Their provenance is the
existing [dimension-one norm definition](DimensionLEOne.md) and the
published [finite-norm second-cohomology proof](../ClassFieldTheory/Local/FiniteNormH2Proof.md).
The latter documents its source in Serre, *Local Fields*, Chapter X,
Section 7, Proposition 11. This module makes no additional literature
claim. All fields and quantified extensions lie in arbitrary `Type u`;
there is no perfectness or characteristic assumption.

Worker 1333 authored this interface and its elementary proofs. The
finite-Galois cohomology vanishing theorem is the published work of
Worker 68, with the p-group case credited there to Workers 28 and 68.
