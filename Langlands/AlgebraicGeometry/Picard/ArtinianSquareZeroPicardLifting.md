# Actual pointed Picard lifting along square-zero Artinian arrows

This internal construction uses the actual pointed Artinian deformation groupoids
and their published pullback comparison. For an arbitrary augmented Artinian arrow
`q : A ⟶ B`, an actual deformation `L` at `B`, and an ordinary bundle `N` at `A`
whose pullback is isomorphic to the underlying bundle of `L`, `repointedLift`
chooses the residue identification on `N` dictated by this isomorphism and the
specified residue identification on `L`.

`repointedLiftIso` retains the supplied underlying bundle isomorphism and proves
its compatibility with the specified residue identifications by cancellation of
the actual reduction comparison. Consequently `pointed_lift_iff` equates existence
of a lift up to actual pointed isomorphism with existence of an ordinary lift up
to actual module-sheaf isomorphism. This part requires neither surjectivity nor a
splitting of `q`. It does not assert that forgetting the residue identification
is injective on isomorphism classes.

The lemma `repointedLiftIso_underlying` identifies the underlying isomorphism
with exactly the supplied one.

For any surjective test arrow, `relativeMap_isClosedImmersion` proves that its
actual relative scheme map is a closed immersion, using its cartesian square
with the map of test spectra. Write this relative map as `i : X_B ⟶ X_A` and
the source algebra map as `q`. For an affine open `U` of `X_A`,
`testSectionHom` is the actual map from `A` to `Γ(X_A, U)`, using the projection
to `Spec A` and the canonical global sections isomorphism. Then
`relativeMap_affine_ker` proves

```text
ker(i.app U) = (ker q).map (testSectionHom f A U).
```

The proof takes sections of the actual cartesian square on the affine open
and the entire test spectra. The canonical section pushout is an isomorphism
by Mathlib's affine cartesian section theorem. The imported
`P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le.CommRingCat.ker_eq_map_ker_of_isPushout`
computes the section kernel. The canonical spectrum global sections
isomorphisms then identify the test-spectrum kernel with the original
ring-map kernel. This is the same section-pushout method used by the published
`Modules.AdicStalkQuotient`, applied to a general surjective test map rather
than a specified ideal quotient.

`relativeMap_ker_pow_eq_bot` uses the affine kernel formula and preservation
of ideal powers and zero under ideal image to extend any vanishing kernel
power to the relative scheme's kernel ideal sheaf. Its quasi-compactness
assumption on `i` is available from the proved closed immersion. In particular
`relativeMap_ker_sq` applies the published elementary-surjection convention:
the source maximal ideal annihilates the kernel. This convention allows
zero kernels and kernels of any dimension. Since the kernel lies in the
maximal ideal, it is square zero, and so is the actual relative kernel.
Neither this argument nor the affine formula needs flatness.

For the obstruction statements, assume only `QuasiCompact f`.
`testSpace_compactSpace` obtains compact underlying spaces for the actual
relative schemes over affine test spectra by base change. In particular
this assumption holds under the properness hypothesis of the atlas task.
For an elementary surjection, `obstruction` applies the published
`SquareZeroPicardObstruction.obstructionMap` to the actual class of the
underlying bundle of `L`. Its target is actual ideal-module H² on `X_A`,
namely derived sections of `StructureKernelModule.kernelModule i`.

`pointed_lift_iff_obstruction` combines `pointed_lift_iff` with the published
`SquareZeroPicardObstruction.lineBundle_lift_iff`. It says exactly that
there exists an actual pointed deformation at `A` whose actual restriction
is pointed-isomorphic to `L` if and only if the defined obstruction is zero.
`exists_lift_of_h2_zero` supplies such a lift when every class in that actual
H² group is zero. The result retains existence of actual compatible bundle
isomorphisms and makes no uniqueness claim.

All rings and schemes share an arbitrary universe `u`. This is an internal
derivation from the named published interfaces, with no new external source
input. Tests are the general augmented local Artinian algebras, with no
coefficient field or augmentation section imposed. No vanishing theorem
for H², coherence or finiteness of these obstruction modules, formal hull,
formal versality, algebraization, or smooth atlas is proved here.
