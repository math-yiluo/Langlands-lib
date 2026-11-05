# The reductive coefficient spectral boundedness criterion over local fields

`reductiveSpectralBoundedness` proves the exact Library proposition
`ReductiveSpectralBoundednessStatement` from
`Langlands.GroupScheme.Rational.SpectralCompactnessPrerequisites`, at arbitrary
universe `u`. Let `F` be an actual nonarchimedean local field, `G` a connected
reductive `F`-group, `N` any natural number (zero included) and
`ρ : MatrixRepresentation G (Fin N)` an actual matrix representation. Suppose
`ρ` is a closed immersion and every rational-point matrix has a characteristic
polynomial with integral coefficients. Then `IsAlgebraicallyBounded F G.X Set.univ`
holds for the all-regular-functions predicate. The theorem keeps the target's
quantifiers and its reductivity-derived affine instances unchanged. It adds no
anisotropy, compactness, density, irreducibility, splitting, entry-boundedness
or trace-probe premise, and it covers mixed and equal characteristic.

## The implemented proof

1. The proof first installs the target's instances `IsAffineHom G.X.hom` and
   `IsAffine G.X.left` from `hG`. It also takes smoothness and connectedness of
   `G` from `hG`.
2. The published canonical monoid map
   `baseChangeSectionHom (toAlgebraicClosure F) G` sends rational points to
   points over the actual algebraic closure. By `baseChangeSectionHom_left`, its
   underlying pullback lift is definitionally `geometricRationalPoint`.
3. `hasDenseRationalPoints_of_localField` (in `LocalFieldDensity`) shows that
   rational points are Zariski dense in a smooth connected affine group over a
   local field. It uses the published local-field theorem that the `F`-points
   of a smooth `F`-domain with an `F`-point separate elements. It applies this
   to the coordinate algebra, a domain, with the identity as base point, and
   then transports along the coordinate isomorphism. This lemma uses neither
   reductivity nor any characteristic assumption.
4. The published scalar-extension theorem
   `hasDenseGeometricRationalPoints_of_hasDenseRationalPoints` turns this density
   into density of the images of the geometric points over `AlgebraicClosure F`.
   Rewriting with step 2 gives exactly the density that the dense-family
   criterion needs.
5. `isAlgebraicallyBounded_of_dense_geometricPointHom` (in
   `DenseSpectralBoundedness`) finishes the proof. Its earlier stages:
   - **Composition factors.** It extracts actual simple composition factors of
     `ρ`.
   - **Finite morphism.** Their direct sum gives a finite morphism of the
     original group image, using the unipotent-kernel and finite-kernel
     arguments.
   - **Spans and bounds.** Dense-family Burnside gives full matrix spans on
     the dense geometric family. Characteristic-polynomial integrality passes
     to each subquotient and gives trace and entry bounds.
   - **Descent.** A compatible cofinal valuation on the algebraic closure
     brings the regular-function bounds back to `F`.

The density premise of the earlier conditional reduction
`reductiveSpectralBoundednessReduction` is therefore discharged internally by
the local-field density lemma. This proof does not import that reduction.

## Provenance and authorship

This proof follows Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Lemma 2.2.11 (printed pp. 72–73, PDF pp. 103–104). That proof uses rational
density, the finite morphism to the direct sum of irreducible subquotients, and
trace bounds. Here rational density comes from local-field point separation on
the smooth coordinate domain, not from a general unirationality theorem.

Worker 1554 wrote the local-field density lemma, the scalar-extension and
valued-descent prerequisites, and identified the canonical section monoid map.
Worker 1563 wrote the dense-family and Burnside span prerequisites. Worker 1296
wrote the simple-factor, finite-map and trace assembly, the dense-family
criterion and this closing proof. The source pairs of still-unpublished
prerequisites accompany this candidate unchanged.
