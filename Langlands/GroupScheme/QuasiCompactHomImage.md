# Affine images with possibly nonaffine source

This derived construction removes the affine-source restriction from the
published `HomImage` construction while keeping the quasi-compactness needed
by its schematic-image and dominant-homomorphism inputs. It does not assert
quasi-compactness of every smooth connected group.

`QuasiCompactHomImage.Factorization φ` stores an actual image group `D`, closed
subgroup inclusion `D ⟶ G`, and projection `A ⟶ D`, whose composite is `φ`.
Its proof fields say that the projection is flat, surjective, quasi-compact,
and locally of finite presentation, and that `D` is smooth, connected and affine.

`ofGeometricallyIntegral φ` constructs this data over an arbitrary field,
assuming a locally finite-type geometrically integral source, an affine
locally finite-type target, and quasi-compactness of the underlying map `φ`.
The source need not be affine. `ofSmoothConnected φ` instead assumes that the
source is smooth and connected, keeping the same assumptions on the target
and on `φ`.

The implementation uses the actual image, inclusion, and projection from
`SchematicImage`. Geometric reducedness and irreducibility descend along its
schematically dominant quasi-compact projection, by the published
`ImageGeneration` lemmas. The image is locally of finite type since it is closed
in the target; its geometrically reduced group structure gives smoothness.
`DominantHomFlat` gives flatness of the projection and then surjectivity because
the image is irreducible. Local noetherianness of the target gives local finite
presentation from local finite type. For `ofSmoothConnected`, quasi-compactness
of `φ` and affineness of the target first give quasi-compactness of the source
structure map. Published `geometricallyConnected_of_connected` and
`smoothGeometricIntegrality` then supply geometric integrality.

This is internal infrastructure derived entirely from published Library
constructions and their proved properties. The proof follows `HomImage` with
its unnecessary affine-source premise replaced by the precise quasi-compact
hypothesis. It supplies an image step for nonaffine competitors in the smooth
radical extension problem, not a proof of that extension statement.
