# Filtered colimits of actual Picard isomorphisms over subalgebras

This internal module constructs the directed category of finitely generated
`R`-subalgebras of an arbitrary commutative `R`-algebra `A`. Inclusions give
the actual contravariant maps between their spectra over `Spec R`.
For a presheaf on the full slice over `Spec R`, these maps give a diagram
of its section types and the canonical cocone of restrictions to `Spec A`.

For a presheaf represented by a scheme affine and locally of finite
presentation over `Spec R`, `affineAlgebraStageSectionsIsColimit_of_representable`
constructs a colimit structure on this cocone. The implemented
argument uses the published specified-section descent theorem for joint
surjectivity. Each individual restriction from a subalgebra is injective:
the representing scheme is affine, so its maps can be read as ring maps,
and the inclusion of a subalgebra is injective. Naturality transports
this cancellation to presheaf sections. Mathlib's filtered-colimit
criterion then proves the cocone's universal property.

The Picard specialization applies the published line-bundle Hom theorem
and the published Hom-to-Isom implication. For any proper, flat, locally
finitely presented morphism `f : X → S`, affine base `t : Spec R → S`,
and two actual families `L, M` over that base, the canonical restriction
cocone for `relativeIsomPresheaf f L M` is a colimit. Its sections retain
the specified actual isomorphisms, with the ordinary pullback comparison
maps and the explicit universe lift already built into that presheaf.
The scheme, base-ring and test-algebra universe remains arbitrary `u`;
the lifted section types lie in `Type (u + 1)`. The Prop-valued definition
`PicardGroupoid.HasAffineIsomSectionsColimit` asserts that this precise cocone
admits an `IsColimit` structure. The theorem
`PicardGroupoid.hasAffineIsomSectionsColimit` proves it under these three
geometric hypotheses, and `PicardGroupoid.affineIsomSectionsIsColimit`
provides the structure itself.

The derivation uses existing Lean results and categorical cancellation;
it introduces no additional literature assertion. This proves a colimit
of isomorphism sections for two families defined on one fixed base.
It does not construct a colimit category of all families, compare every
filtered ring diagram, establish openness of versality or construct a
smooth atlas.
