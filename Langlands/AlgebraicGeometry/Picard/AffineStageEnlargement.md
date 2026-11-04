# Finite subalgebra stages above a chosen stage

This internal construction compares the actual subalgebra indices used in
`AffineIsomColimit`. For a commutative `R`-algebra `A` and a finitely generated
`R`-subalgebra `B`, `affineAlgebraStageEnlargementOrderIso` identifies the
finitely generated `B`-subalgebras of `A` with the finitely generated
`R`-subalgebras of `A` containing `B`. The universes are arbitrary.

The forward map restricts scalars. Finite generation and containment of `B`
come from the published theorem
`Subalgebra.fg_restrictScalars_and_le_of_fg`, imported from the existing
Anthropic FLT port. The inverse `subalgebraOver` uses exactly the same carrier
and ring operations, with the inclusion of `B` supplying its scalar map.
Any finite generating set over `R` still generates this algebra over `B`:
the forward containment follows from closure under the generators, and the
reverse containment follows by restricting scalars in the generated algebra.
Both inverse laws and preservation and reflection of order are carrier
identities.

`affineBaseTowerIso` identifies the affine test obtained by composing
`Spec A → Spec B → Spec R` with the direct test `Spec A → Spec R`.
Its underlying scheme map is the identity; the slice equation is the
contravariant composition law for `Spec`.

The result supplies an index comparison. It does not yet construct a
category of all finite-stage Picard families, a filtered-colimit equivalence
of those categories, or a smooth chart.
