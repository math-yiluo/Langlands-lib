# Faithful flatness of dominant group homomorphisms

The proof reuses the published arbitrary-field flatness theorem
`DominantHomFlat.flat_of_isDominant` from `DominantHomFlat`. Dominance ensures
that every nonempty target open
contains the image of a rational source point: pull the open back, then use
the density of closed points in the locally finite type source over the
algebraically closed field.

For a nonempty target open, its translates by rational image points cover
the target. Otherwise their closed common complement would have a closed
point. Translate the original open on the right by that rational point,
then use dominance to obtain a rational image point in this translated open.
The left translation by that image point moves the chosen closed point into
the original open, a contradiction.

The imported flatness theorem uses generic flatness and translations by
families of points, and applies because the underlying homomorphism is of
finite type and its reduced target is locally noetherian. The resulting
finite-type flat map has open image. Apply the coverage argument
again to this image; invert the corresponding source and target translations
to give a preimage of every scheme point. Quasi-compactness follows from that
of the source over the field.

This is an internal derived proof. It uses reducedness of the target,
finite type of the source, and an algebraically closed field exactly as in
the published proposition target.

The grouped corollary `DominantHomFlat.isIso_of_schematicallyDominant` works
over an arbitrary field. Its source is of finite type, its target is locally
of finite type and geometrically reduced, and the homomorphism is both a
monomorphism over the base and scheme-theoretically dominant. After extension
to an algebraic closure, the actual base-change square preserves schematic
dominance and monomorphy. The theorem above supplies flatness and scheme
surjectivity, so Mathlib's flat quasi-compact surjective monomorphism theorem
makes the base-changed scheme map an isomorphism. Isomorphy descends through
the faithfully flat field extension. Forgetful functors then recover an
isomorphism of the actual group schemes. This corollary does not assume
affineness of either group.
