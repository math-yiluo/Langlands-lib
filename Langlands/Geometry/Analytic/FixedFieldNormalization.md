# Normalizing an analytic arrow over an isomorphic ground field

The inclusion of the analytic fibre over \(K\) sends a map to the
varying-field arrow with identity coefficient map. Its analytic component
composes with the inverse unit comparison for scalar extension. Cancelling
that comparison proves faithfulness. `toFixedFieldMap` recovers the map in
the fibre by composing with the unit, and `toFixedFieldIso` recovers an
isomorphism in the fibre when the given arrow is invertible. The underlying
continuous map of an included arrow is its original analytic point map.

For an isometric field isomorphism \(K\to L\), `scalarExtensionIso` is the
Cartesian projection from the scalar-extended space, which is invertible
over an invertible base arrow. Its image under the underlying-space functor
is therefore a homeomorphism. For \(f\colon Y\to X\) with invertible
coefficient map \(K\to L\), extend \(Y\) along \(L\to K\). Composing the
resulting projection with \(f\) has identity coefficient map, which gives
a representative of the arrow in the analytic fibre over \(K\).

This construction uses the field-changing arrows and analytic scalar
extension of Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), §1.4, printed p. 30 (PDF p. 27), and the description of those arrows
as a fibred category in *Étale equivariant sheaves on p-adic analytic spaces*,
§1.1, printed and PDF p. 1.
