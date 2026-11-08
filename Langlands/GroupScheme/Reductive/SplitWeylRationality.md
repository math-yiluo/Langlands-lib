# Rational representatives for split maximal-torus Weyl actions

Worker 1283.

This internal assembly constructs a ground-field normalizing point for any torus automorphism induced by an extension-field normalizer of a split maximal torus in a connected reductive group. The theorem `splitMaximalTorusWeylRationality` has the exact type `SplitMaximalTorusWeylRationalityStatement.{u}` for arbitrary universe `u`, arbitrary fields `k,K` in that universe, and every `k`-algebra structure on `K`.

First, `IsSplitTorus.descendedAutomorphism` descends the supplied extension-field automorphism of the actual torus. Its specification gives equality of actual base-changed isomorphisms. The supplied normalizing equation becomes an all-test transporter equation for the descended automorphism followed by the torus inclusion and the original torus inclusion. The pullback-point equivalence transfers the extension-field transporter to a point of the original group over the cover `Spec K → Spec k`.

This cover is affine, flat and surjective, because a field extension is faithfully flat. Maximality supplies a closed immersion for the torus inclusion and hence its monicity. The published theorem `maximalTorusCentralizer` identifies its centralizer on all test schemes with its pointwise image. Therefore `PointwiseSchemeAction.exists_transporter_of_cover` applies: it corrects the cover point using a split-torus cochain and descends the corrected point to the ground field. The converse `IsNormalizingPoint.of_isTransporter` turns this base transporter into the required normalizing point.

`SplitWeylRationality.normalizingPoint` chooses this point, and `normalizingPoint_spec` records its normalizing equation for the chosen descended automorphism. Pairing that equation with `descendedAutomorphism_spec` proves the exact rationality proposition. The point is a representative of the same torus action; no equality of its pullback with the originally supplied point is asserted.

The provenance is internal: all structural inputs and the all-test transporter descent are imported, and this module proves their compatibility under the actual group-scheme and commutative-group-scheme base-change functors. It constructs no Weyl quotient scheme or root datum and does not prove the host generic-fibre isomorphism theorem. The source interpretation of the rationality proposition belongs to its separately submitted statement module; the proof here implements integral-coordinate automorphism descent and fpqc transporter descent.
