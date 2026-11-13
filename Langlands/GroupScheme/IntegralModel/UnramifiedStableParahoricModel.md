# Conditional descent of a simply connected stable parahoric model

This internal assembly combines the existing parahoric-model statement,
zero-subgroup lemma, stable-set model descent and connected-fibre descent. It
retains explicit proofs of `UnramifiedParahoricModelStatement` and
`UnramifiedSmoothModelDescentStatement` as premises. It asserts neither statement
unconditionally and does not prove the host Iwahori-model target.

The other inputs are an original local field `F`, an affine group scheme `G`
over `F`, simple connectedness of its actual maximal-unramified extension,
arbitrary supplied building and semilinear data `C` and `D`, a zero datum `E`,
and a subset `Y` given as a translate of a nonempty apartment subset on which
every real affine functional is bounded above. The subset must be stable under
every supplied semilinear coefficient action. The final geometric premise says
that every rational point stabilizing `Y` setwise fixes it pointwise. None of
these geometric conditions is inferred from a chamber hypothesis in this file.
All constructions hold at arbitrary universe `u`.

`exists_descendedStableParahoricModel` applies the supplied parahoric statement
and selects its neutral model `P.neutral`. The zero-subgroup lemma for simple
connectedness rewrites this model's integral-point image to the pointwise fixer
of `Y`. Pointwise fixation implies setwise stabilization directly, and the
supplied geometric premise gives the converse. Thus that image is exactly the
full setwise stabilizer.

The stable-set descent construction now supplies a smooth model over the
original integers together with an actual isomorphism of its unramified base
change to `P.neutral`, compatible with the identity of the generic group. The
connected-fibre helper transports the neutral model's connected fibres through
this isomorphism and descends connectedness to the full special fibre of the
original model. The same isomorphism identifies the integral-point images.

`descendedStableParahoricModel` chooses the resulting actual integral model.
Its three specification lemmas retain smoothness, connectedness of its full
special fibre and the original rational-point membership equivalence with
setwise stabilization. The result is a conditional assembly of published
interfaces and internal helper lemmas, without further literature claims.
