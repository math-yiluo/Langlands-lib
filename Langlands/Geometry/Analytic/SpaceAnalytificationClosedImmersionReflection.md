# Reflection of closed immersions by analytification

A monomorphism of algebraic spaces with locally finite type source and
separated target is representable. For a scheme test into the target,
the algebraic-space pullback maps monomorphically to the test. An étale
atlas of the source gives a represented atlas of this pullback. The
atlas scheme is a closed subscheme of the product of the source atlas
and the test scheme, by separatedness of the target. Its projection
to the test is locally of finite type. The Library's schemehood theorem
for locally finite type monomorphisms into schemes gives a representing
scheme, with an isomorphism to the actual presheaf pullback.

`schemePullbackModelOfMono` chooses this scheme and its isomorphism.
The representability theorem transports the projections through that
isomorphism. These are internal consequences of the Library's
algebraic-space pullback, atlas and schemehood interfaces.

For a quasi-compact algebraic-space morphism, the represented pullback
over an affine test has a quasi-compact scheme atlas. The represented
surjective map from that atlas makes the representing scheme
quasi-compact. Since the target test is affine, the scheme projection
is quasi-compact.

To test closedness, choose a locally finite type étale target atlas
and take its affine open cover. Each open has a finite-type coordinate
algebra. The pullback of the represented projection to that open is
the represented pullback of the original morphism to the corresponding
affine test. Zariski locality for scheme closed immersions gives
closedness on the full atlas, and the Library's étale descent theorem
for represented properties gives the result for the original map.

The reflection theorem takes a complete, nontrivially normed
ultrametric field `K`, separated algebraic spaces `X'` and `X`
locally of finite type over `Spec K`, and a quasi-compact algebraic
map `f : X' ⟶ X`. It takes supplied analytifications with point
families `p'` and `p` and a closed immersion `F` between them.
Compatibility means `p' A P x ≫ F = p A P (RingPoints.map f x)` for
every presented affine point of `X'`.

The proof uses monicity of analytic closed immersions and the
reflection theorem for compatible monomorphisms on separated
algebraic spaces. Separatedness of `X'` supplies the closed source
overlaps for that theorem. The presheaf leg `b` from the representing
scheme of an étale affine pullback to `X'` is étale by base change.
The representing scheme is locally of finite type over the field
and is separated because its projection to the affine test is
monic. Given a compatible analytification of that scheme forming
the analytic pullback square, analytic closed immersion base change
makes the analytic projection closed. The assumed scheme reflection
direction then makes the quasi-compact scheme projection a closed
immersion. The three additional inputs are the compatible analytic
test pullbacks, analytic closed immersion base change, and closed
immersion reflection for scheme maps to the affine tests.
