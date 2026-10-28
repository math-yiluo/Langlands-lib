# Isomorphism detection on quasi-separated test schemes

`Langlands.AlgebraicGeometry.quasiSeparatedTestIsoDetection.{u}` proves the
published proposition
`Langlands.AlgebraicGeometry.QuasiSeparatedTestIsoDetectionStatement.{u}`.
The target and its imported declarations are unchanged. The theorem works in
arbitrary universe `u`, with no geometric assumptions on the base, source
or target.

For an arbitrary scheme `S`, objects `P Q : Over S` and morphism `f : P ⟶ Q`,
the hypothesis is that postcomposition with `f` is bijective on morphisms
from every `T : Over S` with `QuasiSeparatedSpace T.left`. The conclusion is
`IsIso f` in the actual category `Over S`.

## Provenance

This is a derived internal scheme-theoretic argument, not a theorem quoted
from external literature. Worker 535 implemented the affine-cover proof in
the unreviewed `QuasiSeparatedTestIsoPrototype` shared with the relative
dual flatness task. Worker 453 adapted that proof to import and prove the
published statement, and prepared this explanation. The prototype's
development checks are not acceptance evidence for this proof.

## Implemented proof

The private helper `left_cancel_of_quasiSeparated_tests` first extends the
injectivity hypothesis to arbitrary scheme sources. Let `W` be any scheme
and let `a b : W ⟶ P.left` satisfy `a ≫ f.left = b ≫ f.left`. Since `f`
is a morphism over `S`, the equation `Over.w f` implies
`a ≫ P.hom = b ≫ P.hom`.

Restrict `a` and `b` to a chart of `W.affineCover`. Give that affine chart
the structure morphism to `S` obtained by composing its inclusion with `a`
and `P.hom`. The preceding equality makes the restriction of `b` a
morphism over the same `S`. Each chart is affine, hence its underlying space
is quasi-separated by Mathlib's `quasiSeparatedSpace_of_isAffine` instance.
Injectivity on this admissible test identifies the two restrictions.
`Scheme.Cover.hom_ext` then gives `a = b`. This proves `Mono f.left`,
without a hypothesis on `W`.

Next let `U := Q.left.affineCover`. For each chart, equip `U.X i` with
structure morphism `U.f i ≫ Q.hom` to `S`. It is an admissible affine test.
Surjectivity supplies a morphism `lifts i : Over.mk (U.f i ≫ Q.hom) ⟶ P`
whose composite with `f` is the chart map to `Q`. Projecting to underlying
scheme morphisms gives
`(lifts i).left ≫ f.left = U.f i`.

The local lifts agree on the pullback of any two chart inclusions:
after composing with `f.left`, the desired equality is exactly
`pullback.condition`, using the local lifting identities.
Cancellation by the established monomorphism `f.left` proves the equality
before composition. No quasi-separatedness or quasi-compactness of these
pullbacks is used.

`U.glueMorphisms` now constructs an actual scheme morphism
`g : Q.left ⟶ P.left` from these compatible lifts. Its restriction formula
`Scheme.Cover.ι_glueMorphisms_assoc` and cover extensionality show
`g ≫ f.left = 𝟙 Q.left`. Cancelling the monomorphism `f.left` in this
identity gives `f.left ≫ g = 𝟙 P.left`. The Lean proof packages these two
identities as an isomorphism `P.left ≅ Q.left` with homomorphism `f.left`.

Finally the proof installs `IsIso ((Over.forget S).map f)` using this
explicit scheme isomorphism. Mathlib's isomorphism reflection for
`Over.forget S`, applied by `isIso_of_reflects_iso`, yields `IsIso f` over
`S`. Thus the conclusion has an inverse in `Over S`, rather than only an
inverse between underlying schemes. Compatibility with the structure
morphisms is supplied by the reflection theorem from `f`'s compatibility.

The only uses of the testing hypothesis are on affine charts. Neither `S`,
`P.left`, `Q.left` nor the overlaps are assumed quasi-separated,
quasi-compact, separated, noetherian or affine. The proof uses no Picard
functor, parameter-scheme representability result or relative dual
geometry theorem.
