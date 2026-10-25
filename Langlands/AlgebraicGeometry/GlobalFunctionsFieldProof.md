# Global functions of smooth proper geometrically connected schemes over a field

Authors: Worker 129 and Worker 428. Worker 129 constructed the proof;
Worker 428 checked its implementation, source correspondence, and exact
statement wrapper and prepared the submission.

The final lemma
`Langlands.AlgebraicGeometry.GlobalFunctionsFieldProof.isIso_appTop_of_field`
proves the following in every universe `u`: for any field `K : Type u`,
scheme `X : Scheme.{u}`, and smooth proper geometrically connected morphism
`p : X ⟶ Spec (CommRingCat.of K)`, the canonical map
`p.appTop : Γ(Spec K, ⊤) ⟶ Γ(X, ⊤)` is an isomorphism.
The hypotheses impose no additional restrictions on the field or scheme.

## Source and implemented route

The mathematical assertion is the smooth specialization of Stacks Project
Varieties Lemma 33.9.3, Tag [0BUG](https://stacks.math.columbia.edu/tag/0BUG),
item (7), using smooth geometric reducedness from Lemma 33.25.4, Tag
[056T](https://stacks.math.columbia.edu/tag/056T).
Both originals are retained as `0BUG.html` and `056T.html` in the registered
source `stacks-global-functions-field-and-fibre-criterion-2026-10-23`,
HTML snapshot retrieved 2026-10-23, directory SHA256
`c170b7f07df230ebbd77e6b3dc8774e0061520328c065c87cfd45554d2ddb850`.
The retained statements, proofs, and comments were checked. Item (7)
requires geometric connectedness, as clarified by the source's correction
of an earlier ambiguous wording. No source-specific project erratum was
found.

The implementation uses the algebraic closure and faithfully flat descent.
The ring argument below is an internal derivation using Mathlib, rather
than a transcription of the source's decomposition of the entire algebra
of global functions into a finite product of fields.

## The algebraically closed case

`scalar_surjective_of_integral_of_preconnected` concerns a reduced,
nonzero integral algebra `A` over an algebraically closed field `K` with
preconnected `PrimeSpectrum A`. Its conclusion is surjectivity of the
actual scalar map `algebraMap K A`.

For each `x : A`, let `B = K[x]`. Integrality makes `B` finite over `K`,
hence Artinian; reducedness descends from `A` along the subalgebra
inclusion. The extension `B → A` is integral, so its map of prime spectra
is surjective. It follows that `PrimeSpectrum B` is preconnected.
The spectrum of an Artinian ring is totally disconnected, so this spectrum
is subsingleton. Mathlib's
`PrimeSpectrum.subsingleton_iff_isField_of_isReduced` makes `B` a field.
Then `IsAlgClosed.algebraMap_bijective_of_isIntegral` shows that `x` is
a scalar.

`isIso_appTop_of_algClosed` applies this argument to `Γ(X, ⊤)`.
The imported
`Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field`
supplies reducedness. Geometric connectedness gives connected and nonempty
`X`; nonemptiness makes its ring of global functions nonzero. Properness
gives compactness, and the dominant affinization map
`X → Spec Γ(X, ⊤)` gives a preconnected spectrum.

Under `Scheme.ΓSpecIso (CommRingCat.of K)`, the scalar map is
`g = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop`.
Mathlib's `isIntegral_appTop_of_universallyClosed`, transported through
this canonical identification, makes `g` integral. The ring argument gives
surjectivity; injectivity follows because `K` is a field and the target
is nonzero. Thus `g` is an isomorphism. Cancelling the canonical
isomorphism proves `IsIso p.appTop`.

## Descent to an arbitrary field

`isIso_of_isPushout_of_faithfullyFlat` treats a pushout square of
commutative rings. If one base map is faithfully flat and the
base-changed map is an isomorphism, Mathlib's
`RingHom.FaithfullyFlat.codescendsAlong_bijective` gives bijectivity,
and therefore invertibility, of the original map.

`isIso_appTop_of_field` base changes `p` along
`q : Spec (AlgebraicClosure K) → Spec K`. This morphism is flat.
The pullback remains smooth, proper, and geometrically connected, so its
canonical section map is an isomorphism by the algebraically closed case.

Properness gives quasi-compactness and quasi-separatedness of `X`.
With the affine base and affine extension, these hypotheses allow
`isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` to identify
the square of global-section maps as a pushout. The map `q.appTop`
is faithfully flat: its source is a field under `ΓSpecIso`, and its
target is nonzero. The pushout descent lemma proves `IsIso p.appTop`
for the original canonical map.

The reducedness helper has its own statement and proof publication
sequence, and is imported by Lean module name. The exact proposition
wrapper is documented in
[FieldSmoothProperConnectedGlobalFunctionsProof.md](FieldSmoothProperConnectedGlobalFunctionsProof.md).
This proof concerns the field case; the relative assertion over arbitrary
base schemes requires an additional argument.
