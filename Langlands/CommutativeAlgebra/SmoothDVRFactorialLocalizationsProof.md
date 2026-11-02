# Factorial prime localizations of smooth algebras over DVRs

`Langlands.CommutativeAlgebra.smoothDVRFactorialLocalizations.{u}` proves exactly
`Langlands.CommutativeAlgebra.SmoothDVRFactorialLocalizationsStatement.{u}`,
with no outer hypotheses. For every genuine discrete valuation domain `R`,
every smooth commutative `R`-algebra `A` with its specified algebra structure,
and every prime `P` of `A`, the actual ring `Localization.AtPrime P` has
unique factorization. The universe `u` is arbitrary. The algebra need not be a
domain, and there are no restrictions on characteristic, residue field,
completeness, henselianity or excellence.

## Implemented proof

The three regularity lemmas lie in
`Langlands.CommutativeAlgebra.SmoothDVRFactorialLocalizationsProof` and allow
the base and algebra to occupy independent universes.

First, `regularLocal_of_flat_unramified` treats a flat, essentially finite type,
formally unramified local algebra over a regular local ring, assuming the
algebra is Noetherian. Mathlib's unramified local-ring result identifies the
maximal ideal upstairs with the extension of the maximal ideal downstairs.
Extension cannot increase the minimal number of generators of this finitely
generated ideal. Flatness gives going down, so the height formula for the two
maximal ideals shows that Krull dimension cannot decrease. The two inequalities
and regularity of the base prove the regular-local criterion upstairs.

Second, `regularLocal_localization_of_etale` localizes an etale algebra at a
prime and the base at its contracted prime. Finite type over a Noetherian base
makes the algebra Noetherian. The induced local map is flat, essentially finite
type and formally unramified, so the preceding lemma applies. Regularity of
the base ring supplies regularity of its prime localization.

Third, `regularLocal_localization_of_smooth` chooses a standard-etale chart over
a polynomial ring near the given prime. A finite polynomial ring over a regular
ring is regular. The etale lemma therefore makes the chart's prime localization
regular local. The iterated-localization ring equivalence and the equality
between the contracted chart prime and the original prime transport regularity
to the actual ring `Localization.AtPrime P`.

In the closing theorem, a DVR is a regular ring through Mathlib's
Dedekind-domain regularity instance. The explicit smoothness argument is
installed as an instance, and the smooth regularity lemma applies to each
prime localization. The published unconditional theorem
`Langlands.CommutativeAlgebra.regularLocalFactorial`, imported from
`Langlands.CommutativeAlgebra.RegularLocalFactorialProof`, then gives unique
factorization. The final theorem has no conditional factoriality argument.
The target proposition and its imported files are preserved.

## Provenance and authorship

This is an internal affine derivation of the smooth-ascent specialization of
Stacks Project Lemma 35.18.4,
[Tag 036D](https://stacks.math.columbia.edu/tag/036D), followed by the published
regular-local factoriality theorem, whose source is Lemma 15.123.2,
[Tag 0AG0](https://stacks.math.columbia.edu/tag/0AG0). It does not reproduce the
scheme-level descent proof of 036D. The retained originals are `036D.html` in
registered source `stacks-smooth-local-regularity-036D-2026-11-01`, directory
SHA256 `5496a4516f93572c6619901d7a60fd14a8b0c258b6f89742ae3944cd17de49e6`,
and `0AG0.html` in `stacks-regular-local-ufd-2026-10-29`, directory SHA256
`49b665ff41945fd15cc966fe79e70688059509c0487cc27f32167fe1e1baed31`.
Both complete tag pages and proofs were read; they have no comments. The
factoriality proof module documents its algebraic localization and Picard
prerequisites and the correction in the retained 0AFZ comments.

Worker 399 authored the three regularity lemmas and the original conditional
DVR adapter. Worker 669 assembled the unconditional theorem using the published
factoriality theorem and prepared this final paired explanation. Imported
published proofs retain their own authorship. No geometric or valuative
extension conclusion, or result depending on one, enters this proof.
