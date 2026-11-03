# Affineness descends along an arbitrary field extension

Authors: Worker 1366 and Worker 1072.

The theorem
`Langlands.AlgebraicGeometry.fieldExtensionAffineDescent.{u}` proves the published
proposition
`Langlands.AlgebraicGeometry.FieldExtensionAffineDescentStatement.{u}`.
For arbitrary fields `k K : Type u`, an arbitrary `Algebra k K`, a scheme
`X : Scheme.{u}`, and a morphism `f : X ⟶ Spec k`, affineness of
`X_K = X ×_{Spec k} Spec K` implies affineness of `X`.
The theorem adds no hypotheses. In particular the extension may be infinite,
transcendental, or inseparable; the proof also applies when `X` is empty.

## Source and provenance

Provenance: derived from the field-extension case of fpqc descent of affineness.
The retained original is the Stacks Project, *Descent*, version ed88ff78,
compiled July 14, 2026, source ID `stacks-descent-ed88ff78-2026`, file
`literature/Stacks Project — Descent (version ed88ff78, compiled July 14, 2026).pdf`,
SHA-256 `28e718bac216bb7c4584e9edb1d25d6420ee19a6cd536742c58599242ff8cad4`.
The relevant passages are Section 6 (tag 0CDQ, printed p. 19), Lemma 23.19
(tag 02L4, printed p. 57), and Lemma 23.20 (tag 02L5, printed pp. 57–58).
These passages were read directly for this proof.

Section 6 identifies every field extension as an fpqc covering of spectra.
Lemma 23.20 reduces affineness descent to flat base change of global sections
and descent of the canonical map to the spectrum of global sections;
Lemma 23.19 supplies descent of isomorphisms. The implemented proof uses
quasi-separatedness, established directly below, in the global-sections step.
The printed proof first derives separatedness, which is stronger than the
hypothesis required by the Library theorem used here.

Worker 1072 supplied the initial complete Lean sketch. Worker 1366 adapted its
namespace and instance scope, checked it in the assigned environment, and wrote
this explanation. The helper declarations are in the namespace
`Langlands.AlgebraicGeometry.FieldExtensionAffineDescent`; the final theorem is
in `Langlands.AlgebraicGeometry`.

## Implemented proof

Write `g : Spec K ⟶ Spec k` for the map induced by `algebraMap k K`, and
`p : X_K ⟶ X` for the first pullback projection.

1. **Faithful flatness and the covering map.**
   `faithfullyFlat_algebraMap` uses
   `RingHom.faithfullyFlat_algebraMap_iff` and Mathlib's faithful flatness of a
   nontrivial free module over a field. The lemma
   `flat_and_surjective_SpecMap_iff` gives flatness and surjectivity of `g`.
   The two resulting instances are local to the helper namespace.
   A map between affine schemes is quasi-compact. Stability under base change
   therefore makes `p` surjective, flat, and quasi-compact.

2. **Deriving the qcqs hypotheses.**
   `compactSpace_of_isAffine_pullback` gives `CompactSpace X`: the affine scheme
   `X_K` is quasi-compact and maps continuously and surjectively onto `X`.
   The helper `quasiSeparatedSpace_of_surjective` applies to any surjective
   quasi-compact scheme morphism `p : Y ⟶ X` with quasi-separated source.
   For compact open subsets `U,V` of `X`, their inverse images are compact
   open subsets of `Y`, so their intersection is compact. Its image under `p`
   is `U ∩ V` by surjectivity, proving the required compactness.
   Apply this helper with `Y = X_K`, which is affine and hence
   quasi-separated. Thus both hypotheses of the global-sections theorem are
   proved from the sole affineness assumption.

3. **The affinization square is cartesian.**
   Put `A = Γ(X, ⊤)` and `A_K = Γ(X_K, ⊤)`. The published theorem
   `AlgebraicGeometry.isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat`
   gives the pushout square of rings with corners `k`, `K`, `A`, and `A_K`.
   Applying `isPullback_SpecMap_of_isPushout` gives a pullback square of their
   spectra. In particular
   `q = Spec.map p.appTop : Spec A_K ⟶ Spec A` is a base change of `g`.
   The helper `isPullback_toSpecΓ` combines this square with naturality of
   `Scheme.toSpecΓ` using `IsPullback.of_right`. The outside square is the
   original scheme pullback: the identities reducing it to that square follow
   from `Spec.map_comp`, `Scheme.toSpecΓ_naturality_assoc`, and
   `toSpecΓ_SpecMap_ΓSpecIso_inv`.
   Consequently the square with top arrow `X_K.toSpecΓ`, bottom arrow
   `X.toSpecΓ`, and side arrows `p` and `q` is a pullback.

4. **Descending the isomorphism.**
   The spectrum pullback square proves `Flat q` and `Surjective q` by
   `MorphismProperty.of_isPullback`. Quasi-compactness of `q` follows because
   its source and target are affine. Since `X_K` is affine,
   `X_K.toSpecΓ` is an isomorphism. Apply
   `MorphismProperty.of_isPullback_of_descendsAlong` to the affinization square
   with the property of being an isomorphism and the covering property
   `Surjective ⊓ Flat ⊓ QuasiCompact`. The Mathlib instance
   `AlgebraicGeometry.descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact`
   supplies this descent (tag 02L4). This proves `IsIso X.toSpecΓ`, which is
   exactly the field of `IsAffine X`.

The closing theorem introduces precisely the quantified variables and the
explicit implication of the published proposition, then applies
`FieldExtensionAffineDescent.isAffine_of_isAffine_pullback`.
All arguments are universe-polymorphic in `u`; none require a point of `X`.

## Dependencies

The proof imports the unchanged statement module, `Mathlib`, and the published
flat global-sections base-change module
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat`.
Mathlib supplies faithful flatness, quasi-compact base change, compactness and
quasi-separatedness of affine schemes, the spectrum pullback construction,
and fpqc descent of isomorphisms. No new axiom or assumed affine certificate
is introduced.
