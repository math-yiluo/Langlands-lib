# Exact lifting of closed split subgroups over Henselian rings

`Langlands.GroupScheme.henselianClosedSplitHomLift` takes a Henselian local
commutative ring `R`, a field `k` with a surjective algebra map `R → k`, a
split torus `H` over `Spec R`, and a smooth affine group scheme `G` over
`Spec R`. Given an actual closed subgroup homomorphism `i₀ : H_k → G_k`,
it returns a homomorphism `i : H → G`, a proof that `i` is a closed subgroup,
and the exact equality `i_k = i₀`. All ring and field types are in an arbitrary
universe `u`; no characteristic or reductivity hypothesis is used.

This is an internal refinement of the existence construction in
`Langlands.GroupScheme.Torus.HenselianSplitRank`. It keeps the prescribed
residue homomorphism, which that module's split-rank existence result does
not expose. The selected definition chooses a witness from the proved
`exists_closed_splitHom_lift`.

The proof uses `HomScheme.smoothSplitSourceRepresentability` to represent
homomorphisms out of the given split torus by a smooth scheme `M` with a
universal homomorphism. The specified `i₀` gives a `k`-valued point of `M`.
`exists_open_isClosedImmersion_baseChange` provides an open neighborhood of
that point on which the universal homomorphism is a closed immersion.
The smooth pointed section theorem
`Langlands.CommutativeAlgebra.HenselianSections.exists_section_of_smooth_of_surjective`
lifts the point to a section over `Spec R`. Pulling back the universal
homomorphism along this section and applying the identity-base-change
isomorphisms produces `i`. Closedness is preserved by pullback and source
and target isomorphisms. `HomScheme.evaluate_comp` and the section's exact
residue-point equation show that its residue homomorphism equals `i₀`.
The published `HomScheme.evaluate_identityBase` from
`HomScheme.HenselianSplitSourceLifting`, applied to `Over.mk c`, expresses this
final identity using the canonical identity-base-change isomorphisms.

The supporting lemma `RelativeTorus.IsTorus.smooth_of_isLocalRing` proves
smoothness for any relative torus over a local ring. An affine open of an
etale splitting-cover member is chosen above the closed point. Its image is
open and contains that point, hence contains every point of the local base.
The composite is therefore a surjective, flat, quasi-compact map. The torus
is split after this pullback, so smoothness descends by the published
Mathlib local-flat-descent theorem. This supplies smoothness of the ambient
relative torus when applying the lift to a subtorus.

These constructions use the published Hom-scheme, open closed-immersion,
Henselian-section, relative-torus and split-torus interfaces, together with
Mathlib's descent of smoothness. They introduce no additional literature
assertion. Constructing a torus containing a prescribed integral split
torus and proving the fixed-pair special-apartment statement remain separate
obligations.
