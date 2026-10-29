# Extending compatible affine norms

The construction `AffineNormGluing.norm` extends a compatible family of
multiplicative maps on the affine opens of a scheme to a family on all its opens.
It applies to an arbitrary scheme morphism `π : Y ⟶ X`. Its input consists of maps
`N V : Γ(Y, π⁻¹ V) →* Γ(X, V)` for every affine open `V` of `X`, together with
compatibility for every inclusion of affine opens. It uses classical choice to
select the unique glued section. It imposes no condition on the schemes or the
morphism beyond these explicit inputs.

`affine_ext` tests equality of sections on all contained affine opens, and
`affine_cover` proves that those opens cover any given open. To establish the
matching condition, `compatible` tests equality on an overlap using the affine
opens contained in that overlap. Thus the argument does not require affine
intersections. `existsUnique_norm` applies the structure sheaf's unique-gluing
property, and `normSection` selects the resulting section. `res_normSection`
records its restrictions. Equality on affine subopens proves that this operation
preserves one and multiplication, which defines the monoid homomorphism `norm`.
The same restriction argument proves its naturality for every open inclusion.

The additional lemma `degree` assumes an affine scalar degree law for a natural
number `d` and extends that law to every open, using naturality of the morphism's
maps on sections. The lemma `basicOpen` assumes the exact affine point-set equality

`basicOpen (N V f) = {x ∈ V | ∀ y, π(y) = x → y ∈ basicOpen f}`

and proves the same equality over every open. For each inclusion, it chooses an
affine neighbourhood of the point and uses `Scheme.basicOpen_res` in both the base
and the source. Both inclusions are implemented. These lemmas do not construct an
affine norm family or assert the unconditional finite-field extension theorem.

This is an internal derived sheaf construction for the proof of
`FiniteFieldExtensionNormStatement`. Its motivating source is the local-to-global
step of Stacks Project Section 31.18, Lemma 31.18.6 (tag 0BD2), in registered source
`stacks-norms-field-ample-descent-2026-10-26`, retained file `0BCX.html`. The
implemented argument uses all affine subopens and Mathlib's unique-gluing theorem;
it is not a transcription of a chosen-basis construction in that source.
