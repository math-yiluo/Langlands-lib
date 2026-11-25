# Descent proof for homomorphisms of group extensions

`Langlands.GroupScheme.fppfExtensionClosedImmersion.{u}` proves exactly
`Langlands.GroupScheme.FppfExtensionClosedImmersionStatement.{u}`.
It uses the actual kernel-pair isomorphism, the kernel-valued difference
of points with the same image, and descent of proper monomorphisms.
The universe `u` and the base scheme are arbitrary, with exactly the
hypotheses of the published statement.

For the pullback `P = G' ×[Q'] Q`, the factorization of `f` is covered by
`G × ker(q') → P`, sending `(g,k')` to `(f(g)k',q(g))`.
The first pullback square identifies this cover as a base change of `q`.
The second identifies the pullback of the factorization with
`id_G × a : G × ker(q) → G × ker(q')`. Both squares are proved by their
universal properties, using differences in the actual kernels.

Flatness, surjectivity, and local finite presentation of the first cover
follow by base change. The second square descends the closed immersion
`id_G × a` to the factorization. The projection `P → G'` is a closed
immersion by base change from `c`. Their composition is `f`.

The closed-immersion descent instance follows from the proper-monomorphism
criterion: properness descends by the Library's fpqc descent theorem;
monomorphisms descend because the diagonal is an isomorphism, and
isomorphisms descend fpqc. Mathlib converts this to descent along
flat surjective morphisms locally of finite presentation.

The provenance is the derived strengthening of Brian Conrad,
*Reductive group schemes* (2014), Lemma 5.3.8, p.169, disclosed in the
statement's Markdown. The registered source is
`conrad-2014-reductive-group-schemes` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`).
Conrad's lemma assumes short exact sequences of flat, separated,
finitely presented group schemes and proves properness by a valuative
argument after a Noetherian reduction. This internal proof instead uses
the two pullback squares and descent above, requiring only the source
quotient to be an fppf cover. It imposes no such condition on the target
quotient and no finiteness or separatedness condition on the group schemes.
