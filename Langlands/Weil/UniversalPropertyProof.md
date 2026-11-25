# Universal properties of the generic Weil pullback

`Langlands.Weil.universalProperty` proves the imported proposition
`Langlands.Weil.UniversalProperty` with both independent universe parameters
`u` and `v`. The proof treats the original group with its topology and the
group mapping into it at exactly the generality of the statement.
It requires neither surjectivity nor a chosen Frobenius lift, and it assumes
no continuity of either group's operations.

## Implemented proof

For the algebraic clause, the proof takes compatible homomorphisms
`a : H →* Γ` and `b : H →* Degree`. It forms their product homomorphism
`a.prod b` and restricts its codomain to `pullbackSubgroup φ`.
Evaluation of the compatibility equation at each `x` supplies precisely
`φ (a x) = frobenius (b x)`, the membership condition for this restriction.
Thus the constructed map sends `x` to the pair `(a x, b x)`.

Both coordinate equations follow by homomorphism extensionality and
definitional equality. For uniqueness, any competing bundled homomorphism
has these same coordinates at every `x`. The proof applies homomorphism
extensionality, subtype extensionality, and product extensionality, using
the two supplied coordinate equations.

For the continuous clause, the proof repeats this codomain restriction on
the underlying monoid homomorphisms. Its continuity proof first combines
the continuity of `a` and `b` into continuity of their product, then uses
continuity into a subtype. The coordinate identities again follow by
definitional equality. Continuous-homomorphism extensionality reduces
uniqueness to the same equality of subtype values and their two coordinates.

The closing theorem proves both conjuncts of the imported target directly.
It neither redefines the target nor uses the separately stated algebraic
or inertia-topology properties as proved results.

## Exact dependencies and provenance

- Statement:
  `Langlands/Weil/UniversalProperty.lean` and its paired Markdown.
  Its checked target fingerprint is
  `2a7097fbbeeb56f30f678b9c8454ff31671db3ef7801ef6b30206ef498a57008`.
- Definition:
  `Langlands/Weil/Pullback.lean` and its paired Markdown.
- Environment:
  Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
  and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

This is an internal proof from the pair construction and Mathlib's
product, codomain-restriction, continuity, and extensionality interfaces.
It does not claim a proof quoted from an original source. The
definition and statement Markdown retain the original-source provenance
and the distinction between the generic construction and the actual
local Weil group.

The result concerns the generic pullback only. It supplies no absolute-Galois
or residue-field construction and no identification with a p-adic Weil group.
