# The weak Chow cover of a separated algebraic space of finite type

`ChowCoverStatement` is the interface between two halves of the proof of
`ProperSchemeCoverStatement`:

- the scheme-cover construction, a weak form of Chow's lemma for algebraic spaces
  (Stacks Project, Tag 089I), which proves `ChowCoverStatement`; and
- the finite-presentation refinement (Noetherian approximation of the affine base,
  then properness of the cover over the base), which derives
  `ProperSchemeCoverStatement` from it.

## Statement

Let `S` be an affine scheme and `X` an algebraic space over `S` such that

- `X` is separated (`IsSeparated X`: the diagonal of `X` is represented by closed
  immersions), and
- `X` has an étale surjective atlas whose structure morphism is locally of finite
  presentation and quasi-compact (`HasAtlasProperty (lfp ⊓ qc) X`).

Then there are a scheme `U` over `S` and a morphism `a : h_U → X` such that

1. `a` is surjective (`IsSurjective a`);
2. `a` is represented by proper morphisms: for every scheme `T` over `S` and every
   `T → X`, the projection `U ×_X T → T` is a proper morphism of schemes
   (`(inverseImage IsProper (Over.forget S)).relative (schemeYoneda S) a`);
3. `U → S` is locally of finite type and quasi-compact.

## Provenance

This is a derived statement. Stacks Lemma 089I gives, for `X` separated of finite
type over a Noetherian base, a scheme `X'` with a proper surjective morphism
`X' → X` and `X' → S` H-quasi-projective. The statement here keeps only what the
refinement uses: surjectivity, representability by proper morphisms, and finite
type of `U → S`. It does not assume the base Noetherian; the construction works over
any affine base because the atlas is of finite type. It makes no claim that `U` is
proper over `S`.
