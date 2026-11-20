# Localized étaleness of analytified étale maps, conditionally

This module is a conditional assembly with derived provenance. It concerns the
proposition used as input 5 of `SpaceAnalytificationExistenceReductionStatement`: for an
étale map `f : A →ₐ[K] B` of finitely presented `K`-algebras with finite polynomial
presentations `P` and `Q`, the localized morphism `localizedHom K P Q f` is `etale`.
**This proposition is not proved here.** It is derived from two inputs, neither of which
is proved in the Library.

## Declarations

- `AffineAnalytificationLocalizedEtaleReductionStatement` (the entry declaration) is a
  proposition with two hypotheses.
  1. The published statement `AffineAnalytificationEtaleStatement.{u, u, u}`, the affine
     case of Berkovich (1993), Propositions 3.2.10 and 3.3.11, over the ground field. Its
     étale clause says that `f` is étale if and only if the strong map
     `saturatedHom K P Q f` is `StrongHom.IsEtale` (finite pieces). The statement is
     viewed with the original presentations `presentation K Q` and `presentation K P`.
  2. An index-universe comparison, written out in full. Let `X` and `Y` be affinoid atlas
     presentations with universe profile `{u, u, 0}`, the profile of every
     `presentation K P`. Then every strong map `g : ofSaturation X ⟶ ofSaturation Y`
     that is `IsEtaleAllPieces` with respect to `X` and `Y` is `strongEtale`.

     This is the direction `←` of the published `strongEtale_ofSaturation_iff`, which is
     stated only for the profile `{u, v, v}`. Its proof in the Library goes through
     quasi-isomorphism lemmas that are stated for presentations sharing one profile.
     Mixing `X` with `X.saturatedPresentation` (profile `{u, u, u}`) therefore needs new
     work. The Library Markdown of `SpaceAnalytificationEtaleReflection` records the same
     universe gap.

  The conclusion is input 5 in its exact form: for all `K`, `A`, `B : Type u`, presentations
  `P`, `Q` and `f`, `f.toRingHom.Etale → etale (localizedHom K P Q f)`.
- `affineAnalytificationLocalizedEtaleReduction` proves the proposition in four steps.
  1. Hypothesis 1 gives `StrongHom.IsEtale` for `saturatedHom K P Q f`.
  2. `StrongHom.IsEtale.isEtaleAllPieces`, from `FinitePiecesFlatUnramifiedAllPieces`,
     upgrades this to `IsEtaleAllPieces`.
  3. Hypothesis 2 gives `strongEtale (saturatedHom K P Q f)`, since `saturated K P` is
     `ofSaturation (presentation K P)` by definition.
  4. The published `etale_localizationFunctor_map_iff_strongEtale` gives `etale` for the
     image `localizedHom K P Q f` in the localized category.

## Scope

The field `K : Type u` is complete, ultrametric and nontrivially normed. The algebras
are in `Type u`, as in input 5 of the existence reduction. The finite-to-all upgrade in
step 2 is unconditional. The analytic content of input 5 lies in
`AffineAnalytificationEtaleStatement`, and the remaining hypothesis concerns only
universes.
