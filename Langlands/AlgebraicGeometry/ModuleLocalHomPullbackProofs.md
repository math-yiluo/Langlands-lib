# Sheaf laws for local internal-Hom pullback

The theorem `Langlands.Scheme.Modules.localHomPullbackSheafLaws` proves exactly
`LocalHomPullbackSheafLawsStatement` from
[ModuleLocalHomPullbackStatements](ModuleLocalHomPullbackStatements.md). Its two
components are `localHomPullback_restrict : LocalHomPullbackRestrictionStatement`
and `localHomPullback_smul : LocalHomPullbackScalarStatement`. Both concern the
fixed published `localHomPullback` from
[ModuleLocalHomPullback](ModuleLocalHomPullback.md), for arbitrary schemes, scheme
morphisms and module sheaves, with no further hypotheses. For f : X ⟶ Y, module
sheaves M, N on Y, opens i : V ⟶ U of Y and a local morphism h from M to N on U,
the restriction law says
`localHomPullback f V (LocalHom.restrict i h) =
LocalHom.restrict ((Opens.map f.base).map i) (localHomPullback f U h)`. For a
section r of the structure sheaf on U, the scalar law says
`localHomPullback f U (r • h) = f.app U r • localHomPullback f U h`. This module
does not construct the global dual comparison or prove identity or composition
coherence.

Both component proofs use the injectivity of `internalHomSectionsEquiv` and the
published formula `internalHomSectionsEquiv_localHomPullback`. These turn each
law into an equality of morphisms between restricted module sheaves on an open
subscheme. Like `ModuleLocalHomPullback`, the module sets the elaboration
options `backward.isDefEq.respectTransparency false` and
`backward.defeqAttrib.useBackward true`. It also sets
`backward.isDefEq.respectTransparency.types false`. These options affect only
how definitional unfolding is attempted. They do not change the statements, and
the kernel checks every proof.

## Scalar law

`pushforward_map_appTop_smul` shows that pushforward along f turns
multiplication by `f.appTop r` into multiplication by the global function r. The
proof works sectionwise and uses naturality of f on structure-sheaf sections.
`pullback_map_smul` then shows that pullback is semilinear for global scalars:
`(pullback f).map (r • φ) = f.appTop r • (pullback f).map φ`. It applies the
pullback-pushforward adjunction homEquiv, which is injective, and uses unit
naturality together with bilinearity of composition.

For a section r of the structure sheaf on U, `openScalar U r` is the
corresponding global function on the open subscheme U, given by
`U.topIso.inv r`. `internalHomSectionsEquiv_smul` shows that the section
equivalence sends r • h to `openScalar U r` times the corresponding morphism.
`morphismRestrict_appTop_openScalar` shows that the restricted morphism
`f ∣_ U` sends `openScalar U r` to `openScalar (f⁻¹U) (f.app U r)`.
`localHomPullback_smul` combines these identities with `pullback_map_smul` and
moves the scalar through the two conjugating isomorphisms by linearity of
composition.

## Restriction law

The restriction proof first works with arbitrary open immersions, and only at
the end with the specific inverse-image opens.

General helpers:

- `presheaf_map_subsingleton` says that parallel restriction maps between opens
  agree.
- `compHom_isIso` is an instance: the published comparison `compHom` from
  `Picard.RigidifiedPullbackProofs` is an isomorphism. This categorical helper
  is stated for arbitrary scheme-module pullbacks and uses no line-bundle
  hypothesis.
- `compHom_naturality` says that `compHom` is natural in the module.
- `conjugate_square` is a lemma about a square of functors related by a natural
  isomorphism. Conjugating a morphism k by one route equals conjugating it by
  the other, provided the conjugating isomorphisms are compatible on the source
  and on the target.

Open immersions:

- `restrictCompIso a b c h` identifies restriction along c with iterated
  restriction along b and then a, when a ≫ b = c. It is defined from Mathlib's
  `restrictFunctorCongr` and `restrictFunctorComp`.
- `restrictCompIso_hom_app_comp` says that, under Mathlib's
  `restrictFunctorIsoPullback`, `restrictCompIso` corresponds to `compHom`, so
  iterated restriction matches iterated pullback.
  The proof applies the restriction adjunction's homEquiv, which is injective.
  It uses three helper lemmas:
  - `restrictAdjunction_unit_restrictFunctorIsoPullback`: the restriction unit
    becomes the pullback unit;
  - `restrictAdjunction_unit_restrictCompIso`: the unit for a composite factors
    through the units of its factors;
  - `pullbackPushforwardAdjunction_unit_comp`: the pullback units compose
    through `pullbackComp`, via Mathlib's `conjugateEquiv_pullbackComp_inv`.

Commutative squares:

- `restrictPullbackSquareIso f j k g h` generalizes the published
  `restrictPullbackNatIso` to any commutative square g ≫ j = k ≫ f with open
  immersions j and k. It is built from the same isomorphisms
  (`restrictFunctorIsoPullback`, `pullbackComp`, `pullbackCongr`).
  `restrictPullbackNatIso_eq` records that the published iso is the instance for
  `(f ⁻¹ᵁ U).ι`, `U.ι` and `f ∣_ U`, and holds by `rfl`.
- `restrictPullbackSquareIso_hom_app_comp` expresses the iso through `compHom`
  and the inverse of `pullbackComp`.
- `pullback_restriction_coherence` is the pure pullback coherence for a cube made
  of two such squares and two factorizations a ≫ jU = jV and b ≫ kU = kV. It
  uses three instances of `compHom_assoc` after cancelling a `pullbackComp`
  component.
- `restrictPullbackSquareIso_restrict` deduces from it that the square
  isomorphism on the smaller opens, followed by iterated restriction, equals
  iterated restriction followed by the square isomorphisms on the larger opens
  and on the connecting square. The proof cancels on the right the pullback
  along fV of the isomorphism from iterated restriction along jU and a to
  pullback along jV. This isomorphism is built from `restrictFunctorIsoPullback`
  and `compHom`, and is invertible by `compHom_isIso`. It then uses
  `restrictCompIso_hom_app_comp`, `restrictPullbackSquareIso_hom_app_comp`,
  naturality, and `pullback_restriction_coherence`.
- `restrict_conjugation` combines `conjugate_square` with this identity for the
  source and target modules. Pulling back a morphism of restricted modules on
  the larger open and then restricting agrees with restricting first and then
  pulling back.

Opens and local morphisms:

- `LocalHom.app_map'` says that a local morphism commutes with restriction maps
  between smaller opens. `LocalHom.app_conj` deduces that conjugating its
  evaluation by mutually inverse restriction maps changes nothing.
- `internalHomSectionsEquiv_restrict` shows the following for i : V ⟶ U. The
  section equivalence sends `LocalHom.restrict i h` to the restriction, along
  `T.homOfLE`, of the morphism corresponding to h, conjugated by
  `restrictCompIso (T.homOfLE _) U.ι V.ι (T.homOfLE_ι _)`. It is proved
  sectionwise.
- `morphismRestrict_homOfLE` gives the commutative square
  `X.homOfLE _ ≫ f ∣_ U = f ∣_ V ≫ Y.homOfLE _` of inverse-image opens.

`localHomPullback_restrict` rewrites both sides with
`internalHomSectionsEquiv_localHomPullback` and
`internalHomSectionsEquiv_restrict`. The resulting identity is
`restrict_conjugation` for the inverse-image square, with the equations
`homOfLE_ι`, `morphismRestrict_ι` and `morphismRestrict_homOfLE`.

## Provenance

These are implementation proofs of the derived compatibility targets in
[ModuleLocalHomPullbackStatements](ModuleLocalHomPullbackStatements.md). The
targets record locality and scalar transport for the canonical comparison of
the registered source `stacks-relative-differentials-internal-hom-2026-10-21`,
Section 17.22 ([tag 01CM](https://stacks.math.columbia.edu/tag/01CM)) and
Lemma 17.22.5 ([tag 0C6I](https://stacks.math.columbia.edu/tag/0C6I)). The proof
route through restriction-pullback comparison isomorphisms is internal to this
formalization and is not taken from the source.
