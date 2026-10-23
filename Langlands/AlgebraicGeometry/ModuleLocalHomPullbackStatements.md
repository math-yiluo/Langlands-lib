# Local coherence targets for the internal-Hom pullback

This module states the two compatibility laws needed to assemble the published
`Langlands.Scheme.Modules.localHomPullback` into a morphism of sheaves of
modules. The declarations are proposition-valued definitions, not proofs or
additional assumptions on the construction.

For arbitrary schemes X and Y in universe `u`, a morphism f : X → Y, and
arbitrary module sheaves M and N on Y:

- `LocalHomPullbackRestrictionStatement` says that pulling back the restriction
  of a local morphism h from U to V is equal to restricting its pullback from
  f⁻¹U to f⁻¹V. The restriction maps are the actual `LocalHom.restrict`, and
  the inclusion on inverse images is `(Opens.map f.base).map i`.
- `LocalHomPullbackScalarStatement` says that pulling back r • h, for a section
  r of the structure sheaf on U, gives `(f.app U r)` times the pullback of h.
  Thus the scalar is transported by the scheme morphism's actual map on
  structure-sheaf sections.
- `LocalHomPullbackSheafLawsStatement` is the conjunction of these two
  universally quantified laws, with no further hypotheses.

The underlying local operation is defined in
[ModuleLocalHomPullback](ModuleLocalHomPullback.md) by applying the actual
restricted pullback functor to a morphism of restricted module sheaves and
conjugating by `restrictPullbackNatIso`. These targets concern that fixed
construction. They do not replace it with a map supplied as data.

Together with the already proved zero and addition laws, these two targets
express precisely the naturality and linearity needed for the sectionwise
assignment to define

```
internalHom M N → (Scheme.Modules.pushforward f).obj
  (internalHom ((Scheme.Modules.pullback f).obj M)
    ((Scheme.Modules.pullback f).obj N)).
```

This file does not construct that global morphism or its adjunction mate, and
does not assert identity or composition coherence or an isomorphism.

## Provenance

These are derived compatibility targets for the canonical comparison displayed
in the registered source `stacks-relative-differentials-internal-hom-2026-10-21`,
*Stacks Project — Relative differentials and internal Hom (HTML snapshot
2026-10-21)*, folder SHA256
`9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`.
The opening of `01CM.html`, Section 17.22
([tag 01CM](https://stacks.math.columbia.edu/tag/01CM)), defines internal-Hom
sections by local module morphisms and describes their scalar multiplication.
Lemma 17.22.5 ([tag 0C6I](https://stacks.math.columbia.edu/tag/0C6I)) displays the
canonical pullback comparison. Restriction compatibility expresses locality of
pullback of those morphisms; scalar compatibility expresses transport of
multiplication by a function through pullback. These implementation-level
identities are derived from that construction, rather than quoted as separate
source lemmas. The source's finite-presentation and flatness hypotheses concern
invertibility of the comparison; no invertibility claim is made here.
