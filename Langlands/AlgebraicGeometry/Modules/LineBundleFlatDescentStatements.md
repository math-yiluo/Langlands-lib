# Faithfully flat descent of line bundles: statements

This module states two propositions about actual sheaves of modules on schemes
(`Scheme.Modules`) and line bundles in the sense of
`Langlands.AlgebraicGeometry.Picard.IsLocallyFreeRankOne`. Descent data are
written in the equal-composite form used by the published
`Langlands.Scheme.Modules.TrivialIsoDescentStatement`: they are indexed by every
scheme `U` and every pair `a b : U ⟶ X` with `a ≫ p = b ≫ p`, and compared by
the canonical isomorphisms `equalCompositeIso p a b h M : a^*(p^*M) ≅ b^*(p^*M)`
of `Langlands.AlgebraicGeometry.Modules.EqualCompositePullback`.

## Descent of isomorphisms

`Langlands.Scheme.Modules.LineBundleIsoDescentStatement`: let `p : X ⟶ Y` be
quasi-compact, flat and surjective, and let `M` and `N` be locally free modules
of rank one on `Y`. Let `e : p^*M ≅ p^*N` be an isomorphism whose forward map
intertwines the canonical comparisons, that is

`a^*(e.hom) ≫ (equalCompositeIso p a b h N).hom = (equalCompositeIso p a b h M).hom ≫ b^*(e.hom)`

for every scheme `U` and all `a b : U ⟶ X` with `h : a ≫ p = b ≫ p`. Then
there is a unique isomorphism `e₀ : M ≅ N` whose pullback
`(Scheme.Modules.pullback p).mapIso e₀` equals `e`. This generalizes the
published `TrivialIsoDescentStatement`, which assumes global trivializations of
`M` and `N`, to arbitrary line bundles.

## Effectivity of descent data

`Langlands.Scheme.Modules.LineBundleDescentEffectiveStatement`: let
`p : X ⟶ Y` be affine (`IsAffineHom`), flat and surjective, and let `F` be a
locally free module of rank one on `X`. Suppose given isomorphisms
`θ U a b h : a^*F ≅ b^*F` for every scheme `U` and all `a b : U ⟶ X` with
`h : a ≫ p = b ≫ p`, such that

* (naturality) for every `k : V ⟶ U`, the isomorphism `θ V (k ≫ a) (k ≫ b)`
  is the pullback of `θ U a b` along `k`, conjugated by the canonical
  composition isomorphisms `pullbackComp k a` and `pullbackComp k b`;
* (cocycle) `θ U a b ≫ θ U b c = θ U a c` whenever `a ≫ p = b ≫ p = c ≫ p`.

Then there exist a locally free module `M` of rank one on `Y` and an
isomorphism `p^*M ≅ F`. Only existence of some isomorphism is asserted; the
statement does not claim that the isomorphism can be chosen compatible with
`θ`, nor uniqueness of `M`.

Equivalently, `θ` is a descent datum in the usual sense: naturality shows that
`θ` is determined by its value on the two projections `X ×_Y X ⇉ X`, and the
cocycle law on the three projections from `X ×_Y X ×_Y X` is the usual cocycle
condition. Taking `a = b = c` shows `θ U a a` is the identity.

## Provenance

Internal interface statements for the proof of the Library statement
`Langlands.AlgebraicGeometry.Picard.RigidifiedFppfComparisonStatement`. A
quasi-compact flat surjection `p` gives the fpqc covering `{p}` of `Y`. The
first proposition is the full faithfulness part, and the second the
effectivity part, of fpqc descent of quasi-coherent sheaves (Stacks Project,
Descent, Proposition 35.5.2, Tag 023T), restricted to line bundles. That the
descended module is again locally free of rank one is Stacks Project, Descent,
Lemma 35.7.6, Tag 05B2 (finite local freeness descends along fpqc coverings);
the rank is one because `p` is surjective and pullback preserves rank. The
second statement assumes `p` affine, which is the case needed later (base
changes of `Spec R' ⟶ Spec R`).
