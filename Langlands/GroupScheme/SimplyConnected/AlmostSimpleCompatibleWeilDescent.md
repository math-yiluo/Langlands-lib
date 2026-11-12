# Descent of a compatible actual Weil-product comparison

Worker 166. This is internal supporting content for the simply connected
almost-simple Weil-restriction theorem. It combines the published actual
stabilizer-field factor, the independently constructed canonical transport
of its embedding product, arbitrary-Galois isomorphism descent, and the
proved separably closed-field almost-simplicity theorem.

Let `L/k` be an arbitrary Galois extension of fields in `Type u`, and let
`D` be a supplied `SimplyConnectedAlmostSimpleProduct` presentation of
the actual scalar extension `G_L`. Assume that `G_L` is smooth and affine,
and that `G` is affine, quasi-compact, quasi-separated and locally of finite
presentation. For a factor index `i`, use exactly the published field
`E = D.factorStabilizerField i` and actual group
`H = (D.factorStabilizerDescent i).1`.

The theorem
`isAbsolutelyAlmostSimple_factorStabilizerDescent_of_isSepClosed`
requires `IsSepClosed L`. The proved
`separablyClosedAlmostSimpleAbsolute` makes `D.factor i` absolutely
almost-simple. The published field-extension reflection and exact
recovery of that factor then make `H` absolutely almost-simple.
No perfectness or characteristic hypothesis is added. Affineness of `H`
is recorded in the original descent data, and its simple connectedness
provides smoothness and hence local finite type.

For the remaining construction assume that `G` is almost-simple and
supply an actual isomorphism

```text
p : (AffineWeil.groupScheme k E H)_L ≅ pi (D.embeddingConjugateFamily i).
```

The additional input `hp` is the exact equality, for every
`k`-automorphism `σ` of `L`,

```text
baseChange(σ).map(p.hom) ≫ (EmbeddingProduct.galoisIso H σ).hom
  = canonicalDescent(AffineWeil.groupScheme k E H, σ).hom ≫ p.hom.
```

This is a condition on the supplied original comparison and the already
published independent product transport. The construction does not
define transport by conjugating `p`.

`weilRestrictionIsoOfCompatibleEmbeddingProduct` composes `p` with
`q = D.embeddingConjugateProductIso hG i`. The published
`embeddingConjugateProductIso_descent` gives compatibility of `q`; together
with `hp` and functoriality, it gives canonical compatibility of
`p.hom ≫ q.hom`. `Descent.GaloisHom.iso` descends this actual isomorphism
from the Weil restriction to `G`, and taking its inverse gives
`G ≅ AffineWeil.groupScheme k E H`.
`weilRestrictionIsoOfCompatibleEmbeddingProduct_baseChange_inv` records
the exact recovery of the inverse as `p.hom ≫ q.hom`.

If `L` is separably closed, the theorem
`exists_weilRestriction_of_compatibleEmbeddingProduct` supplies every
field, group, finiteness, separability, affineness, local finite type,
simple connectedness, absolute almost-simplicity and isomorphism witness
in the structural conclusion, for these supplied `D`, `i`, `p` and `hp`.
It uses the actual stabilizer field and factor without replacing them.

This unit does not construct `p` or prove its compatibility `hp`, and it
does not assert the unconditional
`SimplyConnectedAlmostSimpleWeilRestrictionStatement`. Those remain
obligations of the host proof. All results here are internal compositions
of published constructions and proofs; no new literature assertion or
unproved structural premise is introduced.
