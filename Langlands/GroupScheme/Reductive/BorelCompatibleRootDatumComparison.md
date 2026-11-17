# Root-datum comparison for supplied Borel chambers

Over an arbitrary field `k`, let `G` and `H` be connected reductive group
schemes with specified split maximal tori `i : T → G` and `j : T′ → H`.
Let `P` and `Q` be the supplied root data on their actual character and
cocharacter lattices, with finite root-index types, and let `b` and `c`
be bases. Suppose actual isomorphisms `f : G ≅ H` and `t : T ≅ T′`
satisfy `i ≫ f.hom = groupHom t.hom ≫ j`.

Choose regular cocharacters `ν` of `T` and `ν′` of `T′` whose strictly
positive pairings detect exactly `b.IsPos` and `c.IsPos`, respectively.
Assume the full subgroup-functor equality

```
(Dynamic.parabolic (groupHom ν ≫ i)).comap f.inv =
  Dynamic.parabolic (groupHom ν′ ≫ j).
```

`BorelCompatibleRootDatumComparison b c t` records a full contravariant
root-datum equivalence `e : Q ≃ P`, preservation of positive roots,
`e.indexEquiv a ∈ b.support ↔ a ∈ c.support`, and the exact actual-map
formulas

```
e.weightMap χ = t.hom ≫ χ
e.coweightMap μ = μ ≫ t.hom.
```

`borelCompatibleRootDatumComparison` constructs these data from precisely
the hypotheses above. The equivalence is the existing chosen
`rootDatumEquivOfTorusCompatibleIso`, so its character and cocharacter
maps come from the supplied torus isomorphism. No algebraic closure,
positive-rank assumption or canonical choice of root labels is required.

`positive_iff_of_torusCompatibleIso` is the corresponding positivity
theorem. It does not need the finite root-index instances. Transport `ν`
to `ν ≫ t.hom` on `T′`. Pullback of each actual target root is the
corresponding source root, and composition preserves the lattice pairing.
Consequently the transported cocharacter is regular. Dynamic functoriality
carries its ambient parabolic through `f`; the assumed equality therefore
identifies this parabolic with that of `ν′`. The published theorem
`regularCocharacterBorel` characterizes equality of regular dynamic
parabolics by equality of all strict root signs. This gives the claimed
positivity equivalence after the two sign-adaptation formulas are applied.

The general auxiliary theorem
`RootPairing.Base.mem_support_equiv_iff_of_positive` concerns two finite
root data and two supplied bases. A full root-datum equivalence preserving
positivity preserves their simple-root supports: express simple roots as
positive roots that cannot be sums of two positive roots, then use the
linear root transport in both directions. The proof uses the existing
`mem_support_iff_positive_indecomposable` characterization.
`simple_iff_of_torusCompatibleIso` applies this auxiliary theorem to the
actual field comparison. The constructor packages these two theorems and
the existing exact lattice-map formulas.

This is a derived construction from the published actual torus-compatible
root-datum comparison, the regular-cocharacter Borel sign criterion,
dynamic functoriality, and positive-root indecomposability. The preceding
paragraphs describe the implemented proof; there is no new external-source
translation. This unit is a field comparison with supplied regular
cocharacters and parabolic equality. It does not construct open overlap
comparisons over arbitrary bases, a relative Borel atlas, effective descent,
or the final finite etale Weil presentation.
