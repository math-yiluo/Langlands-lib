# The canonical pullback square of a subring and a contained ideal

`Langlands.Algebra.SubringIdealQuotientPullbackStatement.{u}` is a
Prop-valued definition in module
`Langlands.Algebra.SubringIdealQuotientPullbackStatement`.
It states that for every commutative ring `B : Type u`, every subring
`R : Subring B`, and every ideal `I : Ideal B` with
`(I : Set B) ⊆ (R : Set B)`, the canonical square

```text
R ------------------------> B
|                           |
|                           |
v                           v
R / (I.comap R.subtype) ---> B / I
```

is a pullback in `CommRingCat.{u}`. The containment is the only additional
premise. The statement includes nonreduced rings and the zero ring, and
has no normality, integrality, noetherianity, finiteness, reducedness,
field, flatness, or nilpotence assumption.

The top arrow is the actual inclusion `R.subtype`. The left arrow is
`Ideal.Quotient.mk (I.comap R.subtype)`, and the right arrow is
`Ideal.Quotient.mk I`. The bottom arrow is the induced homomorphism
`Ideal.quotientMap (I := I.comap R.subtype) I R.subtype le_rfl`.
Its well-definedness uses reflexivity of the contracted-ideal containment.
Each homomorphism is made a categorical morphism with `CommRingCat.ofHom`.
The `IsPullback` arguments are, in order, the top, left, right, and bottom
arrows.

Here `I.comap R.subtype` is the ideal of elements of `R` whose images in
`B` belong to `I`, conventionally denoted `I ∩ R`. Thus the proposition
expresses the canonical ring identity
`R ≅ B ×_(B/I) (R/(I ∩ R))`, with its specified projections and
categorical universal property. This contribution states that proposition;
it does not supply its proof.

The provenance is **derived** from Faltings–Chai, *Degeneration of Abelian
Varieties* (1990), Chapter I, proof of Theorem 1.9, final paragraph,
printed p.7/PDF p.19. In that passage, `B` is the normalization of `R`
and `I` is the conductor, an ideal of `B` contained in `R`. The authors
identify `R` as the fibre product of `B` and `R/I` over `B/I`.
The present statement isolates the elementary algebraic hypotheses of
that identity and generalizes the normalization/conductor example to an
arbitrary commutative ambient ring, subring, and contained ambient ideal.
The contraction above makes the source's quotient `R/I` precise without
introducing a new ring or conductor definition.

The registered source is
`provided-0ecad2ee7ec463aef945e9d85a6d369dd775bbbbbd4e55843b9bfb4aa819da7d`,
file `literature/Faltings-Chai - Degeneration of Abelian Varieties (1990).pdf`,
SHA-256
`f53b164d7d783ca55a5b6ae6b0885601264f13f2a2660a1d689813715899f20e`.
Printed p.7/PDF p.19 was read and checked visually for this contribution.

This ring statement supplies no global scheme pushout, preservation of
affine neighborhoods of finite sets, noetherian induction, or Picard
representability result. Those steps of the surrounding source argument
remain separate obligations.

Worker 1764 prepared this contribution using the formulation supplied by
Worker 139, who is credited as a coauthor.
