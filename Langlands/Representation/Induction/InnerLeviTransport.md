# Inner transport of whole-Levi data

Author: Worker 178.

This derived construction implements inner changes of coordinates on an actual
product Levi. It supplies representation equivalences, real-character
compatibility, analytic temperedness transport, normalized-induction transport,
and the ambient embedding formula needed after a matrix standardizer has been
constructed. It imposes no irreducibility, strict-chamber, positive-rank, or
multiple-block assumption.

## Generic inner pullback

For a commutative ring `R`, a group `G`, an `R`-module `V`, a representation
`ρ : Representation R G V`, and `g : G`, `Langlands.innerPullbackEquiv ρ g`
is an actual equivalence

```
(ρ.comp (MulAut.conj g).symm.toMonoidHom) ≃ ρ.
```

The source acts by `h ↦ ρ(g⁻¹ h g)`. The underlying linear map sends `v` to
`ρ(g)v`, as recorded by `innerPullbackEquiv_apply`; the inverse sends `v` to
`ρ(g⁻¹)v`. The two inverse identities use the homomorphism law and cancellation.
The intertwining identity is `ρ(g)ρ(g⁻¹ h g) = ρ(h)ρ(g)`.

`character_comp_inner_symm` proves that every character `χ : G →* Rˣ` is
unchanged by this pullback. Its proof expands the image of `g⁻¹ h g` and
cancels in the commutative unit group. `twist_comp_inner_symm` then identifies
the twist of the pulled-back representation with the pullback of the twist,
using that character equality pointwise. The universes of `R`, `G`, and `V`
are independent.

## Actual p-adic Levi coordinates

Fix `F : PadicField.{uF} p`, `T : F.TopologicalData`, and an ordered block
shape `B`. All topologies here are induced by `T.topology`.

`T.innerLeviEquiv B m` is the continuous multiplicative equivalence of
`B.Levi F.Carrier` given by `x ↦ m * x * m⁻¹`. Its inverse is
`x ↦ m⁻¹ * x * m`. The `_apply` and `_symm_apply` lemmas give these formulas.
Continuity of both directions follows from multiplication by fixed elements
in the actual Levi topological group.

`leviRealPowerCharacter_comp_innerLeviEquiv` proves that pullback along its
inverse preserves `T.leviRealPowerCharacter B t` for every real vector `t`.
It applies the generic character result, so there is no restriction on the
central direction or on the exponents.

`isLeviTempered_iff_of_equiv` transports
`RelativeRegularComparison.IsLeviTempered T B` across an actual representation
equivalence, allowing two independent carrier universes `uV` and `uW`.
For each measurable and Borel structure and each Haar measure on the actual
quotient of the Levi by its center, it applies the published
`isTemperedModCenter_of_equiv` in each direction. Thus the exact analytic
predicate, including admissibility, unitary central character, and all
`L^(2+ε)` coefficient conditions, is preserved.
`isLeviTempered_inner_iff` specializes this to `innerPullbackEquiv`.

`innerLeviEquiv_embedding_of_standardizer` concerns an actual conjugate block
pair `P`, an ambient matrix `y`, and `m : P.shape.Levi F.Carrier` satisfying

```
y * P.conjugator = P.shape.leviEmbedding F.Carrier m.
```

It proves, for every `x`, the exact identity

```
P.shape.leviEmbedding F.Carrier (T.innerLeviEquiv P.shape m x)
  = y * P.leviEmbedding x * y⁻¹.
```

The proof expands the conjugate embedding, uses the homomorphism laws of the
standard embedding, substitutes the matrix equality, and cancels group
factors. The existence of `y` or `m` is not assumed elsewhere or asserted here.

## Twists and normalized induction

`T.innerLeviTwistEquiv B m t σ` applies the published `twistEquiv` to the
inner pullback equivalence and the common real determinant character. Its
source is the real twist of the inverse-inner pullback of `σ`, and its target
is the real twist of `σ`. The generic twist compatibility above also identifies
the source as the inverse-inner pullback of the twisted representation.

`T.innerLeviInducedEquiv B m t σ` applies the published
`T.normalizedParabolicInducedEquiv` to that twisted equivalence. It is an
actual equivalence between the two normalized inductions, with the published
right-translation action and positive half-modulus normalization. It acts by
postcomposition with the Levi intertwiner. The field and representation
carrier universes remain independent; the induced function spaces use their
usual maximum universe.

## Provenance and scope

These are elementary derived constructions from the imported Library modules
`Induction/Equivalences`, `Induction/ConjugateParabolic`, and
`Classification/RelativeRegularComparisonStatement`, and their representation,
twist, and temperedness dependencies. The proof of analytic transport reuses
the published coefficient transport theorem; no analytic integration theorem
is added. No external literature proposition is claimed verbatim.

This module does not prove existence of a semistandard matrix standardizer,
normalizer decomposition, parabolic conjugacy, exponent faithfulness, or
Langlands data uniqueness. It provides the inner-coordinate transport step
once the relevant matrix equality has been established. In particular, it is
a supporting construction for the semistandard Langlands proof, not a proof
of `GLSemistandardLanglandsConjugacyStatement`.
