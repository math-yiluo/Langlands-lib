# Additive images and ambient smooth real homomorphisms

This is an internal supporting construction by Worker 1374 for ambient
smooth real homomorphisms. It uses the published actual vector-group,
canonical point-topology and compact-image interfaces; no new literature
assertion is introduced.

For a nonarchimedean local field `F : Type u`, an affine group scheme `G`
over `Spec F`, any natural number `n`, and any actual group-scheme morphism

```lean
i : VectorGroup.groupScheme (CommRingCat.of F) n ⟶ G
```

let `f : rationalPoints G →* Multiplicative ℝ` have open kernel in
`rationalPointTopology F G.X`. The selected definition
`vectorImageToOpenRealKernel n i f hf` is the homomorphism
from the actual rational points of the vector group to `f.ker`
whose underlying ambient value at `x` is `rationalPoints.map i x`.
Its coercion lemma records this equality. The supporting theorem
`vectorImage_eq_one` proves `f (rationalPoints.map i x) = 1` for every
actual rational vector-group point.

Here `Multiplicative ℝ` denotes the additive real group, and likewise
the additive field is written `Multiplicative F`. No continuity hypothesis
on `f` beyond the stated openness of its kernel is assumed. The ambient
group need not be connected, reductive or locally of finite type. The
field universe is arbitrary and both field characteristics are included.

The proof first establishes `additiveReal_eq_one`. For a fixed `x` in
the additive field, the continuous additive map from the compact integer
ring `𝒪[F]` sends `z` to `x * z` in the underlying field. The pullback of
the kernel is open. The published
`Langlands.Weil.finite_range_of_open_kernel` gives finite image, so the
image of `1` has finite order. The additive real group is torsion free,
and that image equals `f x`. The lemma `vectorReal_eq_one` applies the
field result to the continuous additive line `z ↦ (j ↦ z * x j)` through
each point of a product of copies of `F`. Its index type has an independent
universe and need not be finite.

The algebraic equivalence `VectorCoordinates.rationalCoordinates R n`
identifies the actual rational points of the standard vector group over
any commutative ring `R` with `Multiplicative (Fin n → R)`. It composes
the existing all-test `VectorGroup.coordinates` with the canonical
isomorphism `Γ(Spec R, ⊤) ≅ R` in every coordinate. Its apply lemma gives
the value as pullback of the actual global coordinate section.
`polynomialPoint_apply_X` identifies these coordinates with evaluation
of the variables under the actual polynomial algebra point map, using
naturality of `Scheme.ΓSpecIso`.

For a topological commutative ring, the definition
`VectorCoordinates.rationalCoordinatesHomeomorph R n` equips exactly this
equivalence with continuity in both directions, using the canonical
`rationalPointTopology R _`. In the forward direction each coordinate
is evaluation of a polynomial variable. In the inverse direction a tuple
gives its polynomial evaluation algebra map; evaluation at each fixed
polynomial is continuous by `MvPolynomial.continuous_eval`. The existing
spectrum and rational-point homeomorphisms transfer this continuity to
actual scheme points.

The theorem `vectorGroupReal_eq_one` uses this homeomorphism and
`vectorReal_eq_one`. Finally, continuity of the actual point map induced
by `i` pulls the ambient open kernel back to the vector group.
`vectorImageToOpenRealKernel` restricts the codomain of that point map
using the resulting annihilation theorem.

These declarations do not assert a factorization of arbitrary rational
points through tori and additive images, or annihilation of all algebraic
derived points. Those remain separate obligations for the ambient
derived-point theorem.
