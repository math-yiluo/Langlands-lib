# Logarithmic coordinates of actual positive split tori

This derived construction compares the actual adelic logarithmic character map
with the positive scalar subgroup of a commutative group scheme `T` over a
number field `F`, supplied with an actual isomorphism
`e : T.toGrp ≅ splitTorus (Spec F) I` and a finite type `I`. No nonempty-rank
assumption is made. All points, characters and topologies are the existing
scheme-point constructions.

`characterNorm_eq_absoluteValue_characterValue` and
`characterLog_eq_log_characterValue` identify the general actual-character API
with torus character evaluation.
`characterCoordinates` identifies the actual character group with `I → ℤ`
through the supplied splitting. Its inverse is composition of an actual
split-torus character with `e.hom`. The coordinate-character and finite-sum
lemmas prove that these are the genuine coordinate characters and that every
character is their integer linear combination.

`dualCoordinatesContinuousEquiv` is the continuous real-linear equivalence
between `RealCharacterDual F T.toGrp` and `I → ℝ` obtained by evaluation at those
coordinate characters. Its inverse sends `v` to the functional
`χ ↦ ∑ i, exponentᵢ(χ) * vᵢ`. The character expansion proves one inverse law;
the coordinate-character exponent formula proves the other. Coordinate
evaluation and finite sums prove continuity in the existing pointwise topology.

Let `d = [F : ℚ]`. The equal positive scalar at every infinite place, with
finite components one, has normalized global norm equal to its `d`-th power.
Consequently `characterLog_full` and `characterLog_full_eq_sum` prove

```
characterLog(full x)(χ) = d * ∑ i, exponentᵢ(χ) * log(xᵢ).
```

The proof applies the actual scalar norm formula, logarithm of a finite product
and logarithm of integer powers. In particular, each coordinate character gives
`d * log(xᵢ)`; the degree factor is retained throughout.

`expUnit` constructs the positive unit with value `exp r` and inverse
`exp (-r)`. Its log identities and continuity include both unit coordinates.
`degree_pos` proves `d > 0`. Thus `logParameters ℓ` has coordinates
`exp(ℓ(coordinateCharacter i) / d)`. The two inverse identities follow from the
coordinate log formula, positivity of `d`, the scalar exponential/log identities
and injectivity of the finite dual coordinates.

`positiveExp` sends those parameters into the actual intrinsic positive subgroup,
using its proved equality with the coordinate image. `positiveLogEquiv` is the
topological group isomorphism from that intrinsic subgroup to
`Multiplicative (RealCharacterDual F T.toGrp)`. Its forward map is exactly the
restriction of the existing normalized character log, with addition in the dual
written multiplicatively. Its inverse is `positiveExp`. The group law comes
from the general character-log multiplication identity; continuity comes from
the existing adelic log and scalar embedding and the explicit inverse parameters.
Empty `I` gives the corresponding trivial groups without a separate exception.

The source motivation is Mœglin–Waldspurger, *Spectral Decomposition and
Eisenstein Series* (1995), I.1.4, printed pp.5–7, especially equation (4) on p.7,
and the equal-archimedean positive scalar embedding in I.2.1, printed pp.18–19.
The finite-coordinate adapters and explicit degree-normalized inverse are
internal constructions implementing the split-torus case of those conventions.
The source's general reductive surjectivity argument also needs the restriction
of characters to a maximal split central torus and its finite-index property.
Those structural comparisons, general reductive surjectivity, Iwasawa heights,
reduction coverage and finite volume remain separate obligations.
