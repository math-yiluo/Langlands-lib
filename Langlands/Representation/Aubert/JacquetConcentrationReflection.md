# Reflecting actual Jacquet concentration

This internal adapter connects actual normalized Jacquet concentration to
concentration of the unchanged actual cut complex and then to common-sign
Aubert effectivity. It preserves the supplied p-adic topology, arbitrary prime,
independent universes, actual degree carriers, and the existing signed
differentials.

## The explicit Jacquet conditions

`JacquetConcentratedAt F T P A m` is a proposition about the actual normalized
Jacquet functors at shapes `C` satisfying `P C`. It requires:

- injectivity of the degree-zero Jacquet differential when `0 < m`;
- equality of the incoming range and outgoing kernel at degree `i + 1` when
  `i + 1 < m`;
- zero actual Jacquet degree carriers at every degree `k > m`.

The maps are `normalizedJacquetMap` applied to the existing `degreeMorphism`,
whose underlying intertwiner is the existing signed cut differential. The last
condition is subsingleton of the actual unipotent coinvariant carrier. No
surjectivity onto degree `m` or vanishing of its terminal quotient is required.
For `m = 0` the first two conditions are empty.

## Reflection to the actual complex

`concentratedAt_of_jacquet` assumes that the chosen family detects every nonzero
actual subquotient of every degree. The published Jacquet injectivity-reflection
theorem gives injectivity of the initial actual differential. The actual
square-zero identity and Jacquet middle-exactness reflection give equality of
range and kernel below the surviving degree. Finally, each degree is an actual
subquotient of itself, through the identity intertwiner; the detecting-family
zero criterion reflects zero Jacquet carriers into zero actual degree carriers.
These are precisely the three clauses of `ActualCutComplex.ConcentratedAt`.
The theorem does not need a finite-length assumption of its own.

`concentratedAt_of_associatedJacquet` uses the proved all-degree detector from
`QuasicuspidalCutSupport.degreesDetected`. At positive rank, for a finite-length
quasicuspidal inducing object `σ` of shape `B` and a finite-length actual
subquotient `π` of its normalized induction, Jacquet concentration over the
family `LevisAssociated B` therefore implies actual cut concentration.
Neither object is required to be irreducible.

## The common support sign

`effective_of_associatedJacquet` specializes the surviving degree to
`m = B.length - 1`. Positive rank gives `0 < B.length`, hence
`m + 1 = B.length`; the existing bound `B.length ≤ n` permits the actual terminal
Euler identity. The proved terminal-effectivity adapter then makes

```
(-1)^(n - B.length) • alternatingOperator [π]
```

coordinatewise nonnegative under the existing composition-factor map to the
lattice of actual irreducible isomorphism classes. It does not assume or prove
irreducibility or nonvanishing of the terminal quotient. The exact Grothendieck
group continues to retain every actual short exact relation.

## Provenance and remaining obligation

The content is an internal specialization of the published actual detecting-family
reflection results, the actual cut differential's square-zero identity, the
proved quasicuspidal cut-degree detector, and the actual terminal Euler calculation.
It introduces no source assertion or classification input. The actual Jacquet
concentration proposition remains an explicit hypothesis: this module does not
prove the filtered graded-map comparison needed to establish it and does not
prove the unconditional `SignedEffectivityStatement`. Rank-zero effectivity is
already available separately in `CutTerminalEffectivity`.
