# Admissible singleton types in an actual affine chamber

This is an internal deduction from the existing affine-root-system and restricted
Tits-building definitions and the proved affine wall comparison and generation
theorems. It introduces no external mathematical assertion. The vector space and
affine torsor retain independent universes `uV` and `uA`. All root-system hypotheses
are those of `IsAffineRootSystemWithRankZero`, including corrected AR4.

For distinct affine functionals `ψ` and `η` with equal derivatives, and any vectors
`v`, `w` satisfying `ψ.linear v = 2` and `η.linear w = 2`,
`affineReflection_mul_ne_of_linear_eq` proves that their actual affine reflections
do not commute. There is no assumption that these vectors have already been
identified. Equal derivatives give

```
ψ(rη x) = ψ(x) - 2η(x),     η(rψ x) = η(x) - 2ψ(x).
```

Applying `ψ` to a supposed commutation equality gives
`-ψ(x) + 2η(x) = 3ψ(x) - 2η(x)` for every `x`. Thus the two
functionals are equal, contradicting their distinctness.

Under `hΨ : IsAffineRootSystemWithRankZero Ψ`, corrected AR4 says that the fiber
of the derivative of each root is infinite. Removing that root leaves another
root `η` with the same derivative.
`exists_distinct_parallel_root` records this fact. AR2 supplies a coroot `w` for
`η`, so `exists_noncommuting_parallel_reflection` supplies an element `t` of the
original `affineWeylGroup Ψ`. Its conclusion retains both noncommutation with
the original reflection of `ψ` and witnesses that `t` is the reflection of
`η`: membership `η ∈ Ψ`, equality of the derivatives, distinctness `η ≠ ψ`,
the coroot `w` and equality of `t` with its affine reflection.
`noncommutingParallelReflection` chooses from this strengthened existential.
Its subtype retains all these properties of the chosen value, so the choice
itself is certified to be an actual distinct parallel root reflection.

`closure_chamberSimpleReflections` specializes the proved geometric wall
comparison and the proved wall-generation theorem to any supplied chamber `C`.
It proves that the actual set `chamberSimpleReflections Ψ C` generates the
affine Weyl group. These are the literal geometric simple reflections already
defined from positive indivisible roots and chamber faces.

`exists_noncommuting_chamberSimpleReflection` proves that each such simple
reflection `s` has another simple reflection `t` with `s*t ≠ t*s`.
If every simple reflection commuted with `s`, the subgroup centralizing `s`
would contain their generated subgroup, hence the entire affine Weyl group.
This contradicts `noncommutingParallelReflection` for the root defining `s`.

Finally, `isAdmissibleType_singleton_chamberSimpleReflections` proves
`IsAdmissibleType (chamberSimpleReflections Ψ C) {s}` for each simple `s`.
For a different simple `r`, `r` itself is in its own component and outside `{s}`.
For `s`, its noncommuting simple neighbor supplies the required element of its
component outside `{s}`. The component is exactly the existing reflexive
transitive closure of noncommutation; no alternative Coxeter convention is used.

These results include rank zero: an empty root system has no simple reflections,
so the quantified conclusions about them are vacuous. They do not assert that an
arbitrary restricted Tits system has admissible singleton types. They also do not
construct valuation data, a realization, galleries, or the five witnesses of
`RootValuationBuildingConstructionStatement`. They discharge the affine
singleton-admissibility prerequisite for a later gallery argument once its Tits
simple set is identified with these actual geometric reflections.
