# Relative-root restrictions in type E₆ with marked short arm and unmarked centre

Module: `Langlands.LinearAlgebra.CartanE6NodeMarking`, namespace
`Langlands.CartanE6Root.NodeMarking`.

The vertices are numbered as in Mathlib's `CartanMatrix.E 6`: the edges are `0–2`, `1–3`,
`2–3`, `3–4`, `4–5`, so vertex `i` is Bourbaki's `α_{i+1}`. Vertex `1` is the end of the
short arm, vertex `3` is the central (branch) vertex, `2` and `4` are the inner long-arm
vertices and `0` and `5` are the long-arm endpoints. The only nontrivial automorphism of
the diagram exchanges `0 ↔ 5` and `2 ↔ 4`.

## The markings

A `NodeMarking` describes a set of marked vertices that contains `1`, does not contain `3`,
and is stable under the exchange of the two long arms. It has three flags:

- `swapsArms`: whether the star action may exchange the two long arms;
- `endsMarked`: whether `0` and `5` are marked;
- `innerArmMarked`: whether `2` and `4` are marked.

`active p` lists the chosen representatives of the marked star orbits: vertex `1` always,
`0` and `2` when they are marked, and `5` and `4` when they are marked and the arms are not
exchanged. `project p c` restricts integral coordinates `c` (in the simple-root basis) to
the marked orbits: it discards the unmarked coordinates and, when the arms are exchanged,
adds the coordinate of `5` to that of `0` and the coordinate of `4` to that of `2`.
`IsProjectedRoot p c` says that `c` is the projection of a positive or negative root of
`E₆`, using the 36 positive roots `positiveCoefficients` of
[`LinearAlgebra.CartanE6RootCoordinates`](CartanE6RootCoordinates.md). Zero is a projected
root, because the simple root `α₄` (vertex `3`) projects to zero.

## The reflection condition

`HasIntegralReflections p` is the integrality and closure property that a crystallographic
root system imposes on the projected roots. For every active coordinate `i` and every
positive integer `m` with `m • unit i` a projected root, there is an integral vector `f`
with `m * f i = 2` such that, for every projected root `c`, the reflected vector
`c - (m * ∑ j, c j * f j) • unit i` is again a projected root. The module
[`Rational.TypeE6NodeMarkingFromRoots`](../GroupScheme/Rational/TypeE6NodeMarkingFromRoots.md)
derives this condition for the marking of an actual Tits index from the Library's relative
root system.

## The theorem

```lean
theorem eq_of_hasIntegralReflections (p : NodeMarking) (h : p.HasIntegralReflections) :
    p.innerArmMarked = false ∧ (p.endsMarked = true → p.swapsArms = true)
```

So only the markings `{1}`, with either star action, and `{0, 1, 5}`, with the arms
exchanged, satisfy the reflection condition.

## Proof

Each of the five excluded markings has a test made of a pivot coordinate `i`, an upper
bound for each other active coordinate `j`, and a witness root. The test is used with
`m = 1`: the simple root at `i` projects to `unit i`.

- The pivot fixes `f`. For each other active `j`, the projected roots of the form
  `unit j + x • unit i` have `x` between `0` and the stated upper bound, and both ends occur.
  The reflection maps this fibre to itself and reverses it, so `f j` equals minus the upper
  bound. Together with `f i = 2` this determines the reflection on the projected roots.
- The witness is a projected root whose reflection is not a projected root.

| marking (`swapsArms`, `endsMarked`, `innerArmMarked`) | marked vertices | pivot | upper bounds at `0,…,5` | witness |
| --- | --- | --- | --- | --- |
| (false, false, true) | `1, 2, 4` | `1` | `(0,0,1,0,1,0)` | `(0,0,1,0,1,0)` |
| (false, true, false) | `0, 1, 5` | `0` | `(0,1,0,0,0,1)` | `(0,-1,0,0,0,-1)` |
| (false, true, true) | `0, 1, 2, 4, 5` | `1` | `(0,0,1,0,1,0)` | `(0,0,1,0,1,0)` |
| (true, false, true) | `1, 2, 4` | `1` | `(0,0,1,0,0,0)` | `(0,0,2,0,0,0)` |
| (true, true, true) | `0, 1, 2, 4, 5` | `1` | `(0,0,1,0,0,0)` | `(0,0,-2,0,0,0)` |

The validity of each test is a finite check over the 72 signed projected roots, made by
`decide` in `validTest_of_bad`. `not_validTest_of_hasIntegralReflections` turns a valid test
into a contradiction with `HasIntegralReflections`: the fibre bounds force `f` at every
active coordinate, and the reflection of the witness, computed with the forced values, would
be a projected root. Coordinates of `f` at inactive vertices do not matter, because
projected roots vanish there.

## Source

The markings are those of the isotropic Tits indices of type `E₆` with the short-arm vertex
`α₂` distinguished and the branch vertex `α₄` not distinguished. Platonov and Rapinchuk,
*Algebraic Groups and Number Theory* (1994), registered as
`platonov-rapinchuk-1994-algebraic-groups-number-theory`, §6.8, list the outer indices in
(6.53), printed p. 379, and the inner isotropic indices in (6.57), printed p. 382, following
Tits. The surviving markings are `{α₂}` for (6.53)(a) and `{α₁, α₂, α₆}` for (6.53)(c).
The inner index with only `α₂` marked does not occur in (6.57), but the reflection
condition alone does not exclude it. The calculation here is an internal finite check
(provenance: internal) and uses no index admissibility from the source.
