# Lower ramification filtrations: level changes, depth functions and action quotients

Module `Nyll.ValuedFieldTheory.Ramification.GaloisValuation.Ramification`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file continues the group theory of a decreasing filtration `G_0 ⊇ G_1 ⊇ …` by normal subgroups (`AntitoneNormalSubgroupFiltration`). It compares the quotients `G/G_n` at different levels, and gives two ways of producing such a filtration: from a depth function on `G`, and from an action of `G` tested on one element against a filtration by "principal units".

## Filtrations

- `herbrandStep i` is `|G_i| / |G_0|` in `ℚ`, and `herbrandFunctionNat n` is the sum of the steps for `i < n`; it is monotone, and a step is positive when `G_i` and `G_0` are finite.
- `quotientMapOfLe`: the projection `G/G_n → G/G_m` for `m ≤ n`. It is surjective and compatible with composition, and its kernel `quotientKernelOfLe` is the image of `G_m`, a normal subgroup; `levelSubgroupToQuotient` (the map `G_m → G/G_n`) has kernel `G_n` and this image as range.
- Isomorphisms: `G_m/G_n` with that kernel (`subquotientEquivQuotientKernelOfLe`), and likewise for the graded pieces and for `G_0/G_1`; `(G/G_n)/(G_m/G_n) ≃ G/G_m`; `(G_l/G_n)/(G_m/G_n) ≃ G_l/G_m` for `l ≤ m ≤ n`, with finite-level versions for `G_n/G_(n+1)` and `G_0/G_1`. For finite `G` the last three have cardinality forms.

## Depth functions

`LowerRamificationDepth G` is a map `depth : G → WithTop ℕ` with `depth 1 = ⊤` whose sets `{depth ≥ n}` are closed under products, inverses and conjugation. `toLowerRamificationFiltration` makes these sets a filtration.

## Action-defined filtrations

`ValuationActionRamification G K` consists of a filtration `U^n` of a group `K` by subgroups, an action `G →* MulAut K` and a probe element `π ∈ K`. Then `lowerRamificationGroup n` is `{σ | σ(π)/π ∈ U^n}`, packaged by `toLowerRamificationFiltration`. The file restates for it the inertia and wild inertia subgroups, the tame quotient, and every quotient criterion above as a condition on the action quotient `σ(π)/π`.

## Watch for

- In both structures the subgroup properties are fields of the structure, so they are assumed by whoever builds an instance. The file builds no instance from a valued field: the header says concrete valued extensions are to supply these estimates.
- The action-defined groups are the library's own notion. The docstrings say the probe is meant to be a uniformizer, but the file does not compare these groups with the classical ones defined through `v(σx − x)`.
- `tameCharacterOfUniformizer` is only the projection `G_0 → G_0/G_1`, with kernel the wild inertia. It does not map into the units of a residue field.
- `herbrandStep` and `herbrandFunctionNat` are an older convention: their steps start at `|G_0|/|G_0|`. The normalized Herbrand function, with steps `|G_(i+1)|/|G_0|`, is `herbrandValueNat` in `Ramification.Herbrand.Function`. The step uses `Nat.card`, which is 0 for an infinite group.
- Levels are natural numbers only.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/GaloisValuation/Ramification.lean`: the Lean file is the source byte for byte (SHA-256 `67ea22dbec487622cd8ed9d5063306392b11d0e8228c736084526a7a56151356`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
