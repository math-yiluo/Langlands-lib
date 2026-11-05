# Split radical containment for pseudo-parabolic subgroups

Author: Worker 60.

`Langlands.GroupScheme.pseudoParabolicSplitRadicalContainment.{u}` proves
exactly `PseudoParabolicSplitRadicalContainmentStatement.{u}`, with no
additional premise. The statement and its imported definitions are unchanged.

The proof introduces the target's full data: every field in universe `u`,
every smooth connected affine group scheme `G`, the supplied ordinary
ground-field radical `r`, cocharacter `χ`, supplied product representative
`i : P → G`, and supplied split ground-field radicals `n` of `G` and
`m` of `P`. For each relative test `T` and point `x`, compose the
membership characterization of `i` as the ordinary-radical product with
the published equivalence `pseudoParabolicSplitRadicalProduct`.
The result `hPs` presents the same actual inclusion `i` as the fppf-local
product of `P_G(χ)` with the supplied split radical `n`. Its closedness
is the original closedness of `i`; the proof chooses no new `P`.

Apply `PseudoParabolicSplitNormalProduct.containment` to that
presentation and the original split-radical predicates. This imported
theorem constructs an actual smooth connected split unipotent product
`D = U_G(χ) R_us,k(G)` inside `P`. Both `P_G(χ)` and `R_us,k(G)`
normalize `D`, so the split-product presentation of `P` makes `D`
normal in `P`. Greatestness of the supplied split radical `m` contains
this subgroup. Composing that containment with `i` gives exactly

```lean
Dynamic.unipotent χ ≤ SubgroupFunctor.range (m ≫ i) ∧
  SubgroupFunctor.range n ≤ SubgroupFunctor.range (m ≫ i)
```

Both containments quantify over every relative scheme test, including
nonaffine and nonreduced tests. Product factorization is fppf-local
throughout. The proof retains every field, including finite and imperfect
fields and every characteristic, and all original representatives.
It adds no reductivity, perfectness, infinitude, lifts, local sections,
or theorem-valued premise, and does not identify the ordinary and split
radicals.

This is an internal proof assembly of the published source-backed target.
It implements the first paragraph of the proof of Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), Corollary 2.2.5,
printed p.64 (one-based PDF p.90), using the published Proposition 2.2.4
proof for the product replacement and the published normal-product
construction for splitness, normality and greatestness. The statement's
paired Markdown records the original-source provenance. The registered
source is
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
