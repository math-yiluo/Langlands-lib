# Separation of actual reflection cells from strict affine root groups

For arbitrary universe `u` and actual valuation building data `B`, this derived
module defines `B.rootReflectionCentralizerCell a ψ m`. Its elements have the
literal factorization

```
w = l * m.val * j(z) * r,
l, r ∈ U_{-ψ},   z ∈ Z(F).
```

Here `j` is the supplied centralizer inclusion and the centralizer factor is
unrestricted. The definition accepts any character, affine functional and
actual normalizer point. It extends the existing centralizer-zero cell rather
than changing its definition.

The theorem
`disjoint_affineRootGroupPlus_rootReflectionCentralizerCell` assumes that `α`
is an actual relative root, `ψ.linear = rootForm B.i α`, and the actual
character action of `m` sends `α` to `-α`. It proves that the displayed cell is
disjoint from the strict affine root subgroup `U_{ψ+}`. The functional need not
belong to a chosen affine-root set, and `m` need not be supplied by an opposite
pair or have a specified valuation functional.

To prove disjointness, take a putative intersection point `w` and the displayed
factors. The normalizer point `n = m * B.centralizer.toNormalizer z` still sends
`-α` to `α`, since the supplied centralizer has trivial character action.
Rearranging the literal factorization gives

```
n.val = l⁻¹ * w * r⁻¹.
```

If `w = 1`, then `n.val = l⁻¹ r⁻¹` lies in the actual negative root subgroup.
The imported theorem `RelativeRoot.normalizer_not_mem_subgroup_of_flip`
excludes a normalizer that both belongs to that subgroup and negates its
nonzero character. This handles the identity case separately from V5.

If `w ≠ 1`, fix an apartment point `x`. Strict root-group membership gives
`w ∈ U_α(F)` and `ψ(x) < x.val α w`. Its valuation is a finite real number
`t`, by the imported nonidentity valuation lemma. Both `l⁻¹` and `r⁻¹` are in
the negative root subgroup, and their product with `w` is the actual normalizer
point `n`. Thus V5 applies to this supplied opposite pair and gives
`x.val (-α) l⁻¹ = -t`. Membership of `l⁻¹` in `U_{-ψ}` also gives
`-ψ(x) ≤ x.val (-α) l⁻¹`. Consequently `t ≤ ψ(x)`, contradicting strict
membership.

For actual parahoric data `P`,
`rootReflectionCell_subset_rootReflectionCentralizerCell` forgets the
centralizer-zero constraint on the exhibited factor. The theorem
`disjoint_affineRootGroupPlus_rootReflectionCell` restricts the preceding
result to the unchanged cell `P.rootReflectionCell α ψ m`.
Finally, `disjoint_affineRootGroupPlus_reflectionElementCell` applies the
published root-flip theorem to any supplied opposite pair of a nonidentity
point of `P.rootGroup α`. It needs no condition relating that point's valuation
to `ψ`.

These constructions and proofs are internal deductions from the imported
actual cells, centralizer character action, valuation axioms and root-subgroup
separation. They require no apartment-axiom, rank-one factorization-existence,
or cover-image centralizer-comparison hypothesis. The earlier jump-cell
inclusion retains its explicit hypotheses. This module proves no existence of
opposite pairs, full rank-one two-cell decomposition, Tits axioms or final
affine Iwahori–Tits statement.
