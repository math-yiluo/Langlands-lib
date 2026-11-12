# Compact rational representatives for split-torus character boxes

Author: Worker 82.

`torusCharacterBox F T S b` is the subset of actual adelic torus points with
all the stated two-sided character-norm bounds.

`exists_characterBox_bound_of_ratSpan_le` transfers these bounds to any
finite family `R` of characters with `ratSpan R ≤ ratSpan S`. It constructs
one positive unit `d` which bounds every character in `R` above by `d` and
below by `d⁻¹`, uniformly over the entire original box. This transfer
requires no splitting or compactness: it applies to any supplied
commutative group scheme, in particular to nonsplit tori. The set `S`
may be infinite and `R` may be empty.

The proof applies the existing rational-span bound for additive real
functionals to the logarithms of the normalized character norms. For each
character in the finite target family, it obtains a nonnegative linear
bound in `|log b|`. Summing those coefficients gives a common bound `D`;
the constructed unit is `expUnit D`. Exponentiation gives the two-sided
normalized norm bounds. No proportionality between individual weights and
simple roots is asserted.

For an actual split torus `T` over any number field `F` in universe `u`,
`exists_isCompact_rational_mul_mem_characterBox` constructs a compact subset of
`T(A_F)` meeting every principal rational left coset whose normalized character
norms lie between `b⁻¹` and `b` for every character in a rationally spanning set
`S`. The set `S` may be infinite; the split torus may have rank zero. All points,
norms, rational maps and topologies are the existing Library constructions.

The proof uses the published logarithmic equivalence `positiveLogEquiv` to
write a point `x` as `a * n`, where `a` lies in the intrinsic positive torus and
`n` is norm one for every rational character. The normalized character norms
of `a` equal those of `x`. The published theorem `isCompact_characterBox`
therefore puts `a` in a compact positive box. Independently, the unconditional
split-torus compact-cover theorem supplies a rational translate of `n` in a
fixed compact norm-one set. Commutativity allows the same rational point to
translate `x` into the product of those two compact sets. The continuous image
of their product is the constructed compact set.

This is internal derived infrastructure for the final compact-image step of
Springer, *Reduction theory over global fields* (1994), §3.5, printed p.215
(PDF p.9). It uses published proofs, rather than a reduction-theory assumption.
The registered source is `springer-1994-reduction-global-fields`, SHA-256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`, file
`literature/Reduction theory over global fields (Springer, 1994).pdf`.
No errata note exists. The theorem does not supply a splitting, bounds for
roots in a general reductive group, Galois descent, or the full compactness
theorem for central maximal split tori.

The rational-span transfer is also internal infrastructure for Godement,
*Domaines fondamentaux des groupes arithmétiques*, Bourbaki exposé 257
(1963, collected 1964), §10, Lemma 2, printed pp.217–218 (PDF pp.18–19).
After obtaining two-sided bounds on dominant characters, that argument
uses their finite-index span to control all characters. The Lean lemma
proves the analytic transfer once the exact rational-span inclusion is
supplied. It proves no dominant-weight spanning theorem, representation
height bound, Weyl overlap estimate or root lower bound.
The registered source is
`godement-1963-bourbaki-257-domaines-fondamentaux`, SHA-256
`b0a531469f376c1a56a7816f0fa579cd301c4162fb1c1aa8909c886e303c722d`,
file `literature/Godement - Domaines fondamentaux des groupes arithmetiques
(Bourbaki expose 257, 1963; collected 1964).pdf`.
No errata note exists for that source.
