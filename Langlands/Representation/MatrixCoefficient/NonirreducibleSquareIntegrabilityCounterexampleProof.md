# Renard IV.3.2: a nonirreducible single-coefficient counterexample

Author: Worker 713. The theorem
`Langlands.Renard.CompactRepresentation.nonirreducibleSquareIntegrabilityCounterexample`
proves the exact published
`Langlands.Renard.CompactRepresentation.NonirreducibleSquareIntegrabilityCounterexampleStatement`.
All construction helpers are private. The statement and its imported predicates
are used unchanged.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, IV.3.2 Remark, printed p.100 / PDF p.106; conventions
in IV.3.1–IV.3.2, printed pp.99–100 / PDF pp.105–106. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The pages were read directly. Renard leaves the counterexample to the reader;
the concrete construction and proof below are internal derived mathematics,
rather than a construction attributed to the source.

## Group, quotient and measures

Take `D = DihedralGroup 0`, Mathlib's infinite dihedral group, with the discrete
topology and its Borel measurable space. This is a Hausdorff, locally compact,
totally disconnected topological group. Mathlib supplies its infinitude and the
identity `DihedralGroup.center_eq_bot_of_zero`.

Use the actual quotient `Q = D / Subgroup.center D`, equipped with the quotient
topology and its Borel measurable space. The center is open because `D` is
discrete, so `Q` is discrete. Its quotient map is injective: equality of cosets
puts the quotient of the representatives in the trivial center. Consequently
`Q` is infinite.

Both measures in the target are counting measure, on `D` and on `Q`
respectively. The helper `count_haar` verifies the Haar conditions: compact
subsets of a discrete space are finite, and a nonempty open subset has positive
counting measure. Translation invariance of counting measure supplies both left
and right invariance. No identification of the quotient with another group or
normalization assumption is needed.

## Smooth representation and nonirreducibility

Let `V = ℂ[D]` and let `ρ` be the left regular representation, so
`ρ(g)[h] = [gh]` on the group-algebra basis. Bundle this as the smooth
representation `π`. Any representation of `D` is smooth because the trivial
subgroup is open and fixes every vector. The same argument applied to the dual
representation shows that every algebraic linear functional used here belongs
to the published smooth dual.

Write `δ = [1]`. The two functionals are evaluation at the identity and
augmentation, the sum of all coefficients of a group-algebra element.
The implementation constructs them with `Finsupp` linear maps and proves their
values on each basis vector. Linear induction proves that augmentation is
invariant under the regular action.

Its kernel is therefore a subrepresentation. It contains the nonzero vector
`[sr 0] - [1]`: augmentation vanishes on this vector, while evaluation at the
identity gives `-1`, since the reflection `sr 0` is not the identity.
The kernel is proper because augmentation takes the value `1` on `δ`.
If `π` were irreducible, its subrepresentation lattice would force this kernel
to be either bottom or top, and these two vectors contradict the respective
possibilities. This proves `¬ π.IsIrreducible` directly.

The trivial character of the center is a unitary central character for `ρ`.
Its kernel is open, and its scalar-action condition follows from triviality of
the center.

## Good and bad coefficients

For the smooth evaluation functional and `δ`, the matrix coefficient at `g`
is `1` when `g = 1` and `0` otherwise. In particular it is nonzero as a function,
as witnessed at the identity. Its descended norm on `Q` is the real indicator
of the singleton `{1}`. The proof uses quotient induction and injectivity of the
quotient map to establish this formula. The singleton is measurable and has
counting measure `1`, so `memLp_indicator_const` proves that the norm belongs
to `MemLp` with exponent `2`.

For the smooth augmentation functional and the same vector, the matrix
coefficient is the constant function `1`. Quotient induction shows that its
descended norm is also constantly `1`. This is not in `MemLp` with exponent
`2`: `memLp_const_iff` would force finiteness of the measure of `Q`, while
`Measure.count_apply_infinite` gives infinite measure.

The raw predicate `π.IsSquareIntegrableModuloCenter` existentially chooses a
unitary central character and then requires all smooth coefficients to be in
`MemLp`. The proof tests its claimed integrability on the augmentation
functional and `δ`. The published
`UnitaryCentralCharacter.coefficientNorm_eq` identifies that chosen datum's
norm with the explicit trivial-character norm above, giving the contradiction.
Thus the failure concerns coefficient integrability itself.

## Exact conclusion

The final proof assumes the universal implication negated by the published
statement and applies it to `D`, its two counting measures, `π`, the proof of
nonirreducibility, the trivial unitary central character and the nonzero
evaluation coefficient. Its conclusion contradicts the bad-coefficient
argument. Both the group and representation carrier lie in `Type 0`, as the
target requires. The positive irreducible single-coefficient criterion is not
used in this proof.
