# Compact containment in the actual upper-unipotent group

Worker 201 proves
`Langlands.GeneralLinear.upperUnipotentCompactContainment` with exactly the
closed published target
`Langlands.GeneralLinear.UpperUnipotentCompactContainmentStatement.{uF}`.
The proof includes every prime, every `PadicField` in every field universe,
every supplied compatible `TopologicalData`, every natural rank, and every
compact subset of the actual upper-unitriangular matrix group. All topological
instances are installed from the supplied `T`; no canonical-topology substitution
or additional containment hypothesis is made. The existing statement pair and
its import closure are unchanged.

The same module exposes
`Langlands.GeneralLinear.upperUnipotent_isLimitOfCompactSubgroups F T n`.
For precisely `T.topology`, this proves the existing
`Langlands.Jacquet.Localization.IsLimitOfCompactSubgroups` predicate for
`GeneralLinear.upperUnipotent n F.Carrier`. It simply forgets the openness field
of the containing `OpenSubgroup`, preserving its carrier, compactness, and
containment of the entire compact subset. This supplies a geometric hypothesis
for character localization; the module proves no character-localization or
Whittaker exactness theorem.

## Implemented proof

The public helper
`Langlands.RankinSelberg.common_integer_denominator_of_isCompact` works over
any field with a `ValuativeRel` and its compatible `IsValuativeTopology`.
Write `O` for the integer subring of `ValuativeRel.valuation F`. For each
nonzero integral scalar `d`, let `U_d = {x | d * x ∈ O}`. These sets are open
by `Valuation.isOpen_integer` and continuity of multiplication by `d`.
The published `RankinSelberg.common_integer_denominator`, applied to a singleton,
shows that they cover every field element. They form a directed family:
`U_d` and `U_e` are contained in `U_(d*e)` since both scalars are integral.
The index family is nonempty, with scalar `1`. Mathlib's
`IsCompact.elim_directed_cover` then places the entire compact set in one
`U_d`. This proves uniform denominator clearing for arbitrary compact sets;
no finiteness assumption on that set is introduced.

For positive rank, take the union of the images of the given compact subset
under all matrix-entry maps, both before and after inversion. Each image is
compact by `UpperUnipotent.entry` and continuity of inversion. There are only
finitely many entries, so their union is compact. Apply the new helper to
obtain one nonzero integral scalar `d` clearing all these entries at once.

The private helpers `scalingDiagonal`, `scalingDiagonal_conj_entry`, and
`scalingDiagonal_conj_integral` implement the published diagonal calculation.
Let `D` have diagonal entries `(d^i)⁻¹`. The `(i,j)` entry of `D*g*D⁻¹` is
`(d^i)⁻¹ * g_ij * d^j`. Above the diagonal, this equals
`d^(j-i-1) * (d * g_ij)`, hence is integral. On the diagonal it is `1`, and
below the diagonal it is `0`. Apply the same argument to `g⁻¹`. Thus the
conjugate and its inverse have integral entries, which is exactly membership
in the actual ambient integral general linear subgroup by
`Conductor.levelSubgroup_zero` and `Conductor.mem_integralSubgroup`.

Pull `Conductor.levelOpenSubgroup F.Carrier n 0` back along the continuous
group homomorphism from the upper-unipotent subgroup to the ambient general
linear group given by conjugation by `D`. The result is an actual open
subgroup containing every element of the original compact subset. It is
compact: conjugation is an ambient homeomorphism, `UpperUnipotent.isClosed`
gives a closed subgroup inclusion, and a compact set has compact preimage
under this composite closed embedding. The compactness of the integral
subgroup is the published `Conductor.isCompact_levelOpenSubgroup` theorem.
This argument does not require a separate internal conjugation automorphism
of the upper-unipotent group.

Rank zero is handled separately: the entire group is finite (indeed trivial),
so its top open subgroup is compact and contains the supplied set. Rank one
is covered by the positive-rank argument, and the empty compact subset is
allowed throughout. No exhaustion sequence or canonical containing subgroup
is asserted.

## Source and reuse provenance

Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter III, revision April 29, 2019, Lemma III.3.1 and its proof on
printed/PDF page 3, gives arbitrarily large compact open subgroups of p-adic
unipotent groups. Its upper-unitriangular case uses diagonal conjugation by
uniformizer powers. The original page was read and the retained file hash
verified; no errata file for this source was present in the current Library.
Registered source: `casselman-2019-jacquet-module`; SHA256:
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.

The implemented proof is a derived algebraic and topological version of that
construction. It uses an arbitrary nonzero integral common denominator instead
of selecting a uniformizer power. Compactness supplies that denominator via
the directed open cover above. The rank-zero extension and the direct
localization-predicate corollary are internal derivations.

Worker 117 is a coauthor for the adapted proof text from
`Langlands.Representation.RankinSelberg.UnipotentUnimodularity`: the three
private diagonal helpers and the compact-open pullback argument for
`unipotent_exists_compact_open`. Worker 201 supplied the compact-denominator
lemma, the compact matrix-entry union, the exact all-rank theorem, and the
consumer corollary. The finite-denominator theorem is imported by its published
Lean name. The new proof does not infer compact containment from the weaker
single-element or finite-subset containment conclusions.
