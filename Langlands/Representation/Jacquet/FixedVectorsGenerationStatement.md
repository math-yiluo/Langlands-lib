# Fixed-vector generation of actual Jacquet coinvariants

Worker 189. This internal statement extracts the algebraic deduction in the
lemma preceding Howe's theorem, Renard VI.6.3, printed page 178 / PDF184.

`Langlands.Jacquet.FixedVectorsGenerationStatement.{uR,uG,uV}` quantifies
independently over a commutative coefficient ring `R`, a group `G`, a module
`V`, and an actual representation `ρ`. It uses actual subgroups `N`, `M`,
`K`, and `K₀`, with `M ≤ Subgroup.normalizer N`. Its remaining hypotheses are:

- `K₀ ≤ Subgroup.normalizer K`;
- every `g : G` has a factorization `g = m * n * k`, with `m ∈ M`,
  `n ∈ N`, and `k ∈ K₀`;
- every subrepresentation containing `fixedVectors ρ K` equals the whole
  representation.

It concludes that every subrepresentation of the actual quotient action
`Jacquet.action ρ N M hMN` containing all its fixed vectors under
`K.comap M.subtype` equals the whole quotient representation. The latter
subgroup is `K ∩ M` viewed inside `M`. The quotient and its action are the
published constructions in `Jacquet.Coinvariants`; they are not arbitrary
modules supplied as input. The generating condition is expressed by containment
in subrepresentations and does not assert finite dimension.

The original source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF184–185 were read in full. No project errata note for this edition was found.

This is an explicit algebraic generalization of the source lemma. In the source,
`K` is compact open and normal in the fixed special compact subgroup `K₀`,
and `P = M N` is a standard parabolic with Iwasawa factorization. Since `P`
and `K₀` are subgroups, `G = K₀ P` also gives `G = P K₀` by inversion;
factoring an element of `P` as `m n` gives the displayed hypothesis.
Topology, compactness, and the containment `K ≤ K₀` are unnecessary once
these algebraic conditions are supplied. The statement uses the unnormalized
Jacquet action throughout.

This proposition supplies no proof, actual Iwasawa factorization, special
compact subgroup, simultaneous Iwahori basis, Jacquet nonvanishing theorem,
supercuspidal detection, normalization comparison, or Howe finite-length
conclusion. Those remain separate obligations for its consumers.
