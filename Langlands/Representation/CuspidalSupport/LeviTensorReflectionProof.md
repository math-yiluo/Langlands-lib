# Supercuspidality reflected by the actual Levi tensor

Author: Worker 158.

`padicLeviTensorSupercuspidalReflection.{uF,uW}` proves exactly the published
`PadicLeviTensorSupercuspidalReflectionStatement.{uF,uW}`. The supplied field
topology is installed, and the field and factor-carrier universes remain
independent. No Jacquet vanishing or tensor comparison is assumed.

The proof fixes a block and a proper standard parabolic of its group. It
refines that block by the chosen shape and uses a one-block shape in every
other block. If this product parabolic were the whole Levi, evaluating at a
coordinate element would put every matrix into the chosen proper parabolic,
a contradiction. The lemma `singleBlock_unipotentSubgroup_eq_bot` proves
that the unipotent subgroup in each remaining block is trivial: its matrix
entries equal the identity entries in the sole block, which covers all
coordinates.

Levi quasicuspidality therefore gives vanishing of the tensor coinvariants
for a subgroup acting only in the selected slot. Irreducibility supplies
nonzero carriers in all other slots. The new derived linear algebra lemma
`FiniteTensor.coinvariants_factor_subsingleton` then gives vanishing of the
selected factor's actual coinvariants. Its proof contracts a tensor basis
vector in the other slots and descends the resulting map to the quotient;
see its paired Markdown for the construction. The empty complementary tensor
is included, so no exception is needed when the original Levi has one block.

Finally, the proof combines this standard-radical vanishing with the given
factor admissibility through the published
`GeneralLinear.isSupercuspidal_iff_standard`. Its existing conjugation
comparison supplies the all-conjugates condition. The statement pair and
all imported Library pairs remain unchanged.

This is a derived implementation of the reverse implication in Zelevinsky
1980, section 1.10 (printed p.174, PDF p.11), with product Levis, refinements,
and quasicuspidality as in Bernstein–Zelevinsky 1977, sections 2.2 and 2.4
(printed pp.446–447, PDF pp.7–8). The original files, registration identifiers,
and hashes are recorded in `LeviTensorReflectionStatement.md`; the proof uses
the quotient contraction route rather than assuming a tensor-coinvariant
isomorphism from those sources.
