# Compact norm-kernel restriction and proper standard Jacquet vanishing

The theorem
`Langlands.Aubert.General.RationalPointFamily.rationalCompactRestrictionCuspidal`
proves the exact published proposition
`RationalCompactRestrictionCuspidalStatement.{uF,uV}`. Worker 389 assembled
the proof with Worker 1555's integral Weyl correction and actual-point
norm-kernel and compact-escape constructions.

The source statement is Renard VI.2.1(c) implies (a), French edition dated
9 July 2026, printed pp.137–138 / PDF pp.143–144, with the proper-standard
convention in Remark 1 on printed p.137. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The implemented proof follows the source's compact averaging and contraction
route, deriving the needed norm-kernel direction by the integral Weyl
construction described below.

All quantifiers of the target are retained: an arbitrary nonarchimedean
local field, an actual connected reductive group scheme, an actual maximal
split torus and generic cocharacter, the canonical rational-point topology
with its stated locally compact, nonarchimedean and Hausdorff premises,
`StandardCocharacterStatement`, the actual relative root system, and
closedness of each actual standard unipotent subgroup. The field universe
`uF` and carrier universe `uV` are independent. The compact-coefficient
antecedent concerns the entire smooth dual of the actual restricted action
on `Plancherel.rationalCommonNormKernel G`, with the subgroup topology.

For a proper standard index `I`, injectivity of `rootSet` shows that its
root set is a strict subset of the simple roots. The supplied standard
cocharacter statement gives a cocharacter `ζ` for that face. The actual
root-system premise supplies the finite relative Weyl enumeration. The
construction `normKernelCocharacter i ζ` subtracts the integral Weyl sum
from the group-order multiple of `ζ`. Its proved pairing laws annihilate
all restricted ambient rational characters and multiply every root pairing
by the positive Weyl-group order. Thus the corrected cocharacter is standard
for the same face. These calculations take place in the integer lattice
and impose no characteristic restriction.

The published `exists_unit_tendsto_pow_zero` chooses a field unit `t` whose
field powers tend to zero. Evaluating the corrected cocharacter at `t`
gives the literal `cocharPoint` used by dynamic contraction.
`normKernelCocharacterPoint_mem` places it in the common norm kernel of
all ambient rational characters. The proper face supplies a simple root
with positive pairing. The compact-escape theorem pulls an ambient compact
set back through the closed torus embedding and maps it into the field by
that character. This compact image is closed and omits zero, whereas the
character values of the powers tend to zero. Therefore the point's powers
eventually leave every ambient compact set.

The helper `rational_cocharPoint_hasOppositeIwahoriBasis` keeps this specified
cocharacter and parameter. The standard-cocharacter comparisons identify
the actual Levi and unipotent radical with the dynamic centralizer and
unipotent subgroup; the opposite radical is the dynamic subgroup for the
inverse cocharacter. Published opposite-cell openness and unique
factorization, Levi normalization and centrality, and uniform dynamic
contraction in both directions supply an ambient-cofinal opposite Iwahori
contraction basis for this same point. Closedness of the opposite subgroup
is derived over the local field, and closedness of the standard radical is
the target's existing premise.

For the representation step,
`normalizedJacquet_subsingleton_of_compactCoefficients_of_oppositeIwahoriBasis`
uses the upper contraction from this basis and applies
`Jacquet.relations_eq_top_of_compactCoefficients_of_iwahoriBasis`.
Smoothness gives a compact open subgroup in the basis fixing each vector.
For any full algebraic functional, composition with compact averaging is
smooth for the restricted action. Compactness of its coefficient support,
inclusion into the ambient group, and escape of the chosen powers give
eventual scalar vanishing along the compressed orbit. The algebraic-dual
separation lemma supplies a zero averaged vector. The published generalized
compression-kernel identity then puts the original vector in the actual
Jacquet relation space. This argument uses no finite-dimensional fixed
space or admissibility premise.

Finally, `normalizedJacquet_subsingleton_of_relations_eq_top` identifies the
underlying carrier of the actual normalized Jacquet object with the
trivial-character localization coinvariants. The equality
`Jacquet.Localization.relations_one` transfers the top relation space;
surjectivity of the quotient map makes every quotient element zero.
The normalization twist changes the descended action and preserves this
carrier. Applying the argument to each proper index proves the existing
`IsCuspidal` predicate with the target's derived semidirect decompositions.

The three helper theorems in this module are internal derived results.
Their provenance is the published dynamic opposite-basis construction in
`RationalOppositeIwahoriBasisProof`, the compact averaging and generalized
kernel results assembled in `CompactCoefficient.IwahoriConverse`, and the
actual normalization and localization definitions. The final assembly also
uses `NormKernelStandardCocharacter` and `NormKernelContractingPoint` for
the integer-lattice and compact-escape derivations. The theorem adds no
admissibility, irreducibility, finite-length, finite-dimensionality,
split-group, nonempty-root, special-compact, Iwahori-basis, Cartan or
compact-escape premise. It proves this converse only; the forward
compact-restriction theorem and the whole-category VI.3.5 decomposition
retain their separate statements and proof obligations.
