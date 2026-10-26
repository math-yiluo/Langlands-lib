# Equal-rank assembly after GL finite length

Worker 353 authored this internal specialization of the published
`EqualRankTrilinearPrerequisites` adapter. It applies the published theorem
`Langlands.glAdmissibleFiniteLength` in each representation-carrier universe,
then uses the existing assembly. The field universe and the two carrier
universes remain independent.

`EqualRankTrilinearMirabolicPrerequisites` is a Prop-valued conjunction of
seven explicit inputs: mirabolic restriction finite length in both carrier
universes, irreducible functional multiplicity in both carrier universes,
finite-exception twisted-pairing rigidity, compact twisted pairing, and
equal-rank Frobenius reciprocity. The restriction finite-length inputs retain
their full published quantifiers; the other five inputs use the supplied
field, topological data and rank. The definition assumes none of these inputs
and contains no uniqueness conclusion.

`equalRankTrilinearPrerequisites_of_mirabolic` prepends the two published GL
finite-length proofs to the seven supplied inputs. The theorem applies
`glAdmissibleFiniteLength.{uF,uV}` and
`glAdmissibleFiniteLength.{uF,uW}` without any universe identification.
`equalRankTrilinearUniqueness_of_mirabolic_prerequisites` then applies the
published `equalRankTrilinearUniqueness_of_prerequisites`. That adapter handles
the comparison of the supplied topology with the canonical topology when
using GL finite length, the character change, finite filtrations, spectral
shift, central bilinear vanishing and coefficient-model descent.

This pair supplies only a conditional implication. It proves neither the
seven remaining inputs nor unconditional equal-rank trilinear uniqueness.
It changes no published statement or imported pair.

The construction is internal derived mathematics: it specializes two
published Library interfaces and makes no additional source-derived claim.
The imported adapters' paired Markdown explains their correspondence with
JPSS's finite-filtration argument, and the imported GL proof's Markdown
explains its finite-length argument.
