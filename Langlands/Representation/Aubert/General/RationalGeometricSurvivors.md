# Actual rational geometric survivors

Worker 167. This is an internal deduction from the published actual normalized
geometric-term constructions, rational standard-Levi conjugation theorems,
maximal-root class comparison, and cuspidal vanishing. It makes no new assertion
from the literature. The results concern individual actual terms, rather than
the Jacquet module of an induced representation.

The generic helper `geometricTermInverseConjugationIso` works for closed Levi
and radical families in any locally compact nonarchimedean group. It has
independent index, ambient group, and carrier universes. Its input is a literal
inverse-conjugation membership equivalence from `M J` to `M I`, together with
the source and target decompositions for `n⁻¹`. For a smooth representation of
`M J`, it identifies the geometric term at `n⁻¹` with pullback along the inverse
of the original `conjugationEquiv n hConj`. It first derives the full-Levi
conjugacy for `n⁻¹` by conjugating the membership test, applies
`geometricTermFullLeviIso`, and uses the identity linear equivalence to compare
`n⁻¹⁻¹ * x * n⁻¹` with `n * x * n⁻¹`. Induction retains the saturated carrier
universe `max uG uV`.

The rational constructions use actual rational points of an affine group
scheme over a topological field, with their canonical `pointTopology`, assumed
locally compact and nonarchimedean. They retain the literal simple-root subsets,
closed rational Levi and radical families, and the actual intersection
semidirect decompositions. The field universe `u` and representation universe
`v` are independent; every rational object has the original carrier universe
`max (u + 1) v`.

`pointGeometricTermRootAssociationIso` assumes the retained connected-reductive,
maximal split torus, generic cocharacter, standard-cocharacter, and actual
normalizer/centralizer comparison inputs. An actual root-association witness
from source `J` to target `I` implies literal conjugacy of the entire Levis by
the published `conjugationMembership_of_rootAssociation`. The generic full-term
comparison then gives pullback along the existing
`rootAssociationLeviConjugationEquiv`. This root-association witness is an
explicit hypothesis of this general helper; it is not a reducibility conclusion.

`pointGeometricTermOneIso` applies at the literal identity element with source
and target `J`. Its full conjugacy follows from multiplication by `1`, and
`conjugationFunctorOneIso` identifies the resulting pullback with the original
object. This construction requires neither root comparisons nor a
non-self-association hypothesis. It assumes the actual decompositions at `1`.

`pointGeometricTermInverseLongestIso` also assumes finite simple roots and Weyl
group, the actual Coxeter system, the original root-length and simple-reflection
comparisons, the minimality-length criterion, and the associated-subset laws.
For every normalizer lift `n` of `longestRep actual J`, it considers the actual
term with target `associatedSubset actual J`, source `J`, and representative
`n⁻¹`. Its output is exactly pullback of the original object along
`(associatedLeviConjugationEquiv ... J n hn).symm`. The standard-cocharacter
premise supplies the existing standard-Levi conjugation statement; the published
`associatedLeviConjugation_of_standard` supplies the full subgroup image. The
generic inverse-conjugation helper proves the objectwise comparison. No
maximality, cuspidality, or irreducibility premise is needed for this surviving
term's identification.

The two remaining theorems concern cuspidal objects for a maximal standard
subset `J` with `J ≠ associatedSubset actual J`. They retain the original
`IsCorollaryLeviCuspidal` predicate, the standard-Levi intersection premise,
and all original root and structural comparisons. For every minimal Weyl
representative, every actual normalizer lift of that class, and every actual
source and target decomposition:

- `pointGeometricSelfTerm_subsingleton_of_ne_one` proves that the self term
  has a subsingleton carrier if its class is not `1`.
- `pointGeometricAssociatedTerm_subsingleton_of_ne_inv_longest` proves the same
  for a term toward the associated Levi if its class is not
  `(longestRep actual J)⁻¹`.

Both proofs use the corresponding published full-intersection equivalence from
`MaximalRootAssociationClasses` to show that the source intersection is proper.
The published `pointCuspidalGeometricTermVanishing_of_rootComparisons` then
kills that actual term. The surviving class directions, including the inverse
on the associated longest representative, are preserved literally. No
finite-length preservation or irreducibility is assumed in either proof.

These results give the candidate surviving terms and vanishing of the other
terms. They do not supply a normalized filtration of the actual induced
Jacquet module or identify the entire module with its surviving grade.
Consequently the induced Jacquet equivalences, simplicity conclusions, and
`RationalRankOneSelfAssociationStatement` remain consumer obligations.
