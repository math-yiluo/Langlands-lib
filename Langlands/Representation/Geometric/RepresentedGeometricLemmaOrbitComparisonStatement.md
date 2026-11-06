# Local normalized orbit comparison for represented parabolics

Worker 1193 supplies an internal prerequisite statement for the filtration form of Renard VI.5.1. It isolates the remaining local representation calculation after the support and exactness constructions. This file asserts a proposition; it does not prove that proposition or the full geometric lemma.

The original source is Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The local coinvariant–compact-induction isomorphism VI.5.1.3 and its tensor proof are on printed p.167 / PDF p.173. The stabilizer calculation and cancellation of the residual modular characters are on printed pp.171–172 / PDF pp.177–178. This is a derived interface for those steps, expressed using the Library's actual functors.

`RepresentedGeometricLemmaOrbitComparisonStatement.{u,v}` quantifies over the same field and connected reductive group scope as `RepresentedGeometricLemmaStatement`. The parabolic maps, actual rational Levi maps, geometric radical maps and multiplication isomorphisms are arbitrary. For one rational point `z`, it assumes a `GeometricLemmaIntersectionDatum` at `z`; all six scheme intersection identities, the actual conjugation map and rational-point homeomorphism, and the maximal split torus condition in that datum are retained.

The proposition asks for a natural isomorphism from the composite of:

1. `smoothLeviInducingFunctor`, the original inducing representation inflated to the literal source parabolic image and twisted by its positive half Haar modulus;
2. `Geometric.orbitPiece` at `z⁻¹`, conjugated restriction to the actual orbit stabilizer followed by compact induction to the literal target parabolic image;
3. `leviParabolicCoinvariantsFunctor`, actual coinvariants by the nested target radical with the inverse half Haar normalization and restriction to the actual target Levi rational points;

to `D.pieceFunctor`, the normalized Jacquet functor along the represented source intersection, pullback along the actual conjugation homeomorphism, then normalized induction along the represented target intersection.

The inverse in the orbit-piece argument is necessary: `orbitPiece P Q w` uses the orbit of `P w⁻¹`, while the datum at `z` describes `P z Q`. Both sides use the same original source category of all smooth complex representations, with representation carrier universe `v` independent of the field/group universe `u`. The target is in representations with carrier universe `max u v`. `Nonempty` packages a natural isomorphism, including naturality in all intertwiners, without choosing one in the statement.

No global representatives or support filtration are inputs. This local prerequisite does not construct intersection geometry, prove compactness of an arbitrary parabolic quotient, or prove the modular cancellation. Those are retained proof obligations. The companion `RepresentedGeometricLemmaOrbitReduction` proves how the local statement, once established together with the existing structural inputs, gives the original filtration statement without weakening its conclusion.
