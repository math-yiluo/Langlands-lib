# Actual simple-root subsets and rational-point families

This is a derived consumer construction for the general Aubert program. It
connects finite subsets of the published simple relative roots to the published
standard subgroup functors on the actual rational-point group. It supplies no
Aubert identity or general reductive structure theorem.

All declarations are in
`Langlands.Aubert.General.RationalPointFamily`. The base `k : Type u` is a field,
`T` is a commutative group scheme over `Spec k`, and `i : T.toGrp ⟶ G` is an
actual group-scheme homomorphism. The root-indexed definitions require
`IsAffineHom G.X.hom`. They need neither splitness nor connected reductivity;
these stronger hypotheses belong to subsequent realization statements.

`SimpleRoot i ν` is exactly the subtype of
`GroupScheme.simpleRelativeRoots i ν` in the character lattice of `T`.
`rootSet i ν I` is the image under `Subtype.val` of a finite subset of this
subtype. Its membership, subset, finiteness and injectivity lemmas prove that no
root is discarded or duplicated. The empty subset maps to the empty character
set. With an explicit `Fintype (SimpleRoot i ν)`, the full subset maps to
`simpleRelativeRoots i ν`. This module constructs no such instance and proves
no general finiteness theorem for the whole root set.

`parabolic`, `levi` and `unipotent` are the exact published
`standardParabolicPoints`, `standardLeviPoints` and `standardUnipotentPoints`
at `rootSet i ν I`. Their ambient carrier is the published
`PointTopology.RationalPoint k G.X`, definitionally the morphisms from the
identity test object to `G.X`. The Levi and unipotent inclusions in the
parabolic follow by evaluating the published subgroup-functor inclusions.
The point group is not replaced by an abstract model.

`torusPoints i` is the actual image of `i` on these rational points, using
`SubgroupFunctor.range`. Its membership lemma is the existence of a torus
point whose postcomposition with `i` is the given ambient point.
`torusPoints_le_centralizerPoints` uses commutativity on every test scheme,
followed by the point homomorphism induced by `i`. The published whole-torus
centralizer inclusion then places these points in every indexed standard
Levi. `centralizerPoints_le_pointCentralizer` tests scheme centralization at
the identity test object to obtain commutation with every point in the image.
Only this direction is proved.

`Weyl i` and `LeviWeyl i ν I` reuse the published actual subgroup quotients:
the normalizer of `torusPoints i` modulo its full centralizer, and the
normalizer intersection with `levi i ν I` modulo the restricted full
centralizer. `schemeStandardWeyl` separately names the published image in
`GroupScheme.relativeWeylGroup i` of scheme-normalizing points lying in
the same standard Levi. No equality of the scheme-normalizer points with the
normalizer of the rational-point image, or of their centralizers, is asserted.
In particular, the proved centralizer inclusion is not silently reversed.

For any topology on `k`, `pointTopology` is exactly the published
`rationalPointTopology k G.X`; it installs no global instance. A consumer
explicitly binds this topology on the same rational-point carrier. Continuity
of group operations, local compactness and the nonarchimedean group property
are separate obligations.

The remaining realization work includes finiteness of the actual simple-root
subtype; existence of standard cocharacters and equality of the intersection
definitions with dynamic subgroups; Levi decomposition, endpoint and
Levi-in-Levi assertions; the scheme-versus-image subgroup and Weyl quotient
comparisons in the actual local-field scope; and the relative-root/Coxeter
and positive-sign comparisons. Even for the empty root set this module
asserts no unsupported equality of its standard Levi with a centralizer:
an empty family of qualifying cocharacters has the published intersection
convention. These obligations remain separate from the representation-theoretic
identities and their proofs.

The source motivation is Aubert, *Dualité dans le groupe de Grothendieck des
représentations lisses de longueur finie* (1995), printed pp.2180–2182,
especially Definition 1.5 and Theorem 1.7, and Renard, *Représentations des
groupes réductifs p-adiques*, version of 9 July 2026, V.3.12 and V.4.1–V.4.3,
printed pp.112 and 118–119. The full-centralizer quotient follows the
Renard convention and the host task; Aubert's printed denominator is the
torus itself, as explained in the published `Group.RelativeWeyl` companion.
The finite-subset image and identity-test packaging are internal constructions,
not additional assertions attributed to either source. The implemented proofs
use injectivity of subtype values, finite-set images, commutativity of torus
points and evaluation of existing subgroup-functor inclusions.
