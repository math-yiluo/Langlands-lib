# Actual semistandard orbit sections

This module constructs actual rational-point orbit sections for
each intrinsic `SemistandardSpectralIndex`, together with representative and
model comparisons. Its declarations are in
`Langlands.HarishChandraSchwartz.RationalSemistandard`.
The intrinsic index itself is imported from
`Langlands.GroupScheme.Rational.SemistandardSpectralIndex`.

The source is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)* (2003), DOI
10.1017/S1474748003000082, registered as `waldspurger-2003-plancherel`,
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
I.1, printed pp.238–239 (PDF pp.4–5), supplies the semistandard geometric
setting. VI.1, printed pp.295–296 (PDF pp.61–62), defines coherent sections
with actual induced coefficient values and tests smoothness in a compact
picture. VI.3, printed p.305 (PDF p.71), uses these section spaces for every
semistandard parabolic and unitary discrete-series orbit.

The rational-point realization, auxiliary scheme models and comparison
targets here are derived implementation content. They specialize the
published actual normalized induction and coherent orbit-section interfaces;
they are not additional assertions quoted from Waldspurger. In particular,
the source's nontrivial self-twist example in VI.1 is respected by retaining
coherence under every actual inducing equivalence.

## Hypotheses and actual subgroup models

The algebraic declarations use `F : Type u` with `[Field F]`, a commutative
group scheme `S` and a group scheme `G` over `Spec F`, and
`i : S.toGrp ⟶ G`. The index `p : SemistandardSpectralIndex i` contains the
actual all-test subgroup functors `P`, `M`, `U`, containment of `i` in `M`,
and the proposition asserting a parabolic with its reductive Levi and
geometric unipotent radical. No representing scheme or cocharacter is an
index field. The Library applies this construction with connected reductive
`G` and maximal split `i`; these two hypotheses occur explicitly in the
projection-continuity and compact-data existence targets and in the standard
specialization.

A sufficient working context for the point-topological and section declarations is
`[ValuativeRel F]`, `[TopologicalSpace F]`,
`[IsNonarchimedeanLocalField F]`, `[IsAffineHom G.X.hom]` and
`[LocallyOfFiniteType G.X.hom]`. They use the published rational-point
topology and its group, Hausdorff, locally compact, nonarchimedean and
measurability instances, with subspace topologies on literal subgroups.
The field is arbitrary nonarchimedean local, including positive
characteristic and finite residue field; no split-group assumption is
introduced. Individual declarations retain only the dependencies appearing
in their types or definitions; the exact scopes of the four unproved targets
are given below. The representation-carrier universe `uV` is independent of `u`.

`parabolic p`, `levi p` and `radical p` are identity-test evaluations of the
three all-test subgroups inside `rationalPoints G`. `decomposition` evaluates
the intrinsic algebraic decomposition on that same test scheme, obtaining
the actual semidirect decomposition. `isClosed_parabolic` and
`isClosed_radical` use the existing closed-immersion point-topology results;
the radical inclusion is the composite of its closed inclusion into the
parabolic with the parabolic's closed inclusion into `G`.

`LeviModel p` consists of a group scheme, its inclusion into `G`, all-test
representability of the exact subgroup `p.levi`, closedness of that inclusion,
and connected reductivity of the representative. `nonempty_leviModel` obtains
these data from `p.isParabolicWithLeviAndRadical`, composing the Levi and
parabolic closed inclusions. `chosenLeviModel` uses this proved existence.
These choices do not change `p`.

`LeviModel.pointHomeomorph` is the published multiplicative homeomorphism
from the representative's rational points onto the literal `levi p`.
`pointHomeomorph_coe` identifies its ambient value with postcomposition by
the actual inclusion. `normCharacters` transports every algebraic rational
character norm through its inverse. Continuity is proved by composition.
`unitaryCoordinates` transports the existing finite circle coordinates for
unitary unramified characters; `unitaryCoordinates_hasLaurent` is the
published Laurent-coordinate transport theorem. The coordinates are those
of the representative's rational image rank, with no supplied arbitrary
torus equivalence.

For a supplied commutative group scheme `A` and morphism
`a : A.toGrp ⟶ m.scheme`, `m.splitCenter a` is the actual point image of `a`
transported into the literal Levi. Given `ha : IsSplitComponent a`,
`splitCenter_le_center` follows from algebraic centrality and the actual
point equivalence.

## Sections, orbit classes and representative change

For an actual canonical
`pi : IrreducibleAdmissibleRep.{0,u,uV} (k := ℂ) (G := levi p)`,
`OrbitSections m pi` is `ProductInducedOrbitSections` for the actual norm
characters and decomposition. It is a dependent product over every actual
inducing representative in the unitary unramified twist orbit. Its fibers
are the published normalized product-induced coefficient objects on
`rationalPoints G × rationalPoints G`, with vector tensor smooth
contragredient coefficients. The raw product alone imposes no coherence.

`CompactData p` supplies an actual open subgroup `compact`, compactness of
its underlying set, continuity of the literal Levi projection, and the
pointwise factorization
`∀ g, ∃ x : parabolic p, ∃ k : compact, g = x * k`.
`smoothOrbitSections m d pi` is the published complex submodule requiring
coherence under **every** actual inducing equivalence and finite
scalar-smooth compact-picture pullback in `m.unitaryCoordinates`.
Finite scalar-smooth means a finite sum of fixed compact coefficient
vectors times scalar functions whose real-angle lifts are `ContDiff ℝ ∞`.
Consequently the construction retains the genuine coefficient action of
self-twists. It is not defined as a product of independent scalar functions.

The orbit-class declarations additionally retain a split component
`a : A.toGrp ⟶ m.scheme`, `ha : IsSplitComponent a`,
`[(m.splitCenter a).Normal]`,
`[MeasurableSpace (levi p ⧸ m.splitCenter a)]`, and a supplied measure
`mu` on that quotient with `[mu.IsHaarMeasure]`.
`OrbitClass m a ha mu` is exactly the published unitary-unramified twist
quotient of actual irreducible discrete-series classes modulo this central
subgroup and measure. No spectral finiteness is included in these inputs.

`orbitRepresentative` chooses an actual irreducible admissible object from
the two existing quotient representatives. Its square-integrability follows
by rewriting the discrete-series class property along `Quotient.out_eq`.
`mk_discreteSeriesClass_orbitRepresentative` proves that this chosen object
represents the original orbit. Given any other actual object `pi'`, its
square-integrability proof `hsq` and an equality `hO` of its orbit with `O`,
`orbitRepresentativeMember` extracts actual unitary orbit membership by
`Quotient.exact`. Its value is precisely `pi'`.

`orbitSectionsBaseEquiv` is the published actual-object reindexing between
raw sections centered at the chosen representative and at `pi'`.
`orbitSmoothSectionsBaseEquiv` restricts it using the published smooth
base-change theorem. These maps retain the actual inducing objects and
coefficient values. The smooth map's `_val` law is reflexive equality with
the raw map applied to the underlying section. The imported base-change
proof supplies independence of the realizing character and equivalence;
no such comparison is assumed here.

## Model change and remaining proposition targets

For two `LeviModel p` over the **same** intrinsic triple,
`LeviModel.schemeIso` is the canonical isomorphism obtained from their
all-test representability. `schemeIso_hom_comp` proves compatibility with
the two inclusions. `pointChange` factors through the literal Levi
homeomorphisms; it fixes each ambient point, has proved identity and
composition laws, and `pointChange_eq_map` identifies it with the rational
point map of this scheme isomorphism.

`characterEquiv` is restriction of algebraic characters along that very
isomorphism. Its inverse and additive laws use functorial character
restriction. `normCharacters_characterEquiv` proves equality of the actual
positive characters on the literal Levi, using naturality of the rational
norm and `pointChange_eq_map`. Extensionality then proves
`commonNormKernel_eq` and `unitaryCharacters_eq`.
`unitaryCharactersEquiv` is subgroup congruence for this equality and leaves
each actual continuous character unchanged.

`representativeModelEquiv` retains each actual inducing object and only
changes its orbit-membership proof. `orbitSectionsModelEquiv` reindexes
accordingly and preserves every actual coefficient value. Its evaluation,
identity and composition laws are proved, and
`orbitSectionsModelEquiv_coherent_iff` preserves and reflects coherence by
applying the original law to the same objects and inducing equivalence.
For a fixed literal central subgroup `C`, normality, centrality proof,
quotient measurable space and Haar measure `mu`, `orbitClassModelEquiv`
compares the two orbit relations on that same `DiscreteSeriesClass`.
Its constructor law fixes each such class. It does not compare different
quotient measures.

The following four declarations are unproved `def ... : Prop` targets.
Their common parameters are `F`, `[Field F]`, `S`, `G`, `i`,
`[TopologicalSpace F]` and `[IsAffineHom G.X.hom]`. The table specifies every
additional parameter or premise; none assumes its conclusion.

| Declaration | Additional parameters/premises and exact obligation |
| --- | --- |
| `ProjectionContinuityStatement` | Parameter `[ValuativeRel F]`; explicit premises `IsNonarchimedeanLocalField F`, `IsConnectedReductive G` and `IsMaximalSplitTorus i`. Under those premises, for every intrinsic `p`, continuity of `(decomposition p).projection`. |
| `CompactDataExistenceStatement` | Parameter `[ValuativeRel F]`; the same three explicit local-field, connected-reductive and maximal-split-torus premises. Under those premises, for every intrinsic `p`, `Nonempty (CompactData p)`, including projection continuity and actual compact-open factorization. |
| `ModelSmoothComparisonStatement` | Parameters `[ValuativeRel F]`, `[IsNonarchimedeanLocalField F]` and `[LocallyOfFiniteType G.X.hom]`, with independent representation universe `uV`. For every `p`, models `m n`, compact data `d e`, actual irreducible admissible `pi` and raw section `q`, membership of `m.orbitSectionsModelEquiv n pi q` in `smoothOrbitSections n e pi` is equivalent to membership of `q` in `smoothOrbitSections m d pi`. It has no smoothness premise or ambient reductivity premise; the supplied models and compact data retain their own defining properties. |
| `SplitCenterChoiceIndependenceStatement` | No additional parameters. For every `p`, models `m n`, commutative group schemes `A B` and split-component morphisms into the respective models, equality of their actual split-center point images in `levi p`. The models themselves supply connected reductivity. |

The first two targets explicitly restrict the proposed geometric existence
and continuity results to Waldspurger's source setting. In particular,
`CompactData` alone does not impose the local-field or ambient
connected-reductivity restrictions; these are explicit premises of its
existence target. The latter two compare already supplied models and compact
data, and retain the broader scopes shown in the table. No local-field or
finite-type hypotheses are implicitly claimed for the fourth target.

The first two require geometric/topological projection and Iwasawa
arguments. The third still requires comparison of the canonical rational
coordinates and compact-picture choices; equality of actual character
subgroups and raw coherent spaces alone does not prove it. The fourth
requires geometric uniqueness/transport of split components. These proof
routes explain the remaining obligations; no proof of these targets is
claimed. In particular, model maps are determined by the actual subgroup
identifications, never supplied as arbitrary comparison equivalences.

## Exact standard specialization and source map

The standard section retains `hG : IsConnectedReductive G`,
`hi : IsMaximalSplitTorus i`, a generic cocharacter `nu` with
`hnu : IsGenericCocharacter i nu`, and a finite set `I` of its simple roots.
`standardIndex` is `SemistandardSpectralIndex.ofStandard` at the existing
root set. `standardLeviModel` uses the existing standard scheme, inclusion,
closed representability and connected reductivity. `standardCompactData`
additionally retains an actual compact open `K`, compactness `hK`, and
`hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) K`; the published
standard projection continuity and factorization discharge its fields.

`standardLeviModel_normCharacters`, `_unitaryCoordinates` and `_splitCenter`
are reflexive equalities with the standard API.
`smoothOrbitSections_standard` is reflexive equality with
`Langlands.HarishChandraSchwartz.rationalInducedSmoothOrbitSections`.
For standard-indexed split components, normality, quotient measurable
spaces and Haar measures, `OrbitClass_standard`,
`orbitRepresentative_standard`, `orbitRepresentativeMember_standard` and
`orbitSectionsBaseEquiv_standard` are reflexive equalities with the existing
standard declarations. `orbitSmoothSectionsBaseEquiv_standard_val` proves
equality of the underlying sections after viewing the same smooth input
through the proved submodule equality. It asserts this value law, not
syntactic equality of the two whole smooth equivalences.

| Source or implementation input | Declarations and status |
| --- | --- |
| I.1, printed pp.238–239: actual semistandard triples | Literal point subgroups, `decomposition`, auxiliary `LeviModel` existence and actual norm/split-center adapters; derived constructions and elementary proofs. |
| VI.1, printed pp.295–296: coefficient sections, coherence, compact-picture smoothness and nontrivial self-twists | `OrbitSections`, `smoothOrbitSections`; specializations of the published actual normalized product-induced section construction. |
| VI.1 and VI.3, printed p.305: unitary discrete-series orbits for each parabolic | `OrbitClass`, chosen representatives, membership and actual raw/smooth representative changes. |
| All-test representability and published norm naturality | Canonical model maps and elementary character, raw-section and fixed-measure orbit-class comparison laws; derived content. |
| Rational realization of the source's structural choices | The four explicit unproved proposition targets above. |
| `RationalStandardSpectralFamily` | Exact standard model, section, orbit, representative and base-change comparisons proved here. |

The induction normalization is inherited from the published full-parabolic
positive Haar half-character construction. This module adds no comparison
with a different normalization convention or manifold-valued smoothness
definition. It introduces no Fourier-family finiteness, intertwiner
invariance, synthesis, weighted inner-product or Plancherel assertion.
