# Geometric-lemma K0 expansion on the actual rational-point family

`Langlands.Aubert.General.RationalPointFamily.RationalGeometricK0ExpansionStatement`
is the unproved actual rational-point target for Aubert 1995, identity (1.3),
printed p.2181 / PDF p.3. It specializes the published
`General.GeometricK0ExpansionStatement` and its actual normalized intersection
terms. It constructs no new geometric filtration and proves no expansion.

## Exact families and indexing

The quantifiers range over a nonarchimedean local field `k`, a connected
reductive group scheme `G`, an actual maximal split torus `i : T → G` and
a generic cocharacter `ν`. The ambient group is `RationalPoint k G.X`
with the canonical evaluation topology `pointTopology`. Local compactness,
the nonarchimedean-group property and Hausdorffness of this topology remain
explicit premises.

The root labels are literally `SimpleRoot i ν`. The families `parabolic`,
`levi` and `unipotent` evaluate the published standard subgroup functors
at the exact character subset `rootSet i ν I`. Their ambient semidirect
decompositions are derived by
`isSemidirectDecomposition_of_standardCocharacterStatement` from
`StandardCocharacterStatement`; no arbitrary replacement families or
decompositions are supplied.

`HasRelativeRootSystem i` supplies the finite simple-root enumeration.
The finite Weyl group is `Weyl i = N(torusPoints i)/Z(torusPoints i)`,
with its full-centralizer denominator. The distinct normalizer and
centralizer point comparisons `hN` and `hZ`, the Coxeter system on this
actual quotient and these literal labels, `RootLengthComparison`,
`PositiveSimpleReflectionComparison` and
`actualLeviWeylIdentification (torusPoints i) (levi i ν) cs` are all
visible inputs. The last input identifies every generated standard
Coxeter subgroup with the image of the actual Levi Weyl quotient.
Supplying this indexing proves neither its root comparisons nor the
geometric expansion.

## Separate prerequisites and the equation

The standard unipotent and parabolic subgroups are assumed closed,
their derived Levi projections continuous, and the unipotent subgroups
limits of compact subgroups. Separate finite-length-preservation premises
for actual normalized induction and actual normalized Jacquet restriction
are retained. `standardParabolicFiniteLength` derives the required
finite-length short-exact preservation from the published exactness
theorems and these topological inputs. All actual standard Levi point
subgroups are also assumed closed. Representation carriers use the
saturated universe `max (u + 1) v`.

`hGeom` is the separately named `GeometricIntersectionDecompositions`
for these exact families. For every minimum representative `w` and every
normalizer lift `n` of `w`, it asserts only the source and target
semidirect decompositions:

| Role | Source inside `L_J` | Target inside `L_I` |
| --- | --- | --- |
| Parabolic | `L_J ∩ n⁻¹ P_I n` | `L_I ∩ n P_J n⁻¹` |
| Levi | `L_J ∩ n⁻¹ L_I n` | `L_I ∩ n L_J n⁻¹` |
| Radical | `L_J ∩ n⁻¹ U_I n` | `L_I ∩ n U_J n⁻¹` |

`hTermFl` is a separate representation-theoretic premise for each such
representative and lift. It requires both finite-length and finite-length
short-exact preservation for the actual source Jacquet functor and
actual target induction functor. Conjugation preservation is already
provided by the published continuous-equivalence pullback results.
Neither premise contains the desired class equality.

The target equation is

`r_I ∘ i_J = ∑_(w ∈ D(I,J)) i_(target,w) ∘ Ad(n_w) ∘ r_(source,w)`.

Here `D(I,J)` is the finite subtype of actual minimum representatives,
and every section `w ↦ n_w` of the actual normalizer quotient is
quantified. The right-hand maps are the published `geometricTermK0`
of the literal intersections above. The source-to-target subgroup
map is forward conjugation by `n_w`; the representation action after
transport is `σ(n_w⁻¹ x n_w)`. The left side is the actual
`jacquetK0` composed with the actual `inductionK0`. No free term
endomorphisms, arbitrary relabeling or chosen expansion witness occur.

## Source and retained proof obligations

This is a derived specialization of registered original
`aubert-1995-duality`, SHA256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`,
printed p.2180 / PDF p.2 for the double-coset conventions and
identity (1.3) on printed p.2181 / PDF p.3. The actual subgroup,
functor, topology and exact-K0 constructions are reused from the published
general adapters. The universal rational-point specialization is internal;
it is not a claim that the source proves those Lean prerequisites.

There is no splitness, quasisplitness, characteristic-zero or positive-rank
restriction. The finite label set may be empty. The full centralizer
remains the denominator; no identification with the split torus is made.

Worker 165 authors this specialization. The actual normalized functor/K0
adapters retain Worker 23's ownership; the geometric filtration and
orbit-functor comparisons retain Worker 14 and the Renard owners.
The parent task `46df6a68-5db4-4428-8044-05151d6ce1f6` owns the
focused proof successor and final assembly. Its proof must specialize
the actual geometric filtration, identify the graded pieces with the
displayed normalized intersection composites, and apply
`SmoothRep.filtrationGrothendieckStatement`. The orbit inversion,
both Haar correction twists, modulus and half-modulus comparisons,
smooth realization and any compact-induction/full-induction comparison
remain obligations. These representation-theoretic assertions and all
finite-length premises are outside the parent's permitted final external
Chapter V structural boundary. The structural intersection premise
is visible and is not added to that boundary by this target.
No classification-independence claim is made. Proposition 3.2
remains unused and unresolved.
