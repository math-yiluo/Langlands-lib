# Strong socles in nonzero Artinian subobjects

Author: Worker 357.

This internal construction returns an actual injective intertwiner from a
supplied strong irreducible socle into any nonzero Artinian representation
embedded in its ambient representation. It is a generic algebraic prerequisite
for later embedding constructions.

## Interface and universes

All declarations are in `Langlands.Classification`. Fix an arbitrary group
`G : Type uG`, three complex vector spaces `V W U : Type uV`, and actions
`ρ : Representation ℂ G V`, `π : Representation ℂ G W`, and
`σ : Representation ℂ G U`. The group universe `uG` and common carrier universe
`uV` are independent. The published strong relation
`h : IsIrreducibleSocle ρ π` includes irreducibility of `π`, an injective map
into `ρ`, and equality of the images of every irreducible embedding into `ρ`
whose source has carrier in `Type uV`.

Given `[Nontrivial U]`, an Artinian group-algebra module
`hσ : IsArtinian (MonoidAlgebra ℂ G) σ.asModule`, and an actual injective
intertwiner `i : σ.IntertwiningMap ρ`, the definition
`IsIrreducibleSocle.artinianSubobjectEmbedding h hσ i hi` returns

```lean
{j : π.IntertwiningMap σ // Function.Injective j}
```

The ambient representation and supplied socle need no Artinianity or finite
length hypotheses. There is no topology, smoothness, admissibility or finite
vector-space dimension premise. All three carriers remain in `Type uV`; the
construction does not resize universes.

`IsIrreducibleSocle.finiteLengthSubobjectEmbedding h hσ i hi` has the same
output and other premises, with
`hσ : IsFiniteLength (MonoidAlgebra ℂ G) σ.asModule` supplying the Artinian
condition. The length here is length over the actual group algebra.

Both definitions are noncomputable chosen maps. Their interface asserts
injectivity; it specifies no preferred atom or naturality law.

## Implemented construction

Install `hσ` as a local instance. The carrier of `σ.asModule` is definitionally
`U`, so `[Nontrivial U]` also gives nontriviality of this module and of its
submodule lattice. Mathlib defines Artinianity as well-foundedness of strict
submodule inclusion. The instances for well-founded lattices give atomicity,
and `IsAtomic.exists_atom` supplies an atom `N` of
`Submodule (MonoidAlgebra ℂ G) σ.asModule`.

The order isomorphism
`Subrepresentation.subrepresentationSubmoduleOrderIso` takes its inverse
image `S`, an atom of the actual subrepresentation lattice of `σ`.
`FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom S hS`
proves that `S.toRepresentation` is irreducible. This generic published lemma
identifies the module underlying the restricted action with the corresponding
simple group-algebra submodule. The normal-subgroup and Clifford results later
in its source module are not used by this construction.

Let `jS : S.toRepresentation.IntertwiningMap σ` be the actual subtype
inclusion. Its injectivity is `Subtype.val_injective`. Compose it with `i` to
obtain an injective map `jρ` into the ambient action `ρ`. The published
`h.socle_eq` identifies the image of `jρ` with the canonical socle of `ρ`.
Thus `socleEquivOfInjective` gives an equivalence
`eS : S.toRepresentation.Equiv (socleRepresentation ρ)`.
The published `h.nonempty_socleEquiv` also supplies
`eπ : π.Equiv (socleRepresentation ρ)`. The returned map is

```lean
jS.comp (eπ.trans eS.symm).toIntertwiningMap
```

The equivalence maps `π` to `S.toRepresentation`; its composite with the
subtype inclusion is injective. This proves that the output subtype is
nonempty. `Classical.choice` then chooses an element of that subtype, so no
existential proof is eliminated directly into data.

The finite-length adapter applies
`isFiniteLength_iff_isNoetherian_isArtinian` and uses its Artinian component
in the first constructor. It preserves the actual map and injectivity in the
output subtype.

## Provenance and existing interfaces

Provenance is internal algebra from the published canonical-socle
constructions, the generic atom-to-irreducible lemma of
`Category.FiniteIndexRestriction`, and Mathlib's Artinian lattice instances and
finite-length comparison. No original-literature assertion is introduced.
The construction proves an actual-map interface from supplied strong socle
data and supplied Artinianity.

A search of the current Library found no existing constructor with this
interface. `CanonicalConstituents` supplies the two equivalences used here but
requires an irreducible embedding for the comparison. The Artinian source
supplies that embedding. `StrongIndecomposabilitySocleProof` extracts a unique
atom and proves a strong-socle existence criterion for its own ambient module;
it does not return the present injection into a separately embedded Artinian
source. Its proof is not imported. The finite-length irreducible extraction
in `Smooth.RenardIrreducibleExistenceProof` uses categorical length and also
does not supply this actual map. The segment-specific support intermediates
are not dependencies.

## Dependency and independence audit

The four direct imports are `Classification.CanonicalConstituents`,
`Category.FiniteIndexRestriction`, `Mathlib.RingTheory.Artinian.Module`, and
`Mathlib.RingTheory.FiniteLength`.

Traversing every project import recursively gives the 15 project modules
listed below, including this module, and the 23 external frontier imports
listed afterwards. Every inherited Lean/Markdown pair is byte-identical to
the supplied Library `644c9c5acc50278ca87d41fcd00bb81216c3e80d`. No project
import or paired Markdown is missing. The code scan found no proof holes,
new axioms or prohibited evaluation mechanisms. The body audit checked the
strong relation's actual image uniqueness, the canonical socle equivalences,
the atom-to-irreducible construction, Artinian atomicity and the finite-length
comparison used above. The remaining inherited modules provide generic
category, smooth subquotient, representation equivalence, lattice and twist
infrastructure. The Weil-named modules in this closure include generic
representation-equivalence invariance, with no GL classification input.

This closure contains no segment module, derivative or mirabolic module,
Jacquet theorem, ordered multisegment theorem or classification conclusion.
It is independent of all exclusions of host task
`8364e73f-14ec-4d14-8f2b-1555a7c1ce95`: parent uniqueness
`30341ae4-65f2-4a0e-9283-763db01a409e`, multisegment exhaustion
`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`, ordered strong-head existence
`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`, quotient coverage
`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`, ordered conversion
`8252833d-c269-41a9-824c-5879e531b23b`, tempered uniqueness
`52e97845-36bb-457d-b76f-70753334b88c`, square-integrable classification
`1cb45da2-7007-4351-a694-594fb148b8d1`, square-integrable exhaustion
`cd8ab97c-0b78-4bce-97c4-d307a28159a4`, regular exhaustion
`bf433f0a-921a-428c-b0c0-6475438125ac`, their conclusions and proof successors,
and the segment-socle part of `8e5b4563-0365-41c7-b134-70f2a0b36292`.

The same inventory excludes Ze80 3.5/9.6 and their proof successors and all
restricted segment, head, socle and full Jacquet formulas under the operator
responses `bd71b9185aab5d6eafffb7891bd3a3ca`,
`0edda6122ce65ed7ac51603c37473920` and
`30144f6f9b59540b88b6d4c1517892d9`. The generic strong-socle relation and its
algebraic canonical-object tools are the lower definitions used here. Neither
the support-only bound nor its restricted length-two `core_mid` step nor the
adjacent-supercuspidal reducibility exception of responses
`ed80148e21e7523abfc048f455e98eb0`,
`2b33898bdd0a5ff1b9031be5155a06f0` and
`ca18fd5005bf5e12a3f7cade18dca865` enters this construction.

The host's special-head product irreducibility equivalence remains a separate
proof obligation. This module supplies neither an embedding of a particular
head nor derivative nonvanishing; a consumer must first provide the strong
socle, a nonzero Artinian source and its actual ambient injection.

### Complete project import inventory

```text
Langlands.Representation.Category.Basic
Langlands.Representation.Category.FiniteIndexRestriction
Langlands.Representation.Category.Subquotients
Langlands.Representation.Classification.ArtinianSocleEmbedding
Langlands.Representation.Classification.CanonicalConstituents
Langlands.Representation.Classification.ConstituentRelations
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.SubrepresentationLattice
Langlands.Representation.Twist.Definitions
Langlands.Weil.Representation.Basic
Langlands.Weil.Representation.Determinant
Langlands.Weil.Representation.IsomorphismInvarianceProof
Langlands.Weil.Representation.Operations
```

### Complete external import frontier

```text
Mathlib.Algebra.Module.Submodule.Map
Mathlib.Analysis.Complex.Basic
Mathlib.Basic.Complex.Basic
Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
Mathlib.CategoryTheory.Skeletal
Mathlib.GroupTheory.Index
Mathlib.GroupTheory.Subgroup.Center
Mathlib.LinearAlgebra.Determinant
Mathlib.LinearAlgebra.Dimension.Constructions
Mathlib.LinearAlgebra.FiniteDimensional.Defs
Mathlib.Order.CompactlyGenerated.Basic
Mathlib.RepresentationTheory.Intertwining
Mathlib.RepresentationTheory.Invariants
Mathlib.RepresentationTheory.Irreducible
Mathlib.RepresentationTheory.Rep.Basic
Mathlib.RepresentationTheory.Semisimple
Mathlib.RingTheory.Artinian.Module
Mathlib.RingTheory.FiniteLength
Mathlib.RingTheory.Finiteness.Basic
Mathlib.RingTheory.SimpleModule.Basic
Mathlib.Topology.Algebra.Group.Basic
Mathlib.Topology.Algebra.Module.ModuleTopology
Mathlib.Topology.Algebra.OpenSubgroup
```
