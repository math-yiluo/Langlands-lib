# Profinite local reciprocity

Worker 10 authored this proposition family. It defines the local profinite
reciprocity assertions for later proof tasks. Its construction imports,
including Completion and FiniteArtin, are published in the current Library.
Compilation of these proposition definitions does not prove local reciprocity.

## Objects and quantifiers

Every target quantifies over every prime, every actual finite extension
`PadicField.{u} p`, and every compatible `TopologicalData T`. The carrier
universe remains arbitrary. The original topology on `F.Carrier` is exactly
`T.topology`; the topology on its units is Mathlib's units topology.
The accepted `Langlands.PadicField.canonicalTopologicalData`
construction in `Langlands.LocalField.Canonical`
supplies data for every such algebraic field. The all-fields obligation is
therefore the existing canonical realization, not an additional restriction
to fields with a postulated reciprocity system.

The target group is Mathlib's
`Field.absoluteGaloisGroupAbelianization F.Carrier`, the actual absolute
Galois group with its Krull topology divided by the closure of its commutator.
`LocalMultiplicative.profiniteCompletion T` is Worker 21's closure of the
diagonal image in the product of the actual open finite quotients. Its map
`completionMap T` uses the original topology. Neither object is an abstract
group supplied by the theorem's hypotheses.

`LocalFiniteAbelianExtension F` consists of actual finite abelian intermediate
fields in `AlgebraicClosure F.Carrier`. Finite restrictions are the actual
restrictions of automorphisms, descended to the closed-commutator quotient.
The norm in `ProfiniteNormResidueRelation` is the image of
`Units.map (Algebra.norm F.Carrier)`.

## Exact assertions

`GeometricProfiniteReciprocityRelation F T r` is a predicate on a candidate
continuous homomorphism. It combines the existing unnormalized relation
(density, exact finite norm kernels, surjective finite components, and
restriction compatibility) with the following normalization. For every finite
abelian extension `L`, every compatible local-field realization `S` of `L`,
every `a` with additive order one, and every integral `x` in `L`, the inverse
of the automorphism attached to `a` takes `x` to `x^q` modulo the maximal
ideal, where `q` is the residue cardinality of the base. The inequality
`S.discreteValuation (sigma.symm x - x^q) < 1` expresses this congruence using
the actual valuation. Thus the map sends uniformizers to geometric Frobenius
on every residue extension. It neither chooses a Frobenius lift nor treats
a ramified finite Galois group as cyclic.

`LocalFiniteIndexSubgroupsOpen` states the characteristic-zero local-field
fact that every subgroup of finite index in the multiplicative group is open.
It does not silently use this fact to construct a continuous map.

`ProfiniteReciprocityExistenceUniqueness` asserts that there exists exactly one
continuous `r` satisfying the normalized relation. Existence is the
conclusion, not a typeclass, supplied certificate or premise.

`ProfiniteReciprocityCompletion` states, for every map satisfying that
relation, injectivity on `F^\times` and the existence of exactly one continuous
group isomorphism from the actual profinite completion to the absolute-Galois
abelianization whose restriction along `completionMap T` is `r`.
`F^\times` itself is not identified with a compact group. The conditional
consequence occurs alongside the unconditional existence assertion in the
aggregate target.

`ProfiniteReciprocityCharacterTransport` states that a continuous complex
character of `F^\times` has finite image if and only if it is the composite
with `r` of exactly one continuous complex character of the profinite
abelianized Galois group. This deliberately does not include arbitrary
quasicharacters in the profinite target. Their transport belongs to the
separate Weil formulation.

`ProfiniteReciprocityNormFunctoriality` states the norm diagram for every
finite extension `E/F`, including non-Galois extensions. The independent
carrier universes are `u` and `v`. The compatible embeddings of the actual
algebraic closures are quantified explicitly. The norm goes from
`E^\times` to `F^\times`, and the induced map on absolute-Galois
abelianizations also goes from `E` to `F`. The two composites agree for
any normalized reciprocity maps. Finite dimensionality over `F` follows
from the compatible finite `Q_p` tower in the norm constructor. Thus the
only diagrams postulated are conclusions about the actual maps; no
reciprocity diagram is supplied as data.

`ProfiniteReciprocityTransferFunctoriality` states the opposite diagram:
field inclusion from `F^\times` to `E^\times` corresponds to transfer
from the base absolute-Galois abelianization to the extension's.
The subgroup `H` is the actual image of the specified
`Field.absoluteGaloisGroup.mapOfAlgebra`. Finite index and a continuous
group isomorphism `j` from the extension Galois group onto that actual
subgroup are existential conclusions. The equation `(j g).val = i g`
pins the isomorphism to the given Galois map.

The continuous map `tr` between the abelianized groups is also a conclusion.
Its value after the surjective base abelianization projection is required
to equal Mathlib's `MonoidHom.transfer` of the composite
`H -> G_E -> G_E^ab`, where the first arrow is `j.symm`. Thus `tr` is
fixed by the genuine coset-product transfer independently of the
reciprocity diagram. It is not an arbitrary map chosen to satisfy that
diagram. The inverse used here identifies an actual subgroup with its
source group; no inverse into an unabelianized Weil group is introduced.
The field extension need not be Galois, and `H` need not be normal.

This formulation pins transfer directly to its coset-product definition.
Its finite-index, subgroup-identification, and continuous-descent conclusions
remain proof obligations. The construction companion module
`Langlands.ClassFieldTheory.Local.Transfer` (formerly
`Langlands.LocalClassField.Transfer`) is also published; its certified
constructors can be used in a later proof of these assertions.

`ProfiniteReciprocityTheorems` is the conjunction of these six theorem
statements. No component is proved in this module. The Weil isomorphism
and ramification/conductor transport remain separate statement obligations.
Pointwise unique existence together with the norm and transfer assertions
for every normalized pair yields a coherent system across finite extensions;
there is no need to assume a globally chosen system as input.

## Original-source correspondence and derived uniqueness

Jean-Pierre Serre, *Local Fields*, English translation, GTM 67 (1979):

- XI.3, printed 169-171 / PDF 175-177, constructs the reciprocity maps,
  characterizes them using the invariant pairing, gives the four
  functoriality diagrams, and passes to compatible finite restrictions.
  Diagram (1) and its inverse-limit form give the norm assertion, without
  requiring the extension between the two base fields to be Galois.
  Diagram (2) and its inverse-limit form give scalar inclusion versus
  transfer. VII.8, Propositions 7-8, printed 121 / PDF 127, gives the
  finite-index coset-product description used by Mathlib's transfer.
- XI.4-5, printed 172-175 / PDF 178-181, identifies the completion for the
  norm topology with the abelian Galois group.
- XIII.4, Propositions 8 and 13 and their corollaries, printed 196-198 /
  PDF 201-203, supplies the finite norm-residue isomorphism and arithmetic
  Frobenius normalization. We invert the reciprocity values consistently
  to obtain geometric normalization.
- XIV.4, Exercise 2, printed 214 / PDF 219, states that finite-index
  subgroups are closed in characteristic zero. A closed subgroup of finite
  index is open, since its complement is a finite union of closed cosets.
- XIV.6, Theorem 1, Corollaries 1-2 and Remark 1, printed 218-219 /
  PDF 223-224, identifies norm groups with open finite-index groups and
  shows that their intersection is trivial. This identifies the source's
  norm-topology completion with the implemented open-finite-quotient model.

The uniqueness characterization used here is a derived consequence of these
finite results, rather than a verbatim theorem from Serre. Two candidate maps
give, on every finite abelian quotient, an automorphism comparing their
surjective maps with equal norm kernels. Compatibility with all intermediate
fields makes this comparison preserve every subgroup of the finite quotient.
Enlarge any given finite abelian extension by an unramified extension of
degree divisible by its group exponent. The residue normalization makes
the comparison the identity on the unramified quotient. Each element
projecting to a generator of that cyclic quotient is fixed: preservation of
its cyclic subgroup writes its image as a power, and the unramified
coordinate forces that power to be one modulo the chosen degree, hence
modulo the exponent of the whole compositum group. Such elements generate
the compositum group, since their pairwise quotients generate the inertia
kernel. Consequently the comparison is the identity on the original finite
quotient, and all finite restrictions separate points of the actual
profinite Galois group. This uses existence of unramified extensions of
arbitrarily divisible degrees as an ordinary local-field theorem; it does
not assume a chosen global Frobenius lift.

Uniqueness of the extension to the completion follows from density and
Hausdorffness. The finite-character consequence is derived from the same
finite quotients: a continuous finite-image character has an open finite-index
kernel and hence descends through its corresponding norm quotient. In the
other direction, a continuous complex character of a profinite group has
finite image. One may use that the complex unit group has a neighborhood
of one containing no nontrivial subgroup, so its continuous character has
open kernel. This is a topological consequence, not an assertion that every
quasicharacter has finite image.

Worker 10 read all the cited original passages. Registered source
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
retained at `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.

## Declaration and dependency map

The pinned environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

| Declarations in this pair | Published constructions used | Source above |
| --- | --- | --- |
| `GeometricProfiniteReciprocityRelation`, `ProfiniteReciprocityExistenceUniqueness` | `ProfiniteNormResidueRelation` and `finiteFamilyOfHom` in namespace `Langlands.LocalClassField`, actual `LocalFiniteAbelianExtension`, normalized order and residue cardinality | XI.3, XIII.4, and the derived uniqueness argument |
| `LocalFiniteIndexSubgroupsOpen` | `PadicField`, `TopologicalData`, actual multiplicative subgroup and index | XIV.4 Exercise 2 |
| `ProfiniteReciprocityCompletion` | `LocalMultiplicative.profiniteCompletion`, `completionMap`, actual absolute-Galois abelianization | XI.4-5 and XIV.6 |
| `ProfiniteReciprocityCharacterTransport` | continuous complex unit-valued homomorphisms, finite norm quotients | Derived from XI.3 and XIV.6 |
| `ProfiniteReciprocityNormFunctoriality` | `localNorm`, `absoluteAbelianizationMap` | XI.3 diagram (1) |
| `ProfiniteReciprocityTransferFunctoriality` | actual `Field.absoluteGaloisGroup.mapOfAlgebra`, `absoluteAbelianizationProjection`, Mathlib `MonoidHom.transfer`, `localInclusion` | VII.8 and XI.3 diagram (2) |
| `ProfiniteReciprocityTheorems` | The six assertions just listed | Their conjunction |

The imported project modules are `Langlands.ClassFieldTheory.Local.Completion`,
`Langlands.ClassFieldTheory.Local.FiniteArtin`, and
`Langlands.LocalField.Normalization.Definitions`. The first two were
published at `Langlands.LocalClassField.Completion` and
`Langlands.LocalClassField.FiniteArtin`; the module-path consolidation
(pilot task `295b0f1c-439f-4b3e-8c86-14e5bd541262`) moved them to the same
basenames under `Langlands/ClassFieldTheory/Local` and changed only these two
import lines here. The old paths remain as declaration-free re-exports, and
the imported declarations keep their published names. Their Galois, Norms,
and local-field dependencies are ordinary published imports. Their authorship
is retained in their own paired Markdown. All local construction source
pairs were read before use and compared with the current published files.
The all-fields topological realization is
`Langlands.PadicField.canonicalTopologicalData` in
`Langlands.LocalField.Canonical`.

The closing declaration has independent universe parameters `u,v`.
Independent review must check the original-source correspondence as well
as the Lean and Markdown; successful elaboration alone establishes neither
semantic acceptance nor any of the asserted CFT theorems.

## Current development check

Worker 10 rechecked this pair in the current environment with `lean_check`,
using the original `Langlands.LocalClassField` import paths. The entry
module compiled without errors or warnings, and inspection of
`Langlands.LocalClassField.ProfiniteReciprocityTheorems` returned
`statement_returns_prop: true` with independent levels `u,v` and only
`propext`, `Classical.choice` and `Quot.sound`. This checks the statement's
elaboration, not its truth. Independent semantic review and publication
remain required. The retained original's SHA256 and all cited page
locators were checked again against the current readable source.
