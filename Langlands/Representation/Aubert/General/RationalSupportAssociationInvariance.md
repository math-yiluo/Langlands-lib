# Association invariance of the actual support category

Author: Worker 12.

`Langlands.Aubert.General.RationalPointFamily.rationalSupportCategoryAssociationInvariance`
proves the whole, unapplied Library proposition
`RationalSupportCategoryAssociationInvarianceStatement.{u, v}` from
[RationalSupportCategoryTargets](RationalSupportCategoryTargets.md).
The theorem has no parameters outside that proposition. The target and its
imports are preserved.

## Source and scope

The source assertion is the parenthesis immediately following the definition
of `Alg({I})` in Anne-Marie Aubert, *Erratum à « Dualité dans le groupe de
Grothendieck des représentations lisses de longueur finie d'un groupe réductif
p-adique »* (1996), printed p. 4687, PDF p. 1. Registered source:
`aubert-1996-duality-erratum`; content SHA256:
`d76b3ef9ea2310d1a3129da990c1abd6c304027e3e939a5a1f06c666978c145f`.
The supplied original is
`Aubert--Dualite dans le groupe de Grothendieck des representations lisses de longueur finie--1995/Aubert--Erratum a Dualite dans le groupe de Grothendieck des representations lisses--1996.pdf`
in the central literature library. This passage defines the category by all
irreducible subquotients and states that it depends only on the association
class of the Levi. The proof here is an internal transport argument on the
published definitions. It uses neither Proposition 3.2 nor its defective
application in the original paper.

The theorem keeps independent universes `u` and `v`, every nonarchimedean local
field `k`, every connected reductive group scheme `G`, its actual maximal
split torus `i`, and the given generic cocharacter `ν`. The group is literally
`RationalPoint k G.X` with `pointTopology`; its local compactness,
nonarchimedean group structure and Hausdorffness remain the displayed
premises. The labels are the actual `SimpleRoot i ν`, and the subgroup
families are `parabolic i ν`, `levi i ν` and `unipotent i ν`.
Representation carriers have universe `max (u + 1) v`.

The given `hStandard`, `hInter`, `hRoots`, `hN`, `hZ`, `hU` and `hM` are
retained with their original meanings. The proof derives its ambient and
inside-Levi semidirect decompositions from the first two. It derives finite
enumeration and the finite-root bound from `hRoots` and splitness of the
chosen torus. It adds no finite-length, admissibility, finite-generation,
exactness, compactness, endpoint or compact-limit premise. It imposes no
characteristic-zero, splitness or quasisplitness assumption on `G`, and no
nonemptiness condition on its simple roots. In relative rank zero the same
proof applies; there are no proper nested subsets of the empty label set.

## Implemented argument

Write `M_I` for `levi i ν I` and `C_n` for the given conjugation functor,
whose action is `x ↦ σ(n⁻¹ x n)`. Fix the actual `n` in the target,
associating `I` to `I′` and conjugating `M_I` to `M_I′`.
For each irreducible subquotient `π` of `E`, membership of `E` in
`Alg({I})` supplies an associated subset `J`, an actual representative `m`
from `I` to `J`, and an irreducible cuspidal `σ` on `M_I`, with `π` a
subquotient of normalized induction from `M_J` of `C_m σ`.

The new cuspidal datum is `C_n σ` on `M_I′`, and its representative to `J`
is `p = m * n⁻¹`. The inverse and product laws for `rootAssociation` give
the association `I′ → J` with this exact `p`. The private lemma
`conjugation_composite_membership` proves its Levi membership equivalence
from the two supplied equivalences, using

```text
n⁻¹ * (p⁻¹ * x * p) * n = m⁻¹ * x * m.
```

Irreducibility of `C_n σ` follows from invariance under a continuous group
equivalence. The public helper `isLeviCuspidal_conjugation` proves its
cuspidality as follows. For any proper nested subset `K′` of `I′`, pull it
back to a proper `K` of `I` along `rootAssociationEquiv`.
The same point `n` associates these nested faces. The structural helpers
identify their Levis and their radicals inside the two outer Levis under
`conjugationEquiv n hn`. Closedness of the inside radicals is the preimage
of the given `hU` under the subgroup inclusion; closedness of the outer
Levis supplies their local compactness.

`GroupTransport.jacquetIsoApp` then identifies normalized Jacquet
restriction of `C_n σ` at `K′` with the pullback of the normalized Jacquet
module of `σ` at `K`. The latter is subsingleton by the exact
`IsLeviCuspidal` hypothesis. Pullback retains its carrier, and an
isomorphism transfers subsingletonness. The three private helpers
`pullback_subsingleton`, `subsingleton_of_iso` and
`jacquet_subsingleton_transport` isolate this step.

Finally, the identity linear equivalence intertwines `C_m σ` and
`C_p (C_n σ)` by the same group identity above. This is the private
`conjugationCancelIso`. Mapping it through the actual
`normalizedInductionFunctor` for the unchanged `J` and applying
`SmoothRep.IsSubquotient.of_iso_right` transports the original subquotient
witness. No comparison of induction from different parabolics is needed.
The private `supportCategory_conjugation` packages these witness
manipulations for abstract groups; the final theorem instantiates it with
the actual rational-point families and the proved structural and
cuspidality lemmas. Every irreducible subquotient of `E` remains quantified.

## Declaration dependencies

The following are proof dependencies, rather than additional premises.
Namespaces in the first column are part of the declaration names.

| Declarations | Role and scope actually used |
| --- | --- |
| `Langlands.Aubert.General.RationalPointFamily.rootAssociation_inv`, `rootAssociation_mul` | Published actual inverse and composite normalizer representatives, reused from Worker 78's `RootAssociationComposition`. |
| `Langlands.Aubert.General.RationalPointFamily.exists_associated_nested_subset`, `rootAssociation_levi_membership`, `rootAssociation_nested_unipotent_membership` | Newly proved proper nested-face transport and actual subgroup membership comparisons for the same representative. See [RationalSupportAssociationStructure](RationalSupportAssociationStructure.md). |
| `Langlands.GroupScheme.Dynamic.orbit_add_zsmul_of_mem_centralizer`, `Langlands.GroupScheme.IsStandardCocharacter.exists_add_zsmul_of_nested`, `Langlands.GroupScheme.mem_standardUnipotent_conj_of_mem_standardLevi` | Newly proved all-test-scheme cocharacter and radical transport lemmas. See [NestedStandardTransport](../../../GroupScheme/Rational/NestedStandardTransport.md). |
| `Langlands.GroupScheme.standardLeviConjugationStatement_of_standardCocharacterStatement`; `Langlands.Aubert.General.RationalPointFamily.levi_map_conj_of_character_image` | Deduce nested Levi conjugation from the existing `hStandard`, then convert it to membership. No new Levi-conjugation premise is introduced. |
| `Langlands.Aubert.General.RationalPointFamily.rootAssociationEquiv`, `weylCharacterAction_point_mk` | Compare literal simple-root labels and their actual Weyl character images. |
| `Langlands.GroupScheme.HasRelativeRootSystem.finite_simpleRelativeRoots`, `simpleRelativeRootFintype` | Finiteness of actual simple roots conditional on the given root-system realization and split torus. |
| `Langlands.Aubert.General.RationalPointFamily.isSemidirectDecomposition_of_standardCocharacterStatement`, `isSemidirectDecomposition_in_levi` | Exactly the ambient and inside-Levi decompositions already used by the target. |
| `Langlands.Aubert.General.conjugationEquiv`, `conjugationFunctor`; `Langlands.SmoothRep.pullbackFunctor`, `mkIso`, `equivOfIso` | Actual continuous group transport, smooth pullback and representation isomorphisms. |
| `Langlands.Aubert.General.GroupTransport.jacquetIsoApp`, `subgroupEquiv` | Actual normalized Jacquet comparison for corresponding Levi and radical subgroups; instantiated on the two outer Levis. |
| `Langlands.Jacquet.Localization.transportEquiv`; `Langlands.Aubert.General.GroupTransport.closedInverseHalfCharacter_transport`, `closedRestrictCharacter_transport` | Transitive construction of that comparison: transport of the coinvariant quotient and invariance of the inverse half Haar modulus under the continuous group equivalence. |
| `Langlands.isIrreducible_comp_continuousMulEquiv_iff` | Irreducibility under change of group; used for the conjugated representation. Its proof uses only `Langlands.CuspidalSupport.isIrreducible_comp_of_surjective`, an order isomorphism of invariant-submodule lattices along a surjective homomorphism. |
| `Langlands.Aubert.General.normalizedInductionFunctor`; `CategoryTheory.Functor.mapIso` | Apply the same actual normalized induction functor to the cancellation isomorphism. |
| `Langlands.SmoothRep.IsSubquotient.of_iso_right` | Transports the induction witness. Its proof uses `Langlands.SmoothRep.isSubquotient_iff_exists`, `hom_hom_injective` and `hom_hom_surjective`: elementary range/kernel factorizations and injectivity/surjectivity of isomorphisms. |

The irreducibility lemma is located in
`Langlands.Representation.CompactCoefficient.GroupTransport`, and its
surjective-pullback helper in
`Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof`.
Neither the compact-coefficient conditions nor the tensor-association
theorem is used. The four elementary subquotient declarations in the last
row are located in
`Langlands.Representation.Classification.SupercuspidalSupport` and apply to
arbitrary smooth representations of a topological group over a commutative
ring. They use no `GL_n` classification or cuspidal-support uniqueness
theorem.

A recursive audit of the theorem's declaration types and values, including
theorem bodies and inductive constructors, finds these elementary helpers
in the classification/cuspidal-support modules. It finds no representation
classification, character-independence, geometric-lemma or functor
adjointness theorem in the dependency closure. The reached declarations in
`Langlands.GroupScheme.Lie.Adjoint`, including `Langlands.GroupScheme.adjoint`
and `adjoint_naturality`, concern the algebraic Lie adjoint action used in
the definitions of relative roots.

The loaded import closure is broader than this declaration dependency
closure. It includes `Langlands.Representation.Classification.Segments`,
`FiniteLengthProof`, `FiniteLengthStatement`, `ConstituentRelations`,
`Supercuspidal`, `SupercuspidalTwist`,
`SupercuspidalContragredientAux`,
`SupercuspidalContragredientStatement` and `SupercuspidalSupport`;
it also includes
`Langlands.Representation.Geometric.GeometricLemmaStatement`,
Weyl and refinement modules, cuspidal-support modules and
`Langlands.Representation.Parabolic.NaturalFirstAdjointness`.
Except for the elementary subquotient helpers identified above, declarations
from those classification modules are not reached by this proof. Their
presence as imports does not supply a mathematical premise.
The proof does not invoke Jacquet exactness, an induction group-transport
theorem or a Grothendieck-group identity. The normalization used throughout
is the Library's actual positive half Haar modulus for induction and inverse
half Haar modulus for Jacquet restriction.
