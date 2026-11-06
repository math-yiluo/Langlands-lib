# Closed self-embeddings of affine algebraic groups

Worker 1717. This internal development proves that a closed embedding of an affine
algebraic object over a field into itself is an isomorphism. It is support for the
self-intersection analysis of the geometric lemma in the proof of the endomorphism
dichotomy of Renard VI.5.3: a Levi subgroup `M` contained in a conjugate `z M z⁻¹`
of itself must equal that conjugate.

## Declarations

- `Langlands.isIso_of_isClosedImmersion_self`: let `X` be an affine scheme with a
  morphism `X ⟶ Spec k`, `k` a field, that is locally of finite type. Then every
  closed immersion `g : X ⟶ X` is an isomorphism. The structure morphism makes `X`
  locally Noetherian, so the published
  `Langlands.GroupScheme.ImageGeneration.isIso_of_isClosedImmersion_endo`
  applies directly. That theorem uses
  `Langlands.CommutativeAlgebra.FormallySmoothLocalCompletion.injective_of_surjective_endo`
  on the induced surjection of global-section rings.
- `Langlands.GroupScheme.isIso_of_isClosedSubgroup_self`: for a group scheme `M`
  over `Spec k` whose structure morphism is affine and locally of finite type, a
  group-scheme endomorphism `f : M ⟶ M` that is a closed subgroup
  (`IsClosedSubgroup f`, i.e. its underlying scheme morphism is a closed
  immersion) is an isomorphism of group schemes. The underlying scheme morphism
  is an isomorphism by the previous lemma, and the forgetful functors from group
  objects to monoid objects, from monoid objects to the over category, and from
  the over category to schemes reflect isomorphisms.
- `Langlands.GroupScheme.IsConnectedReductive.isIso_of_isClosedSubgroup`: the same
  conclusion for a connected reductive group `M` over `k`, whose smoothness and
  affineness supply the finite-type and affine hypotheses.

## Provenance

Internal. The ring-theoretic lemma is the standard fact that surjective
endomorphisms of Noetherian rings are injective; its scheme and group-scheme consequences are formal from
Mathlib's closed-immersion API and the project's `IsClosedSubgroup` and
`IsConnectedReductive` predicates. No source statement is formalized here.
