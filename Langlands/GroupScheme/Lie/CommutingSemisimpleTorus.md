# Commuting semisimple Lie elements in the Lie algebra of one maximal torus

Worker 1296.

This helper module proves three tangent-transport lemmas and one main lemma.
The field `k : Type u` is arbitrary, with any universe and characteristic. It
need not be algebraically closed. All groups are actual group schemes over
`Spec k`. All Lie elements are points of their actual dual-number identity
kernels `lieKernel G k`.

## Transport lemmas

- `Lie.targetMap_comp_apply`: for homomorphisms `f : H ⟶ G` and `g : G ⟶ J`,
  differentiating `f ≫ g` is the same as differentiating `f` and then `g`.
  This is pointwise: `targetMap (f ≫ g) k X = targetMap g k (targetMap f k X)`.
- `Lie.mem_elementCentralizer_of_comp_mono`: let `j : H ⟶ G` be a
  homomorphism whose underlying morphism over the base is a monomorphism,
  and let `Y` be a Lie element of `H`. Let `g` be a point of `H` over a test
  scheme `U`. If `g ≫ j` centralizes `targetMap j k Y` in `G`, then `g`
  centralizes `Y` in `H`. The proof checks the commutation identity after
  composing with `j` and cancels the monomorphism.
- `Lie.mem_elementCentralizerLie_of_mono`: for such a `j`, if
  `targetMap j k Z` lies in the Lie centralizer of `targetMap j k X` in `G`,
  then `Z` lies in the Lie centralizer of `X` in `H`. This is the previous
  lemma applied to the point `Z.val` over the dual numbers.

## Main lemma

`Lie.exists_isMaximalTorus_forall_tangent_of_pairwise` works over any field.
Let `G` be a group scheme over `Spec k` that is smooth and affine, with no
connectedness assumption. Let `l` be a finite list of Lie elements of `G`
with these two properties:

- Every entry is semisimple, `Lie.IsSemisimpleElement G X`.
- `l` is pairwise ordered for the relation "`Z` lies in the Lie centralizer
  of `X`". Formally this is
  `l.Pairwise (fun X Z => Additive.ofMul Z ∈ Lie.elementCentralizerLie G X)`:
  each later entry lies in the Lie centralizer of each earlier entry.

Then there are a commutative group scheme `T` and a maximal torus
`i : T.toGrp ⟶ G` (`IsMaximalTorus i`). Every entry of `l` is
`targetMap i k Y` for some Lie element `Y` of `T`. The statement is
quantified over the list length `n` so that the proof can use induction.

The proof is by induction on the length.

- **Empty list.** The published maximal-torus existence theorem
  `maximalTorusExistence` gives a maximal torus. There is nothing else to
  prove.
- **List `X :: rest`.** Let `c : C ⟶ G` be the chosen closed representative
  `Lie.elementCentralizerGroupι G X` of the all-test centralizer of `X`. The
  published `Lie.smooth_elementCentralizerGroup` shows that `C` is smooth,
  since `X` is semisimple. Let `incl` be the closed inclusion of the identity
  component of `C` into `G`.
  - By the pairwise hypothesis, each entry `Z` of `rest` lies in the Lie
    centralizer of `X`. The published identity
    `SubgroupFunctor.IsRepresentedBy.lie_eq_range_identityComponent` says
    that this Lie centralizer is the tangent image of `incl`. So `Z` has a
    tangent preimage under `incl`; one is chosen with classical choice.
  - The preimages are semisimple, by the published reflection result
    `Lie.isSemisimpleElement_of_closed_subgroup` for the closed subgroup
    `incl`.
  - The preimages satisfy the same pairwise relation in the identity
    component, by `Lie.mem_elementCentralizerLie_of_mono`.
  - The induction hypothesis, applied to the smooth affine identity
    component of `C`, gives a maximal torus `s` there. Every preimage lies in
    the tangent image of `s`.

  The ambient torus is `s ≫ incl`. Three published theorems are used here:
  the published `NilpotentCentralTorusStatement` proof
  `nilpotentCentralTorusStatement`, `unipotentSemisimpleStatement`, and the
  Cartan structure proof `cartanStructure`. With these,
  `preservesMaximalTori_identityComponent_elementCentralizer_of_semisimple`
  shows that `s ≫ incl` is a maximal torus of `G`. The published
  `Lie.semisimpleCentralizerTorusFactor` and its theorem
  `Lie.targetMap_semisimpleCentralizerTorusFactor` give a tangent preimage of
  the head `X` in `s`. For an entry of `rest`, the tangent preimage in `s` is
  pushed forward along `incl` by `Lie.targetMap_comp_apply`, which recovers
  the original entry.

The relation is asked for only in list order. This way the proof never needs
symmetry of Lie centralization.

## Provenance

This is a derived, internal lemma used in the proof of
`SemisimpleMaximalTorusLieCentralizerStatement` (see
`Lie/TorusLieCentralizerProof.md`). It is a finite-list form of the
iterated-centralizer argument sketched as the intended route in
`Lie/TorusLieCentralizerStatements.md`, after Borel, *Linear Algebraic
Groups*, Proposition 11.8. The Lean proof takes one centralizer at a time.
The direct list-induction argument uses the published smoothness and
maximal-torus preservation results for semisimple centralizers. It makes
no direct conjugacy call and needs no algebraic closure of the field.
The imported `cartanStructure` proof does use maximal-torus conjugacy
transitively; this is not a claim of independence from conjugacy.
