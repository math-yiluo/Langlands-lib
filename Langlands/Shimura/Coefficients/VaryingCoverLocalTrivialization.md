# Compatible local trivialization on a fixed source cover

Author: Worker 13.

This module constructs an isomorphism of whole associated-sheaf diagrams
after restricting them to a fixed source cover. Its components are invariant
evaluation along the actual cover maps. It proves compatibility with the
original coefficient transitions and naturality in the entire coefficient
diagram.

## Provenance and inputs

This is an internal categorical construction from the published
[VaryingCoverInverse](VaryingCoverInverse.md),
[CrossCoverEvaluation](CrossCoverEvaluation.md), and
[TorsorSectionSplittingProof](TorsorSectionSplittingProof.md).
It assembles their actual maps and proved isomorphisms. No new assertion is
attributed directly to external literature, and no imported declaration or
its Markdown is changed.

Fix `X : Scheme.{u}`, a commutative ring `R : Type u`, an index category
`I : Type uI` with `Category.{vI} I`, and `D : I ⥤ GrpCat.{u}`. The
scheme, ring, coefficient-module carriers and groups share universe `u`;
the two index universes are independent. The geometric input is
`Y : EquivariantDiagram D X.Etale`, with
`hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i)`.
Each term is an actual etale object with a group action. The predicate
requires a finite group, finite surjective structure morphism and unique
transport of geometric lifts, as defined in [Etale](Etale.md).
The coefficient input is
`M : EquivariantDiagram D (ModuleCat.{u} R)`.

Write `J = Scheme.smallEtaleTopology X`, `Y_i = Y.obj.obj i`,
`M_i = M.obj.obj i`, and `F_i = (etaleAssociatedAt X Y i).obj M`.
Thus `F_i` is the invariant sheaf constructed from the constant coefficient
representation at `i`. Write `L_Z = J.overPullback (ModuleCat R) Z`.
The constant sheaf in this module is always formed on the original site
and then restricted by `L_Z`. No identification with an independently
formed constant sheaf on the slice site is used.

## Evaluation and the transition equation

The preliminary `coverPullback_productEvaluationAlong` is more general:
`C : Type w` has `Category.{v} C` and binary products, `J` is any
Grothendieck topology on it, and `R : Type u` is a commutative ring.
For `a : T → Z`, `b : Z → Y` and a module sheaf `F`, it proves

```text
L_T.map (coverPullback J b F) ≫ productEvaluationAlong J a F
  = productEvaluationAlong J (a ≫ b) F.
```

At `U : Over T`, the two restriction maps are induced by
`b × identity` and the graph of `U.hom ≫ a`. Their composite is the graph
of `U.hom ≫ a ≫ b`. The proof uses the sheaf functor's contravariant
composition law and the binary-product identities. This lemma has
independent site and coefficient universes.

For the small-etale data, `etaleAssociatedEvaluationAlong M i a`, where
`a : Z → Y_i`, maps `L_Z(F_i)` to `L_Z(constantSheaf(M_i))`. It first
restricts the invariant inclusion, then evaluates at the chosen lift.
Its definition specializes `associatedEvaluationAlong` to the sheafified
coefficient action. The lemma `_natural` is naturality for a morphism
`c : M → N` of whole equivariant coefficient diagrams; it specializes
`associatedEvaluationAlongNat` to the component at `i`.

Let `f : i → j`, and let `τ_f` be the already constructed
`etaleAssociatedTransition`. The theorem
`etaleAssociatedTransition_evaluationAlong` proves

```text
L_Z.map (τ_f.app M) ≫ eval_j(a ≫ Y.obj.map f)
  = eval_i(a) ≫ L_Z.map (constantSheaf.map (M.obj.map f)).
```

This is an equation for the actual varying-cover transition, which is
coefficient reduction followed by the inverse of the proved cover
comparison. The proof applies `L_Z` to the published invariant-inclusion
equation for `τ_f`, then composes with product evaluation. The product
lemma above and naturality in the coefficient sheaf give the displayed
equation. No compatibility of an independently chosen isomorphism is
assumed.

## A diagram on one fixed source cover

Fix `k : I`. An object of `Under k` is an arrow `k → i`; a morphism is
an arrow `i → j` whose triangle commutes. Define two functors with common
codomain `Sheaf (J.over Y_k) (ModuleCat R)`:

- `etaleAssociatedSourceSystem k M` restricts the varying associated
  system along `Under.forget k`, then applies `L_(Y_k)`.
- `etaleConstantSourceSystem k M` restricts the underlying module diagram
  along the same forgetful functor, forms constant sheaves on `J`, and
  applies the same localization.

`etaleAssociatedSourceEvaluation k M` is a natural transformation between
them. At `i : Under k` its component is evaluation along
`Y.obj.map i.hom`. Naturality follows from the transition equation:
`Under.w` identifies the composite cover map with `Y.obj.map j.hom`.

For any `a : Z → Y_i`, `etaleAssociatedTrivializationAlong M i a`
makes this evaluation into an isomorphism. It applies
`associatedTrivializationAlongOfSplitting` to
`etaleTorsorSectionSplitting X _ (Y.action i) (hY i) R`, and evaluates
the resulting natural isomorphism at the sheafified coefficient action.
The splitting theorem derives bijectivity of graph restrictions from the
genuine torsor hypothesis. Thus invertibility is proved from geometric
input rather than supplied as a local trivialization field. The `_hom`
lemma identifies its forward map definitionally with evaluation.

`etaleAssociatedSourceTrivialization k M` assembles these isomorphisms
with `NatIso.ofComponents`; its naturality proof is exactly that of
`etaleAssociatedSourceEvaluation`. Its `_hom` lemma identifies the whole
forward natural transformation with that evaluation transformation.

Finally, `etaleAssociatedSourceSystemFunctor k` and
`etaleConstantSourceSystemFunctor k` make the two constructions functorial
in all equivariant coefficient diagrams. Their definitions use the
published associated-system functor, the forgetful functor on coefficient
diagrams and Mathlib's whiskering functors. The natural isomorphism
`etaleAssociatedSourceTrivializationFunctor k` has component
`etaleAssociatedSourceTrivialization k M`; naturality in a coefficient
morphism follows componentwise from
`etaleAssociatedEvaluationAlong_natural`. The final `_app` lemma records
this component formula.

## Scope

The index category need not be filtered or a preorder. Only indices equipped
with an arrow out of `k` occur on this fixed cover. For `I = ℕᵒᵖ`, these
are the exponents at most the exponent underlying `k`. The construction
does not assert that this cover trivializes all larger exponents.

The scheme and compatible finite geometric torsors remain genuine inputs.
This module introduces no new Shimura realization, comparison between slice
sites, cohomology construction, inverse limit, lisse-adic assertion or
commutation of cohomology with a limit. The Harris specialization is in
[HarrisEtaleLocalTrivialization](HarrisEtaleLocalTrivialization.md).

Formal environment: Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. All intrinsic naturality and
invertibility obligations are proved or inherited from the named published
constructions. There are no new axioms or proof holes.
