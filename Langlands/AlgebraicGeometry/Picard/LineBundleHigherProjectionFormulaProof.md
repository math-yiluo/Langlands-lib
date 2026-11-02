# Proof of the projection formula for higher direct images and an actual line bundle

Authors: Worker 943, Worker 317.

Module `Langlands.AlgebraicGeometry.Picard.LineBundleHigherProjectionFormulaProof`, namespace
`Langlands.AlgebraicGeometry.Picard`. The theorem `lineBundleHigherProjectionFormula` proves
`LineBundleHigherProjectionFormulaStatement.{u}`: for every scheme morphism `f : X ⟶ Y`,
actual line bundle `L` on `Y`, module sheaf `M` on `X` and degree `n`, there is an
isomorphism

```
tensorObj L.obj ((higherDirectImage f n).obj M) ≅
  (higherDirectImage f n).obj (tensorObj ((Scheme.Modules.pullback f).obj L.obj) M).
```

The isomorphism itself is the definition `lineBundleHigherProjectionIso f L M n`. Imports:
the statement module and `Langlands.AlgebraicGeometry.Picard.LineBundleProjectionFormulaProof`. The derived-functor comparison
`Langlands.Cohomology.DerivedComparison` reaches the file through these imports.

## Two general category-theory definitions

The two categorical constructions are shared with the degree-zero proof
`Langlands.AlgebraicGeometry.Picard.LineBundleProjectionFormulaProof`. Integration
exposed its previously private constructions under the following public names,
with unchanged bodies; both projection proofs now use the same declarations.

- `tensorLeftEquivalenceOfInverse L N e`: in a braided monoidal category `C`, an isomorphism
  `e : L ⊗ N ≅ 𝟙_ C` gives an autoequivalence of `C` whose functor is `tensorLeft N` and
  whose inverse is `tensorLeft L`. The two natural isomorphisms are built from the left
  unitor, `e` (and its braided version `β_ N L ≪≫ e`) and `tensorLeftTensor`;
  `Equivalence.mk` makes the data an equivalence.
- `tensorLeftRightAdjointCommIso F G adj L N e`: for a monoidal functor `F : C ⥤ D` (here
  `Functor.Monoidal`, so with tensor isomorphisms `μIso` and unit isomorphism `εIso`) with a
  right adjoint `G`, it gives `G ⋙ tensorLeft L ≅ tensorLeft (F.obj L) ⋙ G`. The inverse `e`
  is transported to `F.obj L ⊗ F.obj N ≅ 𝟙_ D`; composing the two tensor-inverse equivalences
  with `adj` gives the adjunctions `tensorLeft N ⋙ F ⊣ G ⋙ tensorLeft L` and
  `F ⋙ tensorLeft (F.obj N) ⊣ tensorLeft (F.obj L) ⋙ G`. `Functor.Monoidal.commTensorLeft`
  identifies the two left adjoints and `Adjunction.rightAdjointUniq` identifies the right
  adjoints.

## The higher projection isomorphism

`lineBundleHigherProjectionIso f L M n` is built in these steps.

1. The published `locallyFreeRankOneTensorInvertible` gives a module sheaf `N` on `Y` and an
   isomorphism `e : L.obj ⊗ N ≅ 𝟙_ Y.Modules` for the monoidal structure on `Y.Modules`.
   Write `F` for the actual pullback `Scheme.Modules.pullback f`, which is monoidal by the
   published `PullbackMonoidal`. Transporting `e` through `F` gives
   `F.obj L.obj ⊗ F.obj N ≅ 𝟙_ X.Modules`.
2. By `tensorLeftEquivalenceOfInverse`, both `tensorLeft L.obj` on `Y.Modules` and
   `tensorLeft (F.obj L.obj)` on `X.Modules` are inverse functors of equivalences, so they are
   equivalences (`Equivalence.isEquivalence_inverse`). The proof records these two facts as
   local instances. Both functors are then additive by
   `Functor.additive_of_preserves_binary_products`, because an equivalence preserves binary
   products. The remaining properties are found by instance inference: an equivalence
   preserves finite limits and colimits, hence homology (Mathlib's
   `Functor.preservesHomologyOfExact`), and it preserves injective objects (Mathlib's
   `Functor.preservesInjectiveObjects_of_isEquivalence`). Inference also supplies the
   additivity of `Scheme.Modules.pushforward f` and injective resolutions in `X.Modules` and
   `Y.Modules`, which `higherDirectImage` already uses.
3. `tensorLeftRightAdjointCommIso` applied to `F`, the pushforward
   `Scheme.Modules.pushforward f` and the adjunction
   `Scheme.Modules.pullbackPushforwardAdjunction f` gives the degree-zero isomorphism
   `c : pushforward f ⋙ tensorLeft L.obj ≅ tensorLeft (F.obj L.obj) ⋙ pushforward f`.
4. The published `Langlands.Cohomology.DerivedComparison.rightDerivedCompIso` turns an
   isomorphism `Φ ⋙ P ≅ T ⋙ Ψ`, with `P` preserving homology and `T` preserving homology and
   injective objects, into `Φ.rightDerived n ⋙ P ≅ T ⋙ Ψ.rightDerived n`. With
   `Φ = Ψ = pushforward f`, `P = tensorLeft L.obj`, `T = tensorLeft (F.obj L.obj)` and `c`,
   and since `higherDirectImage f n` is `(pushforward f).rightDerived n`, its component at
   `M` is an isomorphism `L.obj ⊗ Rⁿ f_* M ≅ Rⁿ f_* (F.obj L.obj ⊗ M)` for the monoidal tensor.
5. The published `localizedTensorIso` (`M ⊗ N ≅ tensorObj M N`) on `Y`, and its image under
   `higherDirectImage f n` on `X`, convert both ends to the Library's explicit sheafified
   `tensorObj`.

`lineBundleHigherProjectionFormula` then gives, for each `X Y f L M n`, the witness
`⟨lineBundleHigherProjectionIso f L M n⟩`.

## Relation to the literature

The statement is the rank-one case of The Stacks Project, Cohomology of Sheaves,
Lemma 20.54.2 (tag 01E8), registered source
`stacks-flat-base-change-projection-formula-2026-11-02`. The Lean proof follows the shape of
the Stacks proof: choose an injective resolution of `F`, note that `f^*E ⊗ -` keeps it an
injective resolution (Stacks Lemma 20.54.1), apply `f_*`, and use the degree-zero
projection formula termwise. In Lean, `rightDerivedCompIso` performs this resolution
argument. The fact that tensoring with `f^* L` preserves injective objects comes here from
its being an autoequivalence, which holds in rank one. The degree-zero isomorphism is the
same construction as the published proof of `LineBundleProjectionFormulaStatement`, and
does not use Stacks' local computation. The proof uses no hypothesis on `f` and no
quasi-coherence of `M`. It builds an isomorphism but does not assert that it is the canonical
projection morphism.
