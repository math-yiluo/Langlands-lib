# Groups of type `E₈` are quasi-split when the quasi-split ones have trivial cocycles: proof

Proof of `Langlands.GroupScheme.TypeE8QuasiSplitOfQuasiSplitCohomologyStatement` (module
`Langlands.GroupScheme.Rational.NumberFieldTypeE8TotallyComplexInputs`):

```lean
theorem typeE8QuasiSplitOfQuasiSplitCohomology :
    TypeE8QuasiSplitOfQuasiSplitCohomologyStatement.{u}
```

The theorem has exactly the statement as its type at every universe `u`, with no further
hypothesis, over every field. Its axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Statement

Let `K` be a field and `G` an affine group scheme over `Spec K`, locally of finite type. Let
`d : TitsIndexData G` be Tits index data and `e : d.Vertex ≃ Fin 8` a numbering of its simple
vertices with `d.cartan a b = CartanMatrix.E 8 (e a) (e b)`. Assume that `G` is simply connected
and absolutely almost simple. Assume moreover that, for every group `H` over `K` with the same
kind of data and properties that is quasi-split, every cocycle of `H` on the cover
`GaloisCocycle.cover K L` of every finite Galois extension `L/K` is trivial. Then `G` is
quasi-split.

## Idea

This is the argument of V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory*
(1994), proof of Proposition 6.16(A), printed p.335. The diagram `E₈` has no symmetry, so `G` is
an inner twist of a quasi-split group `M` by a cocycle with values in the adjoint group of `M`.
For type `E₈` the simply connected group has trivial centre, so the adjoint group is `M` itself.
The hypothesis applies to `M` and the twisting cocycle is trivial. Then `G ≅ M` is quasi-split.
The Lean proof does not use the symmetry of the diagram: the Library's quasi-split inner form
exists for every connected reductive group over a field.

## Proof of the main theorem

1. **Inner form.** `quasiSplitInnerFormExistence` (module
   `Langlands.GroupScheme.Rational.QuasiSplitInnerFormExistenceProof`) gives
   `Q : QuasiSplitInnerForm G` (module `Langlands.GroupScheme.Rational.QuasiSplitInnerForm`). It
   consists of a quasi-split model `Q.model`, an adjoint quotient
   `Q.quotient : Q.model ⟶ Q.adjoint`, a finite Galois extension `Q.carrier` of `K`, a natural
   family of local isomorphisms `Q.localIso` between `Q.model` and `G` over `Spec Q.carrier`, and
   a cocycle `Q.cocycle` of `Q.adjoint` on that cover. By
   `QuasiSplitInnerForm.isQuasiSplit_of_isTrivial` it suffices to show that `Q.cocycle` is
   trivial.
2. **The model is of type `E₈`.** `Q.model` is connected reductive
   (`IsAdjointQuotient.isConnectedReductive`), so it is affine and smooth.
   `LocalGroupIso.toBaseChangeIso` (module `Langlands.GroupScheme.LocalGroupIsoBaseChangeRecovery`)
   turns `Q.localIso` into an isomorphism `φ` of the base changes of `Q.model` and `G` to
   `Q.carrier`.
   - *Simply connected:* `G` over `Q.carrier` is simply connected
     (`isSimplyConnected_fieldExtension_iff`, module
     `Langlands.GroupScheme.Reductive.GeometricSimplyConnected`). So is `Q.model` over
     `Q.carrier` (`IsSimplyConnected.of_iso φ`), hence `Q.model` over `K`
     (`isSimplyConnected_fieldExtension_iff` again).
   - *Absolutely almost simple:* `G` over `Q.carrier` is absolutely almost simple
     (`IsAbsolutelyAlmostSimple.baseChange_of_algebraicExtension`, module
     `Langlands.GroupScheme.Rational.QuasiSplitSplittingReduction`). So is `Q.model` over
     `Q.carrier` (`IsAbsolutelyAlmostSimple.of_iso φ`), and absolute almost-simplicity descends
     to `K` (`IsAbsolutelyAlmostSimple.of_fieldExtension`, module
     `Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorDescentProperties`).
   - *Cartan matrix:* `titsIndexExistence` (module
     `Langlands.GroupScheme.Reductive.TitsIndexExistenceProof`) gives Tits index data `dM` of
     `Q.model`. `separableClosureIsoOfBaseChangeIso φ` is an isomorphism of `Q.model` and `G` over
     `SeparableClosure K`. `TitsIndexData.exists_cartanEquiv_of_separableClosureIso` then gives a
     bijection `v : dM.Vertex ≃ d.Vertex` with `d.cartan (v a) (v b) = dM.cartan a b`. Both
     results are in the module `Langlands.GroupScheme.Reductive.TitsIndexCartanIsoComparison`.
     With `eM := v.trans e`, `dM.cartan a b = CartanMatrix.E 8 (eM a) (eM b)`.
3. **Trivial centre.** `TitsIndexData.natCard_centerCharacter_eq_cartanDet` (module
   `Langlands.GroupScheme.SimplyConnected.CenterCharacterCartan`): the number of characters of
   the toral centre of `dM` over `SeparableClosure K` is `|det E₈|`. Mathlib's
   `CartanMatrix.E₈_det` gives `det E₈ = 1`, so there is exactly one character.
   `TitsIndexData.killsCenter_id` (module
   `Langlands.GroupScheme.SimplyConnected.TrivialCenterCharacters`) gives
   `KillsCenter (𝟙 Q.model)`. `IsAdjointQuotient.isIso_of_killsCenter_id` then makes
   `Q.quotient` an isomorphism.
4. **Applying the hypothesis.** Apply the hypothesis to `H := Q.model` with `dM`, `eM`, the
   properties of step 2, `Q.isQuasiSplit`, `L := Q.carrier`, and the cocycle
   `Q.cocycle.map (inv Q.quotient)` of `Q.model`. The cover of `Q.cocycle` is by definition
   `GaloisCocycle.cover K Q.carrier`. This gives a point `f` of `Q.model` over `Spec Q.carrier`
   with `(Q.cocycle.map (inv Q.quotient)).toFun a b = (a ≫ f) * (b ≫ f)⁻¹` for all pairs of
   points `a, b` of the cover over a common test scheme (`Cocycle.IsTrivial`).
5. **Back to the adjoint group.** Put `f' := f ≫ Q.quotient`. Compose the equation of step 4 with
   `Q.quotient`. Since `inv Q.quotient ≫ Q.quotient = 𝟙` and `Q.quotient` is a homomorphism
   (`MonObj.mul_comp`, `GrpObj.inv_comp`),
   `Q.cocycle.toFun a b = (a ≫ f') * (b ≫ f')⁻¹`. So `Q.cocycle` is trivial, and `G` is
   quasi-split by step 1.

## Scope

The hypothesis of the statement is applied once, to the quasi-split model `Q.model` and the
finite Galois extension `Q.carrier` from step 1. The model is not shown to be split, and no
property of the field `K` is used.
