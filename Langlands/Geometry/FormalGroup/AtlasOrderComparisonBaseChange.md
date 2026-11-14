# Coefficient extension of order-linear different-cover comparisons

## Setting and provenance

This is derived infrastructure for Drinfeld's localization-gluing convention:
*Coverings of p-adic symmetric regions* (1976), printed p.109, paragraph
immediately before §2 (English translation, PDF page 3). The registered source
is `drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The source permits gluing formal groups over localizations. The comparison
constructed here is an internal consequence of actual formal atlas maps,
coefficient extension and cover refinement, rather than a separately stated
source theorem.

Let `O : Type u` and `R : Type v` be commutative rings with `Algebra O R`,
and let `D : Type w` be a possibly noncommutative ring with `Algebra O D`.
Let `σ τ : Type` be finite, with actual atlases `X : BasicAtlas O R σ` and
`Y : BasicAtlas O R τ` and actions `E : OrderAction D X` and
`E' : OrderAction D Y`. An order-linear `Comparison E E'` supplies actual
refinements to equal principal-generator sets and a two-sided formal atlas
isomorphism commuting with every element of `D`. Principal covers may be
infinite. The coefficient extension `S : CommAlgCat.{v} R` is arbitrary,
without flatness or injectivity. Coefficient tests have universe `v`, and the
complete compatible families have universe `v+1`.

All new declarations are in
`Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Comparison`.

## Full-order formal construction

`baseChange` extends both actual refinements and uses the formal isomorphism

```text
(left.orderBaseChangeIso E S).symm.trans
  ((coordinateIso.baseChange S).trans (right.orderBaseChangeIso E' S)).
```

This starts at the refinement of the extended left atlas, passes to the
extension of its original refinement, applies the extension of the original
order-linear formal comparison, then passes to the refinement of the extended
right atlas. Each component has both actual formal maps, coefficient
naturality, overlap compatibility, commutation with every `d : D`, and both
formal inverse equations. Their composition retains those properties. The
outer refinement comparisons use original transition series when image
generators merge and the selected original sources differ.

`toBasicComparison_baseChange` is an equality by definition: forgetting the
order commutation gives exactly the underlying formal `Comparison.baseChange`,
with the same two refinements and full formal maps. It does not merely identify
evaluations or tangent maps.

## Complete compatible families

For every `A : CommAlgCat.{v} S` and
`x : E.Point (restrictTest S A)`, `baseChange_onPoints` proves

```text
(f.baseChange S).onPoints A (E.toBaseChangePoints S A x)
  = E'.toBaseChangePoints S A (f.onPoints (restrictTest S A) x).
```

`baseChange_inv_onPoints` proves the square for the inverse comparison on every
original `E'`-family:

```text
((f.baseChange S).onPoints A).symm (E'.toBaseChangePoints S A y)
  = E.toBaseChangePoints S A ((f.onPoints (restrictTest S A)).symm y).
```

`baseChange_fromPoints` uses the inverse coefficient-family equivalences, for
every `y : (E.baseChange S).Point A`:

```text
f.onPoints (restrictTest S A) ((E.baseChangePointEquiv S A).symm y)
  = (E'.baseChangePointEquiv S A).symm ((f.baseChange S).onPoints A y).
```

All maps retain D-linearity. The complete-family functions of the formal
comparison and the coefficient-family equivalences agree by definition with
their underlying O-linear functions. Consequently the three underlying formal
comparison theorems prove these equations directly, including every
coefficient-extension chart test and both family compatibility conditions.

This unit extends supplied comparison witnesses. Varying-base moduli classes,
height certificates, framing and representability remain separate. Distinct
comparison witnesses are not asserted to induce the same family equivalence.
