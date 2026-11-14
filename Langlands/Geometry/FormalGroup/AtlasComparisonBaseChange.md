# Coefficient extension of comparisons on different principal covers

## Setting and provenance

This is derived infrastructure for the localization-gluing convention in
Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109,
paragraph immediately before §2 (English translation, PDF page 3). The
registered source is `drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The source allows formal groups obtained by gluing over localizations. The
coefficient-extension result here is an internal consequence of the actual
formal atlas, refinement and isomorphism constructions; it is not a separate
theorem stated in that paragraph.

Let `O : Type u` and `R : Type v` be commutative rings with `Algebra O R`, and
let `σ τ : Type` be finite coordinate types. For actual atlases
`X : BasicAtlas O R σ` and `Y : BasicAtlas O R τ`, a
`Comparison X Y` consists of actual cover refinements `left` and `right`, an
equality of their finer generator sets, and a formal atlas isomorphism
`coordinateIso` between the refined atlases. That isomorphism supplies both
formal maps, their coefficient naturality, overlap compatibility, and both
formal inverse equations. Covers can be infinite. Let
`S : CommAlgCat.{v} R` be arbitrary. No flatness or injectivity of `R → S` is
required. Coefficient tests have universe `v`; complete families have universe
`v+1`.

All new declarations are in
`Langlands.FormalGroup.ModuleLaw.BasicAtlas.Comparison`.

## Actual comparison after coefficient extension

`baseChange` extends the left and right refinements by their actual
coefficient-extension construction. The extended finer covers agree by
`baseOpens_eq`. Its formal coordinate isomorphism is

```text
(left.baseChangeIso S).symm.trans
  ((coordinateIso.baseChange S).trans (right.baseChangeIso S)).
```

Starting at the refinement of `X.baseChange S`, this goes back to the
coefficient extension of the original left refined atlas, applies the extended
original formal isomorphism, then goes to the refinement of `Y.baseChange S`.
Every component is a constructed formal atlas isomorphism; composition retains
both actual formal maps and their formal inverse equations. The refinement
comparison uses original transitions when coefficient extension merges
generators and source choices differ. The construction therefore does not
identify those source choices or replace a formal isomorphism with an assumed
point-functor isomorphism.

## Complete-family squares

For every `A : CommAlgCat.{v} S` and
`x : X.Point (restrictTest S A)`, `baseChange_onPoints` proves

```text
(f.baseChange S).onPoints A (X.toBaseChangePoints S A x)
  = Y.toBaseChangePoints S A (f.onPoints (restrictTest S A) x).
```

The proof restricts both sides to the right finer cover, whose complete-family
restriction is injective. Evaluation of the composed formal maps gives three
successive maps. The inverse left refinement square identifies the first
value with the extension of the original restricted family. The original
formal isomorphism's coefficient-extension square moves through the middle
map. The characterization of `f.onPoints` by right restriction and the forward
right refinement square give the required value. The proof concerns complete
compatible families on all coefficient-extension tests, not only a component
on the base ring.

`baseChange_inv_onPoints` gives the square for the inverse different-cover
comparison on every original `Y`-family. It applies the forward square to the
inverse original family and uses the two constructed linear equivalences.

`baseChange_fromPoints` instead uses the inverse coefficient-family
comparisons: for every `y : (X.baseChange S).Point A`,

```text
f.onPoints (restrictTest S A) ((X.baseChangePointEquiv S A).symm y)
  = (Y.baseChangePointEquiv S A).symm ((f.baseChange S).onPoints A y).
```

It follows by applying the injective forward coefficient-family equivalence,
then the forward square and the coefficient equivalences' inverse equations.
All point maps in these equations are O-linear.

Full acting-order compatibility, varying-base moduli classes, height
certificates, framing, and representability are separate constructions. This
unit extends a supplied actual comparison; it makes no assertion that distinct
comparison witnesses act by the same point equivalence.
