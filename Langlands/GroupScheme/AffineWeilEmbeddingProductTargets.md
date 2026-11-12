# Target homomorphisms in the embedding-product point comparisons

Helper lemmas (Worker 204) for Task 5389. They state how the point comparisons of
`Langlands.GroupScheme.AffineWeilEmbeddingProductPoints` and
`Langlands.GroupScheme.AffineWeilEmbeddingProductComparison` interact with an actual
group-scheme homomorphism `f : H ⟶ H'` over `Spec K`. The final module uses them to prove
naturality in `H`. Every statement is an equation of actual scheme points; no commutativity,
smoothness or field hypothesis is used.

## `tensorEmbeddingPointsEquiv_target`

Let `p` be a point of `H` with coefficients in `K ⊗[k] R`. The `τ`-coordinate of the tensor
decomposition of `p ≫ f` is the `τ`-coordinate of `p`, followed by `f`.
`tensorEmbeddingPointsEquiv_apply` writes each coordinate as precomposition with the spectrum of
the tensor evaluation. Precomposition commutes with postcomposition by `f`, and associativity
gives the result.

## `affinePointsBaseChangeMulEquiv_symm_map`

The published inverse base-change comparison `affinePointsBaseChangeMulEquiv k Ω R _` (from
`AffinePointBaseChangeSmooth`) sends a point `p` of the base change to `Ω` to `p.left` followed by
the first pullback projection (`affinePointsBaseChangeMulEquiv_symm_left`). The base change of
`AffineWeil.map k K f` is the induced map of pullbacks (`Over.pullback_map_left`). Its composite
with the first projection is the first projection followed by `AffineWeil.map k K f`
(`pullback.lift_fst`). Therefore the inverse comparison carries the base change of
`AffineWeil.map k K f` to `AffineWeil.map k K f`. This is the special case, for the Weil
restriction, of the Library lemma `affinePointsBaseChangeMulEquiv_symm_target`. It is proved
directly here, so the module does not import `Langlands.Global.InfinitePlaceIwasawaBaseChange`.

## `baseChangeTensorPointsEquiv_target`

`baseChangeTensorPointsEquiv k K Ω H R` is the inverse base-change comparison followed by the
original tensor-valued `AffineWeil.pointsEquiv`. So the theorem follows from the previous lemma
and the published `AffineWeil.map_affinePoints`. The latter says that `pointsEquiv` carries
`AffineWeil.map k K f` to postcomposition by `f`. The conclusion reads:

```text
baseChangeTensorPointsEquiv H' R (p ≫ (baseChange (algebraBaseMap k Ω)).map (map k K f))
  = baseChangeTensorPointsEquiv H R p ≫ f.
```
