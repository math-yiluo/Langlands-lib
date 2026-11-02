# Independence and naturality of regular atlases: proof

The theorem

```lean
theorem regularAtlasCanonicality (k : Type) [RCLike k]
    (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] (d : ℕ) :
    regularAtlasCanonicalityStatement k X d
```

proves the published proposition `regularAtlasCanonicalityStatement`. It
covers every `RCLike` coefficient field in `Type`, every affine `X` and
every source dimension `d`. The target dimension `e` and, where they occur,
the target `Y` are arbitrary. The proof has no level parameters and no
hypotheses beyond those of the statement. It uses only the fields of the
given regular atlases and the published results named below. It does not
construct an atlas from algebraic smoothness. No case split occurs: `d = 0`,
`e = 0`, and empty point spaces are covered by the general argument.

Throughout, the source and target charted spaces are the explicit
`A.chartedSpace` and `B.chartedSpace`, exactly as in the statement. Inside
the proofs the source atlas is installed by a local
`let _ : ChartedSpace (Fin d → k) (RingPoint k X k) := A.chartedSpace`.
The two auxiliary results below are stated for possibly different objects
`X` and `Y`, so the two local instances live on different carrier types.
The identity case `Y = X` is obtained by instantiating them, never by
instance search on a single carrier with two atlases.

## Actual morphisms are smooth

`RegularAtlas.contMDiff_postcomp A B f` proves, for regular atlases `A` on
`X` of dimension `d` and `B` on `Y` of dimension `e` and an actual relative
morphism `f : X ⟶ Y`, that `fun p => p ≫ f` is
`ContMDiff 𝓘(ℝ, Fin d → k) 𝓘(ℝ, Fin e → k) ∞` from `A.chartedSpace` to
`B.chartedSpace`.

The identity family `fun p => p` on `RingPoint k X k` with `A.chartedSpace`
is `RegularSmooth 𝓘(ℝ, Fin d → k)`: for each global regular function `a`,
this is the published `RegularAtlas.contMDiff_regularEvaluation A a`. The
published `RegularSmooth.postcomp` then shows that `fun p => p ≫ f` is
`RegularSmooth`; it pulls back global regular functions along `f` using
`regularEvaluation_postcomp`. Finally, the reverse direction of the
published family criterion `RegularAtlas.contMDiff_iff_regularSmooth B`,
applied with source charted space `RingPoint k X k` and model
`𝓘(ℝ, Fin d → k)`, turns this into `ContMDiff` into `B.chartedSpace`. The
family criterion needs no manifold hypothesis on the source.

## Diffeomorphisms from actual isomorphisms

`RegularAtlas.postcompDiffeomorph A B f` is the real `C∞` diffeomorphism
from `A.chartedSpace` to `B.chartedSpace` for an actual relative
isomorphism `f : X ≅ Y`. Its forward map is `p ↦ p ≫ f.hom` and its inverse
map is `q ↦ q ≫ f.inv`. The two inverse laws follow from
`Category.assoc`, `f.hom_inv_id` (respectively `f.inv_hom_id`) and
`Category.comp_id`. Both smoothness fields are instances of
`contMDiff_postcomp`, once for `f.hom` from `A` to `B` and once for `f.inv`
from `B` to `A`.

## The four conjuncts

- Identity diffeomorphisms (`regularAtlasIndependenceStatement`). For
  atlases `A` and `B` on `X` of dimensions `d` and `e`, the witness is
  `A.postcompDiffeomorph B (Iso.refl X)`. Its underlying equivalence sends
  `p` to `p ≫ 𝟙 X`, which equals `p` by `Category.comp_id`. Thus
  `Equiv.ext` shows that the equivalence is `Equiv.refl`.
- Morphism smoothness (`regularAtlasMorphismSmoothnessStatement`). This is
  `A.contMDiff_postcomp B f` for every affine `Y`, every `e` and every
  `f : X ⟶ Y`. No hypothesis on `f` is used.
- Evaluation smoothness (`regularAtlasEvaluationSmoothnessStatement`). This
  is the published `RegularAtlas.contMDiff_regularEvaluation A a`.
- Isomorphism diffeomorphisms (`regularAtlasIsomorphismStatement`). The
  witness is `A.postcompDiffeomorph B f`. The required equalities
  `eF p = p ≫ f.hom` and `eF.symm q = q ≫ f.inv` hold by definition
  (`rfl`).

## Provenance

The proof is internal. It follows the route that the statement's Markdown
and the task context describe. It applies the published proof module
`RegularAtlasComparisonProof`, specifically
`RegularAtlas.contMDiff_regularEvaluation` and
`RegularAtlas.contMDiff_iff_regularSmooth`. It also uses
`RegularSmooth.postcomp` from `RegularEvaluation` and Mathlib's
`Diffeomorph` structure. No literature result is transcribed.
