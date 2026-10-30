# Stalk dimension at a closed point of a smooth scheme over a field

`Langlands.AlgebraicGeometry.FieldSmoothClosedPointStalkDimensionStatement.{u}`
is the following `Prop`-valued definition:

```lean
∀ (k : Type u) [Field k] (X : AlgebraicGeometry.Scheme.{u})
  (f : X ⟶ Spec (CommRingCat.of k)) (g : ℕ),
  SmoothOfRelativeDimension g f → ∀ (x : X),
    IsClosed ({x} : Set X) →
      ringKrullDim (X.presheaf.stalk x) = (g : WithBot ℕ∞)
```

In words: let `k` be a field and `X` a scheme with a morphism `f` from `X` to
`Spec k`, both in the arbitrary universe `u`. If `f` is smooth of relative
dimension `g`, then for every closed point `x` of `X` the local ring
`O_{X,x}` has Krull dimension exactly `g`.

## The hypotheses and the conclusion

The statement uses Mathlib's own notions directly.

- `k` is an arbitrary field. It need not be algebraically closed or perfect,
  and its characteristic is arbitrary.
- `X` is an arbitrary scheme and `f : X ⟶ Spec (CommRingCat.of k)` is an
  arbitrary morphism to the spectrum of `k`, that is, a `k`-scheme structure on
  `X`. There is no connectedness, irreducibility, properness,
  separatedness, quasi-compactness or global finite-type hypothesis, and `X`
  may be empty (then the statement says nothing).
- `SmoothOfRelativeDimension g f` is Mathlib's
  `AlgebraicGeometry.SmoothOfRelativeDimension` (in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`), taken as an explicit
  hypothesis rather than an instance. It says that every point of `X` lies in
  an affine open `V` mapping into an affine open `U` of the base such that
  `Γ(U) → Γ(V)` is standard smooth of relative dimension `g`, that is, it has a
  submersive presentation whose number of variables minus number of relations
  is `g`. By Mathlib's
  `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`, the
  module of Kähler differentials of each such nonzero chart is free of rank
  `g`. Hence `f` is smooth and `Ω_{X/k}` is finite locally free of constant
  rank `g`, which is the Stacks Project's notion of a morphism smooth of
  relative dimension `g` (Definition 29.35.13, Tag 02G2).
- `IsClosed ({x} : Set X)` says that `x` is a closed point of the underlying
  topological space of `X`. This hypothesis is essential, as explained below.
- `X.presheaf.stalk x` is the stalk of the structure sheaf at `x`, the local
  ring `O_{X,x}`, and `ringKrullDim` is its Krull dimension, the supremum of
  lengths of chains of prime ideals, valued in `WithBot ℕ∞`. The natural
  number `g` is cast into `WithBot ℕ∞`. The conclusion is therefore an equality
  of ring dimensions, with no infinite or `⊥` value allowed.

No dimension carrier is supplied: the relative dimension is the natural number
`g` in the smoothness predicate, and the dimension in the conclusion is the
Krull dimension of the actual stalk ring.

### Local topological dimension versus stalk dimension

Two different dimensions at a point occur in the sources. The local
topological dimension `dim_x(X)` is the minimum of the dimensions of the open
neighbourhoods of `x`; the stalk dimension `dim(O_{X,x})` is the Krull
dimension of the local ring, equivalently the codimension of the closure of
`x`. The proposition concerns only the stalk dimension; it does not state
anything about `dim_x(X)`. The two agree at closed points of locally algebraic
`k`-schemes, but not at other points. For example, for the affine line
`X = 𝔸¹_k`, which is smooth of relative dimension `1` over `k`, the stalk at
the generic point is the field `k(t)`, of Krull dimension `0`, while
`dim_x(X) = 1` at every point. This is why the closed-point hypothesis is
retained: without it the statement would be false.

This file defines the proposition only. It provides no proof of the dimension
equality or of the prerequisite comparison between the rank of the
differentials and the fibre dimension. A separate proof task is to prove this
exact published proposition.

## Derived provenance

This is an internal derived statement. It combines two results of the Stacks
Project; neither of them alone states this Lean interface.

1. **Tag 02G1** (Lemma 29.35.12). Source ID
   `stacks-smooth-differential-rank-2026-10-22`, folder
   `literature/Stacks Project - Smooth morphisms and differential rank (HTML snapshot 2026-10-22)`
   (source-folder SHA-256
   `a20ebb3b9b37ee166cb66decf78eed5aae44e5ed93634cf911eee19d224c1bc5`), file
   `01V4.html` (SHA-256
   `4327b0dc32a5b7a4fc554e6587f0d622d978e306bba4d2783a8aade3704aa3da`),
   Section 29.35, https://stacks.math.columbia.edu/tag/02G1 . The lemma and the
   adjoining Definition 29.35.13 (Tag 02G2) were read in the retained snapshot:

   > Let f : X → S be a morphism of schemes. Assume f is smooth. Then the
   > module of differentials Ω_{X/S} of X over S is finite locally free and
   > rank_x(Ω_{X/S}) = dim_x(X_{f(x)}) for every x ∈ X.

   Lemma 29.35.8 (Tag 01VE) in the same section states that a smooth
   morphism is locally of finite presentation. The section's two web comments
   concern the rendering of a commutative diagram; the tag page of 02G1 has no
   comments. No errata note for this source was found.

2. **Tag 0A21, item (2)** (current Lemma 33.20.3). Source ID
   `stacks-flasque-affine-vanishing-kunneth-a04446e5`, folder
   `literature/Stacks Project - Flasque sheaves, affine vanishing and Kunneth over a field (source at a04446e5)`
   (source-folder SHA-256
   `af02e6f0aff875e216f1e0fde58f6baad3eedeb6b82799a8d6c91ff68cccaa3a`), file
   `varieties.tex` (SHA-256
   `53d0af48818d22ae85675eff76b79fcad4335fda0b4574ec09f5c9e73cc93995`),
   `lemma-dimension-locally-algebraic`, item `item-dimension-at-closed-point`,
   lines 3783-3792, with its proof at lines 3867-3870; `tags.txt` line 12689
   maps the label to 0A21, https://stacks.math.columbia.edu/tag/0A21 . The
   whole lemma and its proof were read. The lemma assumes that `X` is a
   locally algebraic `k`-scheme, which by Definition 33.20.1 (Tag 06LG,
   `varieties.tex` lines 3718-3725) means that `X → Spec(k)` is locally of
   finite type. Item (2) reads:

   > For x ∈ X closed, we have dim_x(X) = dim(O_{X,x}).

   Its proof reduces to an affine neighbourhood and cites the corresponding
   algebra lemma for finite type `k`-algebras. The official tag page has two
   web comments, which correct the order of a sequence in item (9)(d) and are
   unrelated to item (2); the retained source already contains the
   correction.

The derivation is as follows. By the remarks above, Mathlib's
`SmoothOfRelativeDimension g f` makes `f` smooth with `Ω_{X/k}` finite locally
free of constant rank `g`. The base `Spec k` has a single point `s`, with
residue field `k`, so the fibre `X_s = X ×_{Spec k} Spec κ(s)` is `X` itself.
Tag 02G1 then gives `dim_x(X) = rank_x(Ω_{X/k}) = g` for every `x ∈ X`. A
smooth morphism is locally of finite presentation (Tag 01VE; in Mathlib, the
instance from `AlgebraicGeometry.Smooth` to
`AlgebraicGeometry.LocallyOfFinitePresentation`), hence locally of finite
type, so `X` is a locally algebraic `k`-scheme and item (2) of Tag 0A21
applies: at a closed point `x`, `dim(O_{X,x}) = dim_x(X) = g`. The Stacks
Project's `dim(O_{X,x})` is the Krull dimension of the local ring, which is
Mathlib's `ringKrullDim (X.presheaf.stalk x)`.

The Lean statement uses Mathlib's chart-wise definition of relative dimension
instead of the Stacks Project's definition through the rank of `Ω_{X/S}`, and
it omits the intermediate topological dimension `dim_x(X)`: only the final
equality of the stalk dimension with `g` is stated.

## Imports

The module imports only Mathlib: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`
for `AlgebraicGeometry.SmoothOfRelativeDimension`, and
`Mathlib.AlgebraicGeometry.Properties`, which makes `ringKrullDim` available
and contains the related comparison
`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight` between the stalk dimension
and the coheight of the point in the specialization order. That lemma is a
possible aid for the proof, not part of the statement.
