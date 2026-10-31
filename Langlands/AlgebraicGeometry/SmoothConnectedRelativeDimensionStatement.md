# Constant relative dimension of a smooth morphism with connected source

`Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionStatement.{u}` is
the following `Prop`-valued definition:

```lean
∀ (X Y : _root_.AlgebraicGeometry.Scheme.{u}) (f : X ⟶ Y),
  Smooth f → ConnectedSpace X → ∃ n : ℕ, SmoothOfRelativeDimension n f
```

In words: let `f : X ⟶ Y` be a morphism of schemes in the arbitrary universe
`u`. If `f` is smooth and the underlying topological space of `X` is connected,
then there is a natural number `n` such that `f` is smooth of relative
dimension `n`.

## The hypotheses and the conclusion

The statement uses Mathlib's own predicates from
`Mathlib.AlgebraicGeometry.Morphisms.Smooth`, all taken as explicit hypotheses
rather than instances.

- `X` and `Y` are arbitrary schemes and `f` is an arbitrary morphism. Nothing
  is assumed about `Y`: it need not be connected, Noetherian, affine or the
  spectrum of a field. Nothing is assumed about `f` beyond smoothness: no
  properness, separatedness, quasi-compactness or global finiteness.
- `Smooth f` is `AlgebraicGeometry.Smooth`, the geometric notion of
  smoothness: for all affine opens `U ⊆ Y` and `V ⊆ X` with `V ≤ f ⁻¹ᵁ U`, the
  ring map `Γ(Y, U) → Γ(X, V)` is smooth. It does not mention a relative
  dimension or a rank of differentials.
- `ConnectedSpace X` is Mathlib's connectedness of the underlying topological
  space of `X`. Mathlib's `ConnectedSpace` includes nonemptiness
  (`ConnectedSpace.toNonempty`), so `X` is nonempty.
- `SmoothOfRelativeDimension n f` is `AlgebraicGeometry.SmoothOfRelativeDimension`,
  Mathlib's chart-wise notion: every point `x` of `X` lies in an affine open
  `V` mapping into an affine open `U` of `Y` such that `Γ(Y, U) → Γ(X, V)` is
  standard smooth of relative dimension `n`, that is, it admits a submersive
  presentation whose number of variables minus number of relations is `n`. The
  same `n` is used at every point of `X`.

The proposition asserts only existence of such an `n`. It makes no uniqueness
claim. It assumes no differential rank, no fibre dimension and no previously
known bound on the dimension: the natural number `n` is the conclusion, not a
hypothesis.

### Why the source must be connected

Connectedness of the source cannot be dropped. For a field `k`, the disjoint
union `X = Spec k ⊔ 𝔸¹_k` is smooth over `Spec k`, but every standard smooth
chart of relative dimension `n` around the point of `Spec k` has `n = 0`, while
every such chart around a point of `𝔸¹_k` has `n = 1` (in each case the
module of differentials of the chart is free of rank `n`, and its rank at the
point is `0`, respectively `1`). No single `n` works, and the proposition
says nothing about such disconnected sources. Connectedness of the target is
not needed: only the source is required to be connected.

This file defines the proposition only. It provides no proof of it, and no
proof of the comparison between Mathlib's chart-wise relative dimension and
the rank of the module of differentials described below. A separate proof
task is to prove this exact published proposition.

## Derived provenance

This is an internal derived statement. It is not stated verbatim in the
source; it combines a lemma and a definition of the Stacks Project with an
elementary connectedness argument.

The registered original is source ID
`stacks-smooth-differential-rank-2026-10-22`, folder
`literature/Stacks Project - Smooth morphisms and differential rank (HTML snapshot 2026-10-22)`
(source-folder SHA-256
`a20ebb3b9b37ee166cb66decf78eed5aae44e5ed93634cf911eee19d224c1bc5`), file
`01V4.html` (SHA-256
`4327b0dc32a5b7a4fc554e6587f0d622d978e306bba4d2783a8aade3704aa3da`),
Section 29.35 (Tag 01V4). The following passages, with their proofs where
present, were read in the retained snapshot.

1. **Lemma 29.35.12 (Tag 02G1)**, https://stacks.math.columbia.edu/tag/02G1 :

   > Let f : X → S be a morphism of schemes. Assume f is smooth. Then the
   > module of differentials Ω_{X/S} of X over S is finite locally free and
   > rank_x(Ω_{X/S}) = dim_x(X_{f(x)}) for every x ∈ X.

   Its proof reduces, by Lemma 29.35.11 (Tag 01V7), to a standard smooth
   morphism of affine schemes.

2. **Definition 29.35.13 (Tag 02G2)**, https://stacks.math.columbia.edu/tag/02G2 :

   > Let d ≥ 0 be an integer. We say a morphism of schemes f : X → S is smooth
   > of relative dimension d if f is smooth and Ω_{X/S} is finite locally free
   > of constant rank d.

3. **Lemma 29.35.11 (Tag 01V7)**: for any affine open `V ⊆ S` containing
   `f(x)`, the morphism `f` is smooth at `x` if and only if there is an affine
   open `U ⊆ X` containing `x` with `f(U) ⊆ V` such that `f|_U : U → V` is
   standard smooth.

The section page carries two web comments, about the rendering of a
commutative diagram. No errata note for these passages was found.

The derivation is as follows. Let `f : X → S` be smooth with `X` connected.
By Tag 02G1, `Ω_{X/S}` is finite locally free, so every point has an open
neighbourhood on which `Ω_{X/S}` is free of some finite rank. Hence the
function `x ↦ rank_x(Ω_{X/S})` is locally constant on `X`. This step is the
elementary meaning of finite local freeness and is not quoted from the
section. A locally constant function on a connected space is constant, say
with value `d`, so `f` is smooth of relative dimension `d` in the sense of
Definition 29.35.13.

## Relation to Mathlib's chart predicate

The source defines relative dimension through the constant rank of
`Ω_{X/S}`; Mathlib's `SmoothOfRelativeDimension n f` instead asks for standard
smooth charts of relative dimension `n` around every point. These are
different definitions, and the source's conclusion does not by itself give
Mathlib's. A proof of this proposition must therefore establish the needed
correspondence between the two notions as part of its mathematics: for the
constant `d` obtained from connectedness, every point must be shown to have a
standard smooth chart of relative dimension exactly `d`. No rank hypothesis may
be assumed for this purpose, and none appears in the statement.

The following existing declarations are possible aids, not part of the
statement.

- `AlgebraicGeometry.Smooth.exists_isStandardSmooth` gives, for smooth `f`
  and each point `x`, an affine chart around `x` on which
  `Γ(Y, U) → Γ(X, V)` is standard smooth, of some unspecified relative
  dimension (a Mathlib counterpart of Tag 01V7).
- `Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth` says
  that a standard smooth algebra `S` over `R` with `S` nontrivial is standard
  smooth of relative dimension `n` exactly when `Module.rank S Ω[S⁄R] = n`.
  A chart containing a point has a nontrivial ring of sections, so this
  converts chart dimensions into ranks of Kähler modules of the chart rings.
- The published theorem `Langlands.Scheme.smoothDifferentialsFiniteLocalBasisRank`
  (module `Langlands.AlgebraicGeometry.SmoothDifferentialsFiniteLocalBasisRank`)
  proves `Langlands.Scheme.SmoothDifferentialsFiniteLocalBasisRankStatement`:
  smoothness gives finite local bases of the sheaf of relative differentials,
  and a specified chart relative dimension `n` gives local freeness of rank
  `n`. It does not prove constancy of the rank on a connected source or the
  converse direction from rank to chart dimension.

## Imports

The module imports only `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, which
defines `AlgebraicGeometry.Smooth` and
`AlgebraicGeometry.SmoothOfRelativeDimension` and makes `ConnectedSpace`
available for the underlying space of a scheme.
