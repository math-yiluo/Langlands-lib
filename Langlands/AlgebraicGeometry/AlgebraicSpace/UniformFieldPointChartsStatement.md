# Finitely many affine étale charts carrying all field-valued points

Author: Worker 80.

`Langlands.AlgebraicGeometry.AlgebraicSpace.UniformFieldPointChartsStatement` is an
intermediate statement for the closedness part of Corollary 5.7 of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed pp.16–17. It is derived
from the construction in the proof of Stacks Project, Lemma 68.8.3 (Tag 0BBN), together with
the fibre-degree bound in the proof of Lemma 68.8.4 (Tag 07S9). The module only states it and
contains no proof.

## The statement

Let `C : Type u` be a commutative ring and let `X` be an algebraic space over `Spec C` (the
Library notion `AlgebraicSpace (Spec (CommRingCat.of C))`). Assume:

- `X` is separated (`IsSeparated X`: the diagonal is a representable closed immersion);
- `X` is quasi-compact (`IsQuasiCompact X`: there is a surjective étale atlas by a scheme
  whose underlying space is compact).

Then there are a natural number `n`, schemes `U i` over `Spec C` for `i : Fin n`, and
morphisms of algebraic spaces `f i : U i → X` (from the algebraic space represented by
`U i`), such that:

1. each `(U i).left` is an affine scheme, and each `f i` is étale (`IsEtale (hom (f i))`);
2. for every field `k : Type u` with a `C`-algebra structure and every `k`-valued point
   `x : RingPoints C X k` of `X`, there are an index `i` and a `k`-valued point
   `u : RingPoint C (U i) k` of `U i` (a morphism `Spec k → U i` over `Spec C`) such that
   `RingPoints.map (f i) ((schemeRingPointsEquiv C (U i) k).symm u) = x`, that is, `f i`
   maps `u` to `x`.

The same finite family of charts works for all fields `k` at once. For a single point the
lifting is the Library theorem `FieldPointEtaleLift.exists_affine_etale_point`, whose chart
depends on the point.

## Relation to the sources and derived content

Stacks Project, Lemma 68.8.3 (Tag 0BBN), registered source `stacks-stratification-2026-11-02`,
file `0BBN.html`, first paragraph of the proof: for a quasi-compact algebraic space `X` with a
surjective étale map `U → X` from an affine scheme, let `W_p` be the `p`-fold fibre product
`U ×_X … ×_X U` minus all diagonals. The symmetric group `S_p` acts freely on `W_p` over `X`,
the quotient `V_p = W_p/S_p` is a scheme, and `V_p → X` is étale. The second paragraph shows
that a point `Spec k → X` with `k` algebraically closed factors through the image of `V_p`
when the fibre `U ×_X Spec k` has at least `p` points, and that `V_p ×_X Spec k` has exactly
one point when the fibre has exactly `p` points. The proof of Lemma 68.8.4 (Tag 07S9, file
`07S9.html`) adds that, when the degrees of the fibres of `U → X` are bounded by `n`, only
`p ≤ n` occur.

The present statement is derived from that construction; it is not stated in the source. When
`X` is separated, `U ×_X U` is affine, so each `W_p` and each quotient `V_p` is affine, and the
degrees of the fibres of `U → X` are bounded. For any field `k` and any `x : Spec k → X`, the
fibre `U ×_X Spec k` is a finite étale `k`-scheme of some degree `p ≤ n`. Over a finite
Galois extension `L/k` that splits it, its `p` points over `L`, in some order, give an
`L`-point of `W_p`. Its class in `V_p` is invariant under `Gal(L/k)`, hence is a `k`-point of
`V_p` over `x`. So the charts
`V_1 → X, …, V_n → X` have the property stated. The choices here are the restriction to
separated spaces, which makes the charts affine; the formulation with arbitrary fields `k`
rather than algebraically closed ones; and the packaging as a finite indexed family. The name
of the statement is chosen here.

The use in Conrad's Corollary 5.7: Conrad's proof of closedness (printed p.16, last
paragraph) uses "a huge disjoint union" of étale charts through which every `R`-point lifts,
and in the locally compact case (printed p.17) a finite stratification of `X` by schemes to
get finitely many charts. For a separated `X` of finite type over a henselian valuation ring
`O`, applying the present statement to the residue field of `O` and lifting the residue
points by Hensel's lemma (the Library theorem
`HenselianIntegralPointsCompact.exists_point_of_residue_point`) gives finitely many affine
étale charts through which every `O`-point of `X` lifts.

## Sources

- Stacks Project, Decent Algebraic Spaces, Lemma 68.8.3 (Tag 0BBN), proof, and Lemma 68.8.4
  (Tag 07S9), proof: registered source `stacks-stratification-2026-11-02`, directory SHA-256
  `844f29708bb7e14d69fe37b2251bb94ea49065647c1257aaaeb4655ac6a1288e`.
- Conrad, registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
  `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, proof of Corollary 5.7,
  printed pp.16–17.
