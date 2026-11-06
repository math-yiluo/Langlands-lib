# Covariant exhaustion from big-cell and Steinberg data

`SteinbergCovariantExhaustionFromBigCellStatement` is the implication
`SteinbergBigCellStatement → SteinbergCovariantExhaustionStatement`, at the same
universe `u`. The theorem `steinbergCovariantExhaustion_of_bigCell` proves it. It
proves neither proposition by itself.

Worker 1330 derives this file internally. It translates the test-scheme
hypotheses of `SteinbergBigCellStatement` into the algebra-valued point
hypotheses of the Hopf-algebra theorems in `Chevalley.CellExhaustion`, and
assembles the four conditions of `SteinbergCovariantExhaustionStatement`. No
literature claim is made.

Throughout, `k : Type u` is a field. `G` and `H` are actual group schemes over
`Spec k` with affine total spaces, `hopfAlgebra G` is the published coordinate
Hopf algebra of `G`, and `pointAlgebraHom G T g` is evaluation of coordinates at a
test point `g : T ⟶ G.X`.

## Inverse points and the antipode

- `pointHopfAlgHom G T g` is `pointAlgebraHom G T g`, typed as an algebra map out
  of `hopfAlgebra G`.
- `toConv_pointHopfAlgHom_mul`: evaluation at `g * h` is the convolution product
  of the evaluations at `g` and `h`. The proof uses the published
  `pointAlgebraHom_mul`, `corepresentation_comul` and Mathlib's
  `Algebra.TensorProduct.productMap_eq_comp_map`.
- `toConv_pointHopfAlgHom_one`: evaluation at the identity point is the
  convolution unit, by `pointAlgebraHom_one` and `corepresentation_counit`.
- `pointHopfAlgHom_inv`: evaluation at `g⁻¹` is evaluation at `g` composed with
  the antipode algebra map. Evaluation at `g⁻¹` is a right convolution inverse
  of evaluation at `g`, by the two previous lemmas. The published
  `Chevalley.antipode_convMul_self` makes evaluation at `g` composed with the
  antipode a left inverse. In a monoid a left and a right inverse agree.
- `antipodeCoord G` is the antipode algebra map, typed on `algebra G`, and
  `pointAlgebraHom_antipode` restates the previous lemma on elements:
  `(S f)(g) = f(g⁻¹)`.
- `counit_eq_one_of_pointAlgebraHom_one`: if `d(1) = 1` at the identity rational
  point, then `counit d = 1`. By `pointAlgebraHom_one`, `d(1)` is the image of
  `counit d` in the global functions of `Spec k`. That ring is nontrivial, since
  `Scheme.ΓSpecIso` identifies it with `k`, so the algebra map from `k` is
  injective.
- `antipode_mem_leftCovariantSubspace_of_points`: if
  `d(g i'(h)⁻¹) = χ(h) d(g)` on all test schemes, then the antipode of `d` is
  left `i'`-covariant of weight `χ`. By the published
  `mem_leftCovariantSubspace_iff_points`, it suffices to check
  `(S d)(i'(h) g) = χ(h) (S d)(g)`. Both sides become values of `d` at inverse
  points, and `(i'(h) g)⁻¹ = g⁻¹ i'(h)⁻¹`.

## From test-scheme points to algebra-valued points

- `specCounitEquiv B` is the counit of the published adjunction
  `algΓAlgSpecAdjunction` at a `k`-algebra `B`, as an algebra equivalence from
  `B` onto the global functions of its spectrum. It is bijective because the
  relative spectrum functor is fully faithful.
- `postcomp_injective`: pushing algebra-valued points forward along an injective
  algebra map is injective. Here `postcomp` is from `Chevalley.CellExhaustion`.
- `pointAlgebraHom_injective`: a test point of `G` is determined by its
  evaluation of coordinates. The published `pointAlgebraHom_eq` writes evaluation
  as an adjunction equivalence applied to the point followed by an isomorphism.
- `pointHopfAlgHom_algPoint`: evaluation at the published `algPoint G φ` of an
  algebra map `φ` out of `hopfAlgebra G` into `R` is `φ` followed by
  `specCounitEquiv`.
- `pointMap_toConv_pointHopfAlgHom`: restricting the evaluation at `b ∈ H(T)`
  along the published coordinate pullback of `i : H → G` is evaluation at
  `i(b)`, by `pointAlgebraHom_pullback`.

`decomposition_algebraPoints` assumes the decomposition condition on test
schemes: every `g ∈ G(T)` at which `d` is a unit equals `i(b) i'(b')⁻¹`. For
every `k`-algebra `R : Type u` and algebra map `g` out of `hopfAlgebra G` with
`g(d)` a unit, it produces algebra-valued points `b`, `b'` of `H` with
`g * i'(b') = i(b)` in the convolution monoid. That is the decomposition
hypothesis of `Chevalley.CellExhaustion`. Apply the test-scheme condition to the
point `x = algPoint G g` of `Spec R`. Take `b` and `b'` to be the evaluations at
the resulting test points, followed by the inverse of `specCounitEquiv`. The
required identity holds after pushing forward along `specCounitEquiv`, by the
lemmas above and `x i'(b') = i(b)`. `postcomp_injective` removes the pushforward.

`intersection_algebraPoints` assumes the intersection condition, that
`i(c) = i'(c')` on test points implies `i(c) = j(t)`, and left `j`-invariance of a
coordinate `w` on all test schemes. For algebra-valued points `c`, `c'` with
`i(c) = i'(c')` it proves `(i(c) * g)(w) = g(w)` for every algebra-valued point
`g` of `G`. That is the invariance hypothesis of `Chevalley.CellExhaustion`. The
proof passes to the corresponding test points of `Spec R`. There
`pointAlgebraHom_injective` turns the equality of algebra-valued points into
equality of test points. The intersection condition then gives `t`, and
invariance of `w` gives the result after pushforward along `specCounitEquiv`.

## Equal-size conjugate bases

`exists_conj_irreducible_bases` takes the cofinal irreducibility condition of
`SteinbergBigCellStatement` for `i` and `χ`. For each `e` it returns `e' ≥ e`
with a basis `bX` of the `i`-covariant coordinates of weight `χ ^ e'`, indexed by
`Fin m`, on which the regular representation is rationally irreducible. It also
returns a basis indexed by the same `Fin m` of the covariant coordinates of
weight `χ ^ e'` for `i' = i ≫ inn(n)`. The second basis is the published
`leftCovariantConjBasis`, which transports `bX` by translation by `n⁻¹`. The
stability proof is the published `rightAct_mem_leftCovariantSubspace`, as in
both statements.

## The reduction

`steinbergCovariantExhaustion_of_bigCell` takes `SteinbergBigCellStatement` and
fixes `k`, `p` and a simply connected `G`. It obtains `Λ`, `j`, `H`, `i`, `n`,
`χ` and `d` with their seven conditions. The witnesses for
`SteinbergCovariantExhaustionStatement` are the same `Λ` and `j`, the subgroup
maps `i` and `i' = i ≫ inn(n)` from the same `H`, and the weight `χ` for both.

- Through the published `leftCovariantSubspace_eq_hopf`, left covariance of `d`
  and of its antipode are the Hopf-algebra covariance hypotheses of
  `Chevalley.CellExhaustion`. `counit d = 1` comes from `d(1) = 1`.
- Condition 1, injectivity of the difference comorphism, is
  `CellExhaustion.injective_differenceComorphism`. Its hypotheses are
  `decomposition_algebraPoints` and left regularity of `d`. Left regularity
  follows from `d` being a nonzerodivisor, by Mathlib's
  `isRegular_iff_mem_nonZeroDivisors`.
- Condition 2, `1 ∈ X₁ * Y₁`, is
  `CellExhaustion.one_mem_mul_leftCovariantSubspace`.
- Condition 3, exhaustion of left `j`-invariant coordinates, is
  `CellExhaustion.exists_mem_mul_leftCovariantSubspace`, with
  `decomposition_algebraPoints` and `intersection_algebraPoints`.
- Condition 4 is `exists_conj_irreducible_bases`.

## Consequence

`simplyConnectedPositiveCharConjugationMap_of_bigCell` composes this reduction
with the published `steinbergTensorEmbedding_of_covariantExhaustion` and
`simplyConnectedPositiveCharConjugationMap_of_steinberg`. It proves that
`SteinbergBigCellStatement` implies the exact statement
`SimplyConnectedPositiveCharConjugationMapStatement`, at the same universe.
`SteinbergBigCellStatement` itself remains unproved.
