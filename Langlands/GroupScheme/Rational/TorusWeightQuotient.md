# Vector group quotients of cyclic weight subgroups

Let `k` be a field, `σ : TorusAction F I` a split-torus action on a corepresented group
functor `F` whose representing algebra `B` is formally smooth and of finite type over
`k`, `a ≠ 0` a character and `r > 0`. Let `U_r` be the weight subgroup of the cyclic
tail `cyclicTail a r` (`Rational.TorusWeightSubgroups`, `Rational.TorusWeightPolynomial`).
This module shows that its closed subgroup scheme
`cutGroupScheme (isCutOutBy_weightIdeal e σ (cyclicTail a r))` maps onto a vector group
by primitive coordinates of weight `r • a`. The map is a represented fppf quotient
(`RelativeRoot.IsFppfQuotient`) by the next cyclic weight subgroup. All declarations are
in namespace `Langlands.GroupScheme.Corepresented`.

## Statements

- `aeval_sum_elim_ulift_bijective`: suppose `aeval (Sum.elim y z)` is bijective on
  `k[Fin N ⊕ ι]`, with `ι : Type`. Then so is `aeval (Sum.elim y (z ∘ ULift.down))` on
  `k[Fin N ⊕ ULift ι]`. This adapts the index universe to the published quotient theorem.
- `exists_isFppfQuotient_cyclicTail`: there are `N` and elements
  `y : Fin N → B ⧸ weightIdeal e σ (cyclicTail a r)` with the following properties.
  - `hy`: they form a primitive family (`VectorGroup.IsPrimitiveFamily`) for the
    corepresentation `weightCorep e σ (cyclicTail a r)`.
  - Each `y i` is homogeneous of weight `r • a`.
  - Let `M` be any subgroup functor of the cut group scheme whose points over every test
    scheme `T` are exactly those whose algebra point (`pointsEquiv`) lies in
    `weightSubgroup e σ (cyclicTail a (r + 1))`. Then
    `RelativeRoot.IsFppfQuotient M (VectorGroup.quotientMap hy)`.

## Proof

`exists_primitive_coordinates` (`Rational.TorusWeightPrimitive`) gives the primitive
coordinates `y`, further coordinates `z` with `aeval (Sum.elim y z)` bijective, and the
kernel description: the `y i` vanish on a point exactly when it lies in `U_{r+1}`. The
published `VectorGroup.isFppfQuotient_quotientMap` (Worker 1239,
`Langlands.GroupScheme.VectorGroupQuotient`) then applies, after lifting the index type of
`z` to `Type u` with `aeval_sum_elim_ulift_bijective`.

## Provenance

Internal supporting material for the proof of
`Langlands.GroupScheme.RelativeRoot.CyclicWeightFiltrationStatement` (task 023326af).
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed., Lemma 3.3.8 (printed p.111)
states that `U_{A_j}(G)/U_{A_{j+1}}(G)` is a vector group whose Lie algebra has the single
weight `j • a`. Here the quotient is constructed explicitly, on the cut group scheme, as a
morphism to a vector group, using the target's notion `IsFppfQuotient`. The route is
internal to this formalization.
