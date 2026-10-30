# Divisibility of geometric points of abelian schemes

This module proves the published statement
`Langlands.AbelianScheme.AlgClosedPointDivisibilityStatement` (module
`Langlands.AbelianScheme.AlgClosedPointDivisibilityStatement`, imported
unchanged). The exact-target theorem is
`Langlands.AbelianScheme.algClosedPointDivisibility`.

## Statement proved

Let `S` be a scheme, `B : AbelianScheme S` an actual abelian scheme, `K` an
algebraically closed field in the same universe, `s : Spec K ⟶ S` a morphism and
`m` a natural number with `(m : K) ≠ 0`. Then every point `y : Over.mk s ⟶ B.X`
is an `m`-th power `x ^ m` of some point `x : Over.mk s ⟶ B.X`. The power is
taken in Mathlib's group of morphisms into the group object `B.X`. No hypothesis
beyond the statement is added.

## Proof

The proof has two auxiliary results over a field and a final transport along
the pullback square of the base change.

`multiplication_etale_of_field`: for any field `K`, an abelian scheme `A` over
`Spec K` and `m` with `(m : K) ≠ 0`, the underlying scheme morphism of
multiplication by `m` is étale. Since `(m : K) ≠ 0` we have `m > 0`. The image of
`m` in `Γ(Spec K, ⊤)` is a unit because it is the image of the unit `(m : K)`
under the ring map `(Scheme.ΓSpecIso K).inv`. The published theorem
`Langlands.AbelianScheme.multiplicationEtale` then gives étaleness.

`multiplication_surjective_of_field`: under the same hypotheses, the
underlying scheme morphism `f` of multiplication by `m` is surjective. The proof
is the clopen-image argument.

- `f` is étale, so it is flat and locally of finite presentation, and hence an
  open map (`f.isOpenMap`).
- `f` lies over `Spec K`, that is `f ≫ A.X.hom = A.X.hom`. The structure
  morphism `A.X.hom` is proper, so it is universally closed and separated.
  `UniversallyClosed.of_comp_of_isSeparated` makes `f` universally closed, and
  hence a closed map.
- `Spec K` is a one-point space and `A.X.hom` is geometrically connected, so
  Mathlib's `GeometricallyConnected.connectedSpace_of_subsingleton` makes the
  total space `A.X.left` connected.
- `A.X.left` is nonempty. A geometrically connected morphism is surjective by a
  Mathlib instance, because its fibres are connected and hence nonempty. So
  `A.X.hom` maps onto the nonempty `Spec K`, and the range of `f` is nonempty.

The range of `f` is open, closed and nonempty in a connected space, so it is
everything.

`algClosedPointDivisibility` proves the statement. Let `BK` be the base change
`(baseChange s).obj B`, an abelian scheme over `Spec K`. Its underlying scheme is
`pullback B.X.hom s`. Let `f` be the underlying scheme morphism of
multiplication by `m` on `BK`, and let `g` be multiplication by `m` on `B`.

1. By the two auxiliary results, `f` is étale, hence locally of finite type,
   and surjective.
2. `Langlands.GroupScheme.multiplication_baseChange` identifies `f` with the
   base change `((Over.pullback s).map g).left`. That map is the pullback lift
   of `pullback.fst ≫ g.left` and `pullback.snd`, so
   `f ≫ pullback.fst = pullback.fst ≫ g.left`. The `Over` condition for `f`
   gives `f ≫ pullback.snd = pullback.snd`.
3. The point `y` and the identity of `Spec K` define the section
   `y' = pullback.lift y.left (𝟙 _)` of the pullback.
   `Langlands.exists_point_lift_of_locallyOfFiniteType_surjective`, applied to
   `f` and `y'` with `K` algebraically closed, gives `a : Spec K ⟶ pullback B.X.hom s`
   with `a ≫ f = y'`. Composing with `pullback.snd` and using step 2 gives
   `a ≫ pullback.snd = 𝟙`.
4. The point is `x = Over.homMk (a ≫ pullback.fst)`. It lies over `s` because
   `a ≫ pullback.fst ≫ B.X.hom = a ≫ pullback.snd ≫ s = s` by the pullback
   condition.
5. `x ^ m` is rewritten as `x ^ (m : ℤ)` with `zpow_natCast`. By
   `Langlands.GroupScheme.points_multiplication` this equals `x ≫ g`. On
   underlying scheme morphisms,
   `a ≫ pullback.fst ≫ g.left = a ≫ f ≫ pullback.fst = y' ≫ pullback.fst = y.left`.
   Hence `x ^ m = y`.

## Dependencies

The proof imports published Library results by Lean name. These are
`Langlands.AbelianScheme.multiplicationEtale` (module
`Langlands.AbelianScheme.MultiplicationEtale`),
`Langlands.exists_point_lift_of_locallyOfFiniteType_surjective` (module
`Langlands.AbelianScheme.AlgClosedIsogenyPointLifting`),
`Langlands.GroupScheme.multiplication_baseChange` and
`Langlands.GroupScheme.points_multiplication`. It uses no isogeny statement, in
particular not the unproved `Langlands.GroupScheme.MultiplicationIsogenyStatement`.
The only axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The task cites Milne, *Abelian Varieties* (1986, author's corrected version of
2022), Theorem 8.2 on p.13 and Proposition 20.7 on p.44, for surjectivity of
multiplication by `m`; the statement is its consequence at geometric points.
The implemented route need not follow Milne's proofs. It proves surjectivity
only over the field `K` with `m` invertible, by combining étaleness (open
image), properness (closed image) and connectedness of the abelian scheme over
`Spec K`.
