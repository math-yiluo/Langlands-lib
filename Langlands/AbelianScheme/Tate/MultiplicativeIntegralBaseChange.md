# Integral multiplicative Tate comparison under base change

This internal construction connects the published comparison between actual
torsion points of the multiplicative group and roots of unity with actual
group-scheme base change. It imports `IntegralBaseChange` and
`MultiplicativeAffineTestScheme`. Every new declaration is in
`Langlands.GroupScheme.Gm.TateComparison`.

## Inputs and canonical geometry

Let `b : S' ⟶ S` be any morphism of schemes in the same universe and
`T : Over S'` any test scheme. The test scheme `(Over.map b).obj T`
has the same underlying scheme as `T`, with structural morphism composed
with `b`. Its global section ring is therefore definitionally the same.

The published `Gm.baseChangeIso b` is the canonical group-scheme
isomorphism from the pullback of `Gm S` to `Gm S'`, constructed through
the representation of units. The published `Tate.levelBaseChange` and
`Tate.integralBaseChange` are induced by the pullback adjunction on actual
torsion points and their coherent families. The `Tate.levelMap` and
`Tate.map` maps use actual group-scheme homomorphisms.

No finite/étale, invertibility, connectedness or field hypothesis is
needed for this comparison. The topology throughout is the existing
product-subspace topology on coherent families of discrete torsion
levels. Compactness and profiniteness are not asserted here.

## Finite levels and the actual pullback formula

For every natural number `n`, including zero, the lemma
`levelEquiv_actualBaseChange` proves

```text
levelEquiv ((Over.map b).obj T) n
  (Tate.levelBaseChange b (Gm S) T n
    (Tate.levelMap T (Gm.baseChangeIso b).inv n x))
  = levelEquiv T n x.
```

Here the displayed group-scheme objects abbreviate their `toGrp` values.
Thus applying the inverse canonical multiplicative-group isomorphism and
then the actual torsion pullback identification preserves the root
coordinate in `Γ(T.left, ⊤)`. The Lean proof applies the injective
underlying-unit map and invokes
`Gm.baseChangeUnitsEquiv_baseChangeIso_inv` on the actual section
underlying `x`.

`levelBaseChange b T n` packages a `ZMod n`-linear equivalence from
`Tate.Level (Gm S').toGrp T n` to
`Tate.Level (Gm S).toGrp ((Over.map b).obj T) n`. Its definition uses
the two canonical root-coordinate equivalences:

```text
levelLinearEquiv T n
  followed by (levelLinearEquiv ((Over.map b).obj T) n).symm.
```

`levelBaseChange_eq_actual` proves that this packaged equivalence is
exactly the actual composite in the first formula, using injectivity of
the target root comparison and `levelEquiv_actualBaseChange`.
Consequently the construction is tied to actual pullback, rather than
to an arbitrary comparison equivalence supplied as data.

`levelEquiv_levelBaseChange` gives the unchanged root coordinate directly
by cancellation of the equivalence and its inverse.
`levelBaseChange_transition` proves compatibility with the actual
quotient-power transition for every `h : n ∣ m`. Applying the injective
target root comparison reduces both sides to the same root transition.

## Integral and away comparisons

For a predicate `P : ℕ → Prop`, `Tate.Index P` consists of positive
integers satisfying `P`. `integralBaseChange b T P` is the continuous
`Global.ProfiniteIntegerRing`-linear equivalence between the selected
actual torsion limits of `Gm S'` at `T` and `Gm S` at
`(Over.map b).obj T`. It composes the published continuous root
comparison at `T` with the inverse comparison at the composed test
scheme. Linearity and continuity in both directions are inherited from
those equivalences.

`integralEquiv_integralBaseChange` states that the coherent root family
is unchanged. `evaluation_integralBaseChange` identifies each coordinate
with `levelBaseChange`; the latter equality is definitional.
`integralBaseChange_eq_actual` proves

```text
integralBaseChange b T P x
  = Tate.integralBaseChange b (Gm S) T P
      (Tate.map T P (Gm.baseChangeIso b).inv x).
```

The proof uses subtype and coordinate extensionality and the finite
actual-pullback formula. This establishes the connection of the bundled
continuous equivalence to the actual torsion inverse limit.

For any natural modulus `m`, `awayBaseChange b T m` uses the selected
orders coprime to `m` and is continuous linear over
`Global.PrimeToProfiniteIntegerRing m`. It is constructed from the
published away root comparisons. `awayBaseChange_apply` identifies
its underlying function with the corresponding selected integral
comparison by reflexivity.

`integralBaseChange_restrictAway` proves that restriction from all
positive orders to the orders coprime to `m` commutes with these maps.
It also holds by reflexivity, since both sides select and compare the
same coordinates.

## Test schemes and affine points

`integralBaseChange_testRestrict` proves naturality for any actual
morphism `a : T' ⟶ T` over `S'`:

```text
C_(b,T') (testRestrict a x)
  = testRestrict ((Over.map b).map a) (C_(b,T) x).
```

The proof applies the injective root comparison, then its base-change
invariance and its existing test-scheme naturality. The two maps on
global sections are definitionally equal.

For any commutative ring object `R` and `t : Spec R ⟶ S'`,
`affineIntegralEquiv_integralBaseChange` states that the affine
comparison with `TateTwist.Divisibility.Integral R P` is unchanged when
the point is composed with `b`. It follows by applying the root map
induced by the canonical `ΓSpecIso R` to
`integralEquiv_integralBaseChange`.

`fullBaseChangeAt b t` and `awayBaseChangeAt b t m` abbreviate the
continuous linear equivalences at the affine point, respectively over
the full and away residue rings. Fields, including geometric-point
fields, are special cases of this affine formulation.
`affineAwayEquiv_awayBaseChangeAt` is the selected affine identity
specialized to the away predicate, with the existing away scalar
bundles.

## Provenance and scope

This unit is internally derived from the published representation of
units by `Gm`, its canonical base-change isomorphism, actual torsion
pullback, and the finite and integral root comparisons. The finite unit
identity is the geometric input; the inverse-limit identities are
proved coordinatewise. No new assertion is attributed to literature.

The unit constructs finite and selected/full/away integral comparisons.
Prime-adic and rational base-change comparisons, fundamental-group
pullback and its compatibility with monodromy, pairing compatibility,
and the identity/composition coherence for iterated base changes remain
separate work. It introduces no chosen roots or twist trivialization
and does not claim completion of the parent PEL infrastructure task.
