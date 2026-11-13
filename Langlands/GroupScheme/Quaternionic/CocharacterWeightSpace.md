# Weight spaces of a cocharacter of `O(q)` on `D^n`

Author: Worker 73.

Module `Langlands.GroupScheme.Quaternionic.CocharacterWeightSpace`, namespace
`Langlands.GroupScheme.Quaternionic.FirstKindInvolution`. This module contains two
definitions and no theorem. It supports the statements
[`IsometryMaximalSplitTorusWeightsStatement`](MaximalSplitTorusWeightsStatement.md) and
[`SpinCoverVectorWeightsStatement`](../SimplyConnected/SpinCoverVectorWeightsStatement.md).

## Setting

`K` is a field and `D : Type u` a finite-dimensional division `K`-algebra. `σ` is an
involution of the first kind of `D` (published module `Quaternionic.Involution`). `n` is a
finite type of coordinates. `q : σ.QuadraticForms n` is an element of the Library's
fixed-sign quotient `M_n(D) ⧸ {X - ᵗX^σ}` (published module `Quaternionic.Forms`).
`σ.isometryGroup q` is the published isometry group scheme `O(q)` over `Spec K` (module
`Quaternionic.GroupSchemes`). It comes with the closed inclusion `σ.isometryGroupι q` into
the unit group scheme of the finite `K`-algebra `M_n(D)`. No characteristic, centrality,
involution-type, nondegeneracy or smoothness hypothesis is used here.

The fixed-sign quotient is not always Tits's space of `σ`-quadratic forms. Tits 1968, §2
(source `tits-1968-formes-quadratiques-clifford`, printed pp. 20–23, PDF pp. 3–6) divides
by `{X - ε ᵗX^σ}`, where `ε = ±1` is the type of the involution. The Library quotient is
Tits's construction only when `D` is central and `σ` has type `1`, that is, when its
symmetric elements have dimension `d(d + 1)/2` for `D` of degree `d`. In characteristic 2
this holds for every involution of the first kind, since there `ε = −1 = 1`. For an
involution of type `−1` in characteristic different from 2, Tits uses the opposite sign,
and the Library quotient is a different object. The definitions below are internal: they
are stated for the Library quotient in general. Statements that use them and invoke Tits's
results, such as `IsometryMaximalSplitTorusWeightsStatement`, add the centrality and type-1
hypotheses themselves.

## `isometryAffineUnitsOver`

`σ.isometryAffineUnitsOver q R` is a monoid homomorphism. Its source is the group of
points of `O(q)` with values in a commutative `K`-algebra `R`, that is, morphisms
`Spec R ⟶ O(q)` over `Spec K` (`GroupScheme.affinePoints`). Its target is the unit group
`(R ⊗[K] M_n(D))ˣ`. It composes a point with the closed inclusion `σ.isometryGroupι q`,
then applies the published identification `FiniteAlgebraUnits.affinePointsEquiv` of the
`R`-points of the unit group scheme with `(R ⊗[K] M_n(D))ˣ`. For `R = K` it agrees with
the published `isometryAffineUnits`, which this definition generalizes to every
coefficient algebra. (It is unrelated to the published `isometryUnits` of module
`Quaternionic.QuaternionicMoritaIsometryProof`, a subgroup of units defined from a
representative matrix.)

## `cocharacterWeightSpace`

Let `f : 𝔾_m ⟶ O(q)` be a homomorphism of group schemes over `Spec K` (a cocharacter of
`O(q)`), and let `c ∈ ℤ`. Then `σ.cocharacterWeightSpace q f c` is the subset of row
vectors `v ∈ D^n` (functions `n → D`) satisfying the following condition. Take any
commutative `K`-algebra `R` and any point `t ∈ 𝔾_m(R)`. Let `u ∈ (R ⊗[K] M_n(D))ˣ` be the
unit `σ.isometryAffineUnitsOver q R (f(t))`. Transport `u⁻¹` to a matrix over
`R ⊗[K] D` by the published algebra isomorphism
`TensorMatrix.equiv R n : R ⊗[K] M_n(D) ≅ M_n(R ⊗[K] D)`. Then

`(1 ⊗ v) · u⁻¹ = t^c ⊗ v` in `(R ⊗[K] D)^n`.

Here `(1 ⊗ v)` is the row vector with entries `1 ⊗ v_i`, and the product is the row-vector
product `Matrix.vecMul`. The unit `t ∈ Rˣ` attached to the point is the published
`Gm.affineUnitsEquiv`, and `t^c ⊗ v` is the row vector with entries `t^c ⊗ v_i`.

So `v` has weight `c` for `f`: `f(t)` acts on it by `t ↦ t^c` on points with values in
every commutative `K`-algebra. The action is the one used throughout the Library's
quaternionic modules: a point `u` of `O(q)` acts on row vectors by inverse right
multiplication `v ↦ v u⁻¹`, as in the published `isometryRowAction`. Exchanging `u` for
`u⁻¹` would only replace each weight `c` by `-c`.

The set is a left `D`-submodule of `D^n`. The three proof obligations in the definition
check this.

* It is closed under addition, because `Matrix.vecMul` is additive in the row vector.
* It contains `0`, because `0 · u⁻¹ = 0`.
* It is closed under left multiplication by `a ∈ D`. Indeed `1 ⊗ (a v_i)` is the product
  `(1 ⊗ a)(1 ⊗ v_i)`, so `(1 ⊗ a v) · u⁻¹ = (1 ⊗ a) · ((1 ⊗ v) · u⁻¹)`. This equals
  `(1 ⊗ a)(t^c ⊗ v_i) = t^c ⊗ a v_i` entrywise.

The condition is imposed with every coefficient algebra `R`, not only at `K`-rational
points. This matters over finite fields, where `𝔾_m(K)` is finite and rational points do
not detect weights.

## Provenance

This is an internal derived definition. It formalizes the usual weight-space decomposition
of the natural representation of `O(q)` on `D^n` restricted to a one-parameter subgroup.
The literature uses this decomposition only in the settings where the Library quotient
agrees with the classical forms, as explained above. Tits describes the classical indices
of type `D_n` through it, for a central division algebra and a type-`1` involution: see the
type `D_n` entries of Table II in Tits 1966 (source
`tits-1966-classification-algebraic-semisimple`, printed pp. 56–57, PDF pp. 61–62).
Borel–Tits 1965 4.24 uses it for an ordinary quadratic form, the case `D = K`, to compare
the rank of `O(Q)⁰` with the index of `Q` (source `borel-tits-1965-groupes-reductifs`,
printed p. 99, PDF p. 40). The functor-of-points form is chosen so that it has the
intended meaning over every field, including finite fields and fields of characteristic 2.
