# The torus zero subgroup is the Kottwitz kernel

`Langlands.Geometry.Building.Kottwitz.TorusKottwitzKernelStatement` states
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (Cambridge, 2023),
§11.1, Proposition 11.1.5, `T(K)^0 = ker(κ_T)`, printed p. 423, PDF p. 454.
The subgroup `T(K)^0` is defined in Definition 2.5.13, printed p. 90,
PDF p. 121. The map `κ_T` comes from Proposition 11.1.1, printed p. 421,
PDF p. 452.

The authors' corrections and additions (version of 1 November 2024) do not
change Proposition 11.1.5: their only Chapter 11 entries concern §11.7.
Their §2.5 entries change the sign in the definition of `ω_T` and replace
Remark 2.5.15. They leave Definition 2.5.13 unchanged, and a sign change does
not affect either side of the statement, since both sides are kernels.

## Setting and scope

KP's Chapter 11 works over a Henselian discretely valued field with perfect
residue field. There `K` is its maximal unramified extension inside a fixed
separable closure, and `T` is a `K`-torus. The Lean statement uses the setting
of the existing map `torusKottwitz`:

* `F` is any nonarchimedean local field, `K = UnramifiedClosure F` is the
  maximal unramified extension of `F` inside `SeparableClosure F` (not its
  completion), and `L` ranges over intermediate fields of `F^sep/K`.
* The torus `T` is a commutative group scheme over a field of definition `k`.
  The field `k` carries algebra maps to `K` and to `F^sep` forming a scalar
  tower, and `K/k` is normal. These are exactly the hypotheses of
  `torusKottwitz`. KP's `K`-torus is the actual base change
  `T_K = (CommGroupScheme.baseChange (baseMap k K)).obj T`. It is a torus
  by `IsTorus.baseChange`, and it is affine by `torusIsAffine`.

Taking `k = K` covers every `K`-torus. Then `T_K` is the base change along the
identity, which is canonically isomorphic to `T`, and
`map_torusNormIwahori_eq_of_iso` transports the norm subgroup along such
isomorphisms. Taking `k = F` covers every `F`-torus. Both specializations
elaborate with the Library's instances, including `IsGalois F K` from
`inertiaFixedField_isGalois`; this was checked in a private
compilation. The field-of-definition parameter is an internal generalization
of KP's presentation. It follows `torusKottwitz` and the reductive
`UnramifiedZeroKernelStatement` pattern. It is used so that the constructed
map, which lives on the original group's coefficient points, can be used
without a supplied comparison.

## The statement

For every such `F`, `k`, `T` and every finite Galois `L/K` inside `F^sep`
over which `T_K` splits, in the form
`IsSplitTorus (baseChanged K L T_K.toGrp)`, we have

```
torusNormIwahori K L (intermediateValuation F L) T_K =
  (torusKottwitz F k T hT).ker.comap (baseChangeCoeffEquiv k K T.toGrp).toMonoidHom
```

as subgroups of the rational points of `T_K`.

**Left side.** `torusNormIwahori` is the image, under the actual Galois
norm `rationalNorm K L T_K : T_K(L) → T_K(K)`, of the existing subgroup
`characterValuationKernel (intermediateValuation F L) (T_K)_L`, i.e. of the
points on which every rational character has valuation one. `T_K` splits over
`L`, so every character of `(T_K)_L` is rational. This kernel is therefore the
bounded subgroup `T(L)^b = T(L)^0` of KP Proposition 2.5.8, and its norm image
is the Iwahori subgroup `T(K)^0` of Definition 2.5.13. It is the same
expression used by `UnramifiedZeroDatum.torusIwahori`. The equality is
asserted for every splitting field `L`, so the statement does not assume that
`T(K)^0` is independent of `L` (KP Lemma 2.5.12). That independence follows
from the statement instead.

**Right side.** `torusKottwitz F k T hT` is the constructed homomorphism
from `torusKPoints F k T`, the `K`-coefficient points
`affinePoints T.toGrp (CommAlgCat.of k K)` of the original group scheme, to
`Multiplicative (TorusTarget F k T)`. That target is the inertia coinvariants
`X_*(T)_I` of the actual geometric cocharacter lattice. Its kernel is a
subgroup of the coefficient points.

**Coefficient-point comparison.** `baseChangeCoeffEquiv k K T.toGrp` is the
Library's multiplicative equivalence from the rational points of
`baseChanged k K T.toGrp` to the `K`-coefficient points of `T`. It sends a
section `x` of `T_K` to its composite with the pullback projection
`T_K → T` (`baseChangeCoeffEquiv_left`). The pulled-back kernel consists of
the `x ∈ T_K(K)` with `torusKottwitz F k T hT (baseChangeCoeffEquiv k K T.toGrp x) = 1`.
The group `rationalPoints (baseChanged k K T.toGrp)` is definitionally
`rationalPoints T_K.toGrp` (`baseChange_toGrp` is `rfl`), so both sides are
subgroups of one group.

## Valuation conventions

The left side uses `intermediateValuation F L`. This is the restriction to `L`
of the spectral valuation `sepClosureValuation F`, the unique extension of
the valuation of `F` to `F^sep`. It takes values in `ℝ≥0` and is written
multiplicatively, so "valuation one" means additive valuation zero.

The map `torusKottwitz` is characterized by the norm square `TorusNormLawAt`
of KP Proposition 11.1.1. That square uses `splitValuation` with
`normalizedIntermediateValuation F L`. This is the `ℤ`-valued valuation chosen
by classical epsilon to have the ordering of the restricted spectral valuation
and to map `L^×` onto the integers, as Proposition 11.1.1 requires. Its
existence is the separate `NormalizedIntermediateValuationStatement`.
Equivalent valuations have the same elements of valuation one, but the
statement does not assume that the two conventions give the same bounded
subgroup. Comparing them, including through the normalized valuation's
specification, is a proof obligation.

The splitting hypothesis here concerns `T_K` base-changed to `L`. The norm
law of `torusKottwitz` instead concerns the direct base change `T_L` from `k`.
The two group schemes are canonically isomorphic by the tower comparison
`towerBaseChangeIso`, and relating the two conditions and the two norms is
likewise left to the proof.

## What is not assumed

No kernel equality, boundedness property or replacement map is supplied as a
premise. `torusKottwitz` is the Library's classical-epsilon choice of a
homomorphism satisfying the norm law at every finite Galois splitting field.
The statement concerns that map and does not assume
`TorusKottwitzExistenceStatement`. A proof therefore has to show that the
selected map satisfies its norm law, as well as the kernel identity.
`KPZeroNormKernel` concerns the different character-valuation kernel and is
not this result. The rational form after Proposition 11.1.5, `T(k)^0 = ker(κ_T)`
for a torus over the base field, is not part of this statement.

KP's proof uses three facts. The norm `T(L) → T(K)` is surjective, and the norm
square gives `T(K)^0 ⊆ ker(κ_T)`. Conversely, an element of the inertia
augmentation submodule is a sum of elements `y - σ y`. A uniformizer `ϖ` of
`L` gives norm-one points `y(ϖ)/σ(y(ϖ))` with exactly these valuations, so a
preimage under the norm can be adjusted into the bounded subgroup.
This file states the proposition and does not prove it.
