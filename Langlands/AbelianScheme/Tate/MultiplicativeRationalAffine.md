# Affine rational and adelic Tate comparisons for the multiplicative group

This is an internal scalar-extension construction from the actual integral
affine comparisons in `MultiplicativeDivisibilityAffine`. It also uses the
published rational Gm comparison in `MultiplicativeRational` and the existing
full and away scalar actions on Tate modules and roots-of-unity twists.
No additional assertion from the original literature is used.

## Inputs and rationalization

Let `S` be any scheme, `R` a commutative ring object, and `f : Spec R ⟶ S`.
For any predicate `P : ℕ → Prop`, `affineRationalEquiv f P` identifies the
rationalization of the actual selected Gm torsion-section limit over `Spec R`
with the rationalization of the corresponding selected roots-of-unity limit
in `R`. The selections retain the positive orders satisfying `P`.

Both carriers are written `ℚ ⊗[ℤ] Integral`. The construction forgets
`affineIntegralEquiv f P` to its canonical integer-linear equivalence,
then extends scalars from the integers to the rationals.
`affineRationalEquiv_tmul` and its inverse formula describe the maps on
pure tensors. `affineRationalEquiv_toRational` states compatibility with
the canonical maps `x ↦ 1 ⊗ x`; it does not assert their injectivity.

`affineRationalEquiv_apply` identifies this rationalized affine map with
`rationalEquiv (Over.mk f) P` followed by the root-induced rational map of
the canonical section isomorphism `Scheme.ΓSpecIso R`.
The inverse formula uses its inverse section map before the inverse
rational Gm comparison. Both proofs use tensor induction: pure tensors
are definitional, and the additive case follows by linearity.

## Full residue and finite-adelic scalars

`affineRationalEquiv_scalarAction` intertwines the existing actions of
`ℚ ⊗[ℤ] Global.ProfiniteIntegerRing`. It applies the general scalar-extension
compatibility theorem `TateScalarExtension.map_action` to the actual integral
affine equivalence, which is linear over the profinite-integer ring.

For an explicit hypothesis
`h : Global.RationalProfiniteIntegerAdeleComparison`,
`affineRationalEquiv_finiteAdeleAction` evaluates this compatibility at
the inverse comparison image of a finite adele.
`affineFiniteAdeleEquiv` bundles the same underlying map as a linear
equivalence over `Global.FiniteAdeles ℚ`. Its type and body locally install
the previously constructed `finiteAdeleModule` structures using the same
`h` on both sides. The application formula confirms that the function
is unchanged.

## Full and away selections

`affineFullRationalEquiv` specializes to the constantly true predicate.
`affineAwayRationalEquiv f m` specializes to `Nat.Coprime n m` for an
arbitrary natural number `m`.

`affineAwayRationalEquiv_scalarAction` intertwines the existing actions of
`ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m`. Its proof uses
`TateScalarExtension.map_action` for `affineAwayEquiv`, whose underlying
additive equivalence agrees with the selected integral affine map.

Given the coupled hypothesis
`hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m`,
the corresponding action theorem intertwines the actual away finite-adelic
actions. `affinePrimeToFiniteAdeleEquiv` bundles this as a linear equivalence
over `Global.PrimeToFiniteAdeles m`, with the local source and target
`primeToFiniteAdeleModule` structures. Its underlying function remains
`affineAwayRationalEquiv`. The full hypothesis `h` remains a parameter
through the type of `hAway`. Neither scalar-comparison hypothesis is
proved here.

## Restriction compatibility

The two rational `restrictAway` theorems assert that the affine comparisons
commute with full-to-away coordinate restriction, in both directions.
Tensor induction reduces these equalities to the integral affine restriction
squares. The two finite-adelic versions reuse the same rational formulas,
since the additional scalar bundles do not change the maps.
The full bundle in each such formula uses the same `h` as `hAway`.

All constructions work without characteristic, finiteness, rank or
connectedness hypotheses, without restrictions on the selection predicate,
and without a primality or nonzero hypothesis on `m`.
This unit asserts no rational topology or continuity, test-scheme
base-change or geometric monodromy law, torsion finiteness or rank, chosen
twist trivialization, Weil pairing, or completion of the parent PEL task.
