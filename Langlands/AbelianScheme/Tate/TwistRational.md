# Rational Tate twists and natural automorphism actions

This module rationalizes the full and prime-to-`p` limits of actual roots of
unity. It constructs the maps induced by ring homomorphisms, integral and
rational equivalences induced by ring equivalences, and the resulting
automorphism and field-Galois actions. The main namespace is
`Langlands.TateTwist.Divisibility`.

## Provenance

This is an internal extension of
`Langlands.AbelianScheme.Tate.TwistDivisibility`. It reuses that module's
coherent root families, residue scalar actions, maps and restriction.
The rationalization and tensor-map proofs adapt Worker 142's
`Langlands.AbelianScheme.Tate.Rational`. The automorphism construction extends
the prime-adic construction in `Langlands.AbelianScheme.Tate.Twist`.
Worker 142 is credited as a coauthor for the rationalization patterns.

The underlying original source is B. Edixhoven, G. van der Geer and B. Moonen,
*Abelian Varieties*, preliminary draft built 2012-02-08, Chapter X (10.8),
printed p.144 (PDF p.148). It describes the prime-adic roots-of-unity twist
and its natural Galois action, with the field and prime convention on
printed p.141 (PDF p.145). Registered source:
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The original passage was read in developing the imported prime-adic
construction and its retained extract was reread for this module. No
source-specific errata file was present in the available Library.

The source does not state the arbitrary-ring and arbitrary-index-predicate
interfaces in this module. Those interfaces are derived by rationalizing
the existing coherent families and applying the ring maps to every root.
No rank or comparison result is inferred from the prime-adic source.

## Rationalization and maps

For any commutative ring `R` and predicate `P : ℕ → Prop`,

```text
Rational R P = ℚ ⊗[ℤ] Integral R P.
```

Here `Integral R P` is the actual roots-of-unity limit indexed by positive
integers satisfying `P`. `RationalFull R` takes all positive integers;
`RationalAway R p` takes those coprime to `p`. The latter is defined for any
natural `p`, with its usual prime-to-`p` interpretation when `p` is prime.
The outer namespace also exports `Langlands.TateTwist.RationalFull` and
`Langlands.TateTwist.RationalAway`.

These tensor products carry the usual additive group and rational vector
space structures. `rationalTensorComm` is the integer-linear tensor
commutation equivalence with `Integral R P ⊗[ℤ] ℚ`; its pure-tensor formula
is proved. `toRational` sends `x` to `1 ⊗ x`. Its injectivity is not part of
this module.

For an actual ring homomorphism `f : R →+* S`, `rationalMap P f` is the
rational-linear scalar extension of the existing additive map `map P f`.
The pure-tensor formula is

```text
q ⊗ x ↦ q ⊗ map P f x.
```

The module proves identity, composition, and compatibility with
`toRational`. Identity and composition are checked on pure tensors using
tensor-product extensionality and the corresponding integral laws.
`rationalRestrictAway` extends the integral restriction from all positive
indices to the indices coprime to `p`. Its pure-tensor formula and
compatibility with `toRational` are definitional; its naturality with
respect to ring maps follows by tensor extensionality from
`restrictAway_map`.

## Equivalences and automorphisms

`mapEquiv P f` for a ring equivalence `f : R ≃+* S` is the additive
equivalence whose forward map is `map P f.toRingHom` and whose inverse
is induced by `f.symm`. The inverse laws follow from integral map
composition and identity.

`fullLinearEquiv` equips that equivalence with linearity over
`Langlands.Global.ProfiniteIntegerRing`; it works for every `P`.
`awayLinearEquiv` equips the away equivalence with linearity over
`Langlands.Global.PrimeToProfiniteIntegerRing p`. Both reuse the
corresponding integral linear maps, so their scalar actions are the
actual residue actions already constructed on the root limits.
`rationalMapEquiv` is the rational scalar extension of the integer-linear
version of `mapEquiv`. Its pure-tensor formula and equality of its
underlying linear map with `rationalMap` are proved.

`automorphismAction R P` is a monoid homomorphism from ring automorphisms
of `R` to full-profinite-integer-linear automorphisms of `Integral R P`.
`awayAutomorphismAction R p` gives the same underlying action on the
away limit, bundled as linear over the away scalar ring. The multiplication
law respects function composition: the product `f * g` applies `g` first,
then `f`. This follows from `map_comp P g.toRingHom f.toRingHom`.

`evaluation_automorphismAction` proves that each coordinate is acted on
by `levelMap f.toRingHom n`. Thus the action is the action on actual
roots, without a choice of primitive roots or a basis. Each fixed
automorphism is continuous on the integral limit by `continuous_map`.
The full and away action formulas agree on the away limit, and
restriction intertwines the two actions.

`rationalAutomorphismAction R P` is a monoid homomorphism into rational
linear automorphisms, constructed using `rationalMapEquiv`. Its monoid
laws follow from the rational map identity and composition laws.
It satisfies

```text
f(q ⊗ x) = q ⊗ f(x).
```

Compatibility with `toRational` is definitional. Equivariance of
`rationalRestrictAway` follows from its naturality under ring maps.

## Field-Galois specialization and scope

For fields `K`, `L` and an algebra structure `K → L`, `galoisAction K L P`,
`awayGaloisAction K L p`, and `rationalGaloisAction K L P` restrict these
natural actions along the canonical homomorphism from `Gal(L/K)` to the
ring automorphisms of `L`. No normality or separability assumption is
needed to define these actions of the field-automorphism group.

This module proves continuity of each fixed integral automorphism.
It does not construct a topology on the automorphism group or prove
joint continuity of the action. It puts no topology on the rational
twists. The rational scalar field provided here is `ℚ`; identification
of rationalized full or away scalar rings with adelic rings, and the
resulting adelic actions, remain separate work.

Rank-one, freeness, prime-adic product comparison, the scheme-theoretic
comparison with points of `μ_n`, geometric fundamental-group actions,
Weil pairings, and a cyclotomic scalar formula for the full and away
actions are also separate obligations. No trivialization of the twist,
equivariant or otherwise, is chosen here.
