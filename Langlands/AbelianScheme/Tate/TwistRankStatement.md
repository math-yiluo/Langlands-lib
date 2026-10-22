# Rank one of the actual integral Tate twist

`Langlands.TateTwist.IntegralRankOne Ω p` is a proposition-valued definition.
It states that if the field `Ω` is separably closed and the prime `p` is
nonzero in `Ω`, then there exists a `ℤ_[p]`-linear equivalence

```text
ℤ_[p] ≃ₗ[ℤ_[p]] Langlands.TateTwist.Integral Ω p.
```

The equivalence is expressed with `Nonempty`; it is neither supplied as input
nor chosen by this module. The target is the published inverse limit of the
actual groups of `p ^ n`-th roots of unity, with power-by-`p` transitions and
the residue-defined `ℤ_[p]`-module structure. It is not an arbitrary line.

## Source correspondence

The source is B. Edixhoven, G. van der Geer and B. Moonen, *Abelian Varieties*,
preliminary draft built 2012-02-08, Chapter X (10.8), printed p.144
(PDF p.148), with the field and prime convention on printed p.141
(PDF p.145). Registered source:
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The original passages were read directly. No source-specific errata file
was present in the available Library.

In (10.8), the source defines the twist from roots of unity over a separable
closure and states that its underlying module is free of rank one. The
chapter's prime is different from the characteristic. The Lean condition
`(p : Ω) ≠ 0` is precisely that restriction for a field and prime `p`.
The source's separable closure is separably closed. Conversely, an arbitrary
separably closed field can be viewed as its own separable closure, so the
statement needs no auxiliary ground field.

A linear equivalence with the scalar ring is the concrete module-theoretic
form of being free of rank one. This formulation includes freeness, rather
than asserting only a numerical rank for a potentially nonfree module.
The source's multiplicative notation for roots of unity becomes additive
notation through the published `Additive (rootsOfUnity _ Ω)` levels.

## Status and scope

This module states the existence theorem and does not prove it. A separate
proof must construct compatible generators or an equivalent argument from
the actual roots of unity. No generator, finite-level basis, compatible
primitive-root system, or inverse-limit comparison is assumed here.

The claimed equivalence is algebraic and generally noncanonical. It is not
asserted to commute with Galois actions, to trivialize the cyclotomic
character, or to preserve a chosen topology. No roots of unity are chosen
in the definition, and the published natural automorphism action on the
twist is unchanged. Rational rank, full and away twists, geometric
monodromy, and pairings are outside this statement.
