# Separatedness of a chosen dual parameter scheme over a field

`Langlands.AbelianScheme.FieldDualSchemeSeparatedStatement` is a proposition
definition. For every field `k : Type u`, every existing
`A : AbelianScheme (Spec k)`, and every proof `hA : HasDualScheme A`, it
asserts

```text
IsSeparated (dualScheme A hA).hom
```

that is, the structural morphism of the chosen parameter scheme
`dualScheme A hA` to `Spec k` is separated.

The field is arbitrary: there is no perfectness or algebraic-closedness
hypothesis. The base is exactly `Spec k` and the declaration is
universe-polymorphic in `u`. No projectivity of `A`, finiteness hypothesis on
the parameter scheme, tensor coherence or inverse-bundle input is assumed.

## Original source and derived formulation

The source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary draft, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Chapter VI §3, printed p.95 (PDF p.99), admits from the general theory that
`Pic_{X/k}` is a group scheme over `k` with projective connected components
and that it represents the functor of line bundles rigidified along the zero
section. Theorem (6.18), printed p.96 (PDF p.100), states that `Pic⁰_{X/k}`
is reduced and hence an abelian variety; separatedness is part of
properness. Definition (6.19) on the same page names this the dual abelian
variety. Paragraph (6.2), printed p.88 (PDF p.92), gives the universal
classification of rigidified line bundles by actual pullback. Corollary
(7.22), printed p.106 (PDF p.110), identifies `Pic⁰` with the kernel of
the line-bundle homomorphism; this motivates the translation-invariance
criterion on geometric fibres used by the Library.

The statement concerns the Library's chosen universal parameter scheme, not
a named identity component of a Picard scheme, so it is a derived
consequence. In this Library `HasDualScheme A` asserts the existence of a
parameter scheme and a rigidified family satisfying `IsUniversalPicardZero A`
(translation invariance on every algebraically closed field-valued fibre,
classification over every test scheme, including nonreduced test schemes).
A proof by comparison with the source’s `Pic⁰` must justify the comparison
of these actual functors; equality of geometric point sets alone is
insufficient. One possible alternative route, recorded only as guidance, uses the group structure on the chosen dual: a `k`-rational point of
any `k`-scheme is closed, so the unit section is a closed immersion, and the
diagonal is a base change of the unit section along `(x, y) ↦ x · y⁻¹`. The
Library's group-scheme constructions on `dualScheme A hA` take displayed
coherence and inverse-bundle inputs, which such a proof must discharge or
avoid.

## Role

This is one of three inputs from which the Library target
`FieldDualSchemeGeometryStatement` (smooth, proper and geometrically
connected) follows by Mathlib arguments; the others are
`FieldDualSchemeSmoothStatement` and `FieldDualSchemeSurjectionStatement`.
No proof or new axiom is given here.
