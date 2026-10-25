# Smoothness of a chosen dual parameter scheme over a field

`Langlands.AbelianScheme.FieldDualSchemeSmoothStatement` is a proposition
definition. For every field `k : Type u`, every existing
`A : AbelianScheme (Spec k)`, and every proof `hA : HasDualScheme A`, it
asserts

```text
Smooth (dualScheme A hA).hom
```

that is, the structural morphism of the chosen parameter scheme
`dualScheme A hA` to `Spec k` is smooth.

The field is arbitrary: there is no perfectness or algebraic-closedness
hypothesis. The base is exactly `Spec k` and the declaration is
universe-polymorphic in `u`. No projectivity of `A`, ample line bundle,
tensor coherence, inverse-bundle input or dimension formula is assumed.

## Original source and derived formulation

The source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary draft, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Chapter VI §3, printed p.95 (PDF p.99), admits that `Pic_{X/k}` is a group
scheme over `k` and identifies it with the functor of line bundles rigidified
along the zero section. Theorem (6.18), printed p.96 (PDF p.100), states
that `Pic⁰_{X/k}` is reduced, hence an abelian variety, of dimension
`dim X = dim_k H¹(X, O_X)`. Smoothness over `k` is part of being an abelian
variety. Definition (6.19) on that page names this abelian variety the dual
of `X` and restricts the Poincaré bundle to it. Paragraph (6.2), printed
p.88 (PDF p.92), describes the universal property by actual pullback of
rigidified line bundles along a unique parameter morphism.

The statement concerns the Library's chosen universal parameter scheme, not
a named identity component of a Picard scheme, so it is a derived
consequence of the source theorem. In this Library `HasDualScheme A` asserts
the existence of a parameter scheme and a rigidified family satisfying
`IsUniversalPicardZero A`, whose class predicate is translation invariance on
every algebraically closed field-valued fibre, and whose universal property
classifies families over every test scheme, including nonreduced ones. A
proof must compare this functor with the source's `Pic⁰`; Corollary (7.22),
printed p.106 (PDF p.110), identifies `Pic⁰` with the kernel of the
line-bundle homomorphism map and motivates that comparison. Equality of
geometric point sets alone is not enough for smoothness, since the statement
is scheme-theoretic.

## Role

This is one of three inputs from which the Library target
`FieldDualSchemeGeometryStatement` (smooth, proper and geometrically
connected) follows by Mathlib arguments: smoothness supplies the smooth
field and local finite type; separatedness
(`FieldDualSchemeSeparatedStatement`) and a surjection from `A`
(`FieldDualSchemeSurjectionStatement`) supply the rest. No proof or new axiom
is given here.

The Lean statement and initial exposition are reused from Worker 268's
shared design for the parent geometry proof. Worker 432 checked the cited
original passages and prepared this focused statement for independent review.
