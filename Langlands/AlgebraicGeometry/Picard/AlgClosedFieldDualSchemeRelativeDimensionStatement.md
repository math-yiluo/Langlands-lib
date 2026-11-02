# The dual of an abelian variety has the same relative dimension

`Langlands.AbelianScheme.AlgClosedFieldDualSchemeRelativeDimensionStatement`
is a proposition definition. For every algebraically closed field
`K : Type u`, every `A : AbelianScheme (Spec (CommRingCat.of K))`, every proof
`hA : HasDualScheme A` and every natural number `g`, it asserts that

```text
A.HasRelativeDimension g → SmoothOfRelativeDimension g (dualScheme A hA).hom
```

that is, if the structure morphism of `A` is smooth of relative dimension `g`,
then so is the structure morphism of the chosen dual parameter scheme
`dualScheme A hA` to `Spec K`. `AbelianScheme.HasRelativeDimension g` is the
Library's abbreviation for Mathlib's `SmoothOfRelativeDimension g A.X.hom`, so
hypothesis and conclusion use the same Mathlib predicate. No proof or new
axiom is given here.

The field is algebraically closed, the base is exactly `Spec K`, and the
declaration is universe-polymorphic in `u`. No projectivity of `A`, ample line
bundle or other hypothesis is added.

## Original source and derived formulation

The source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary draft, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`. Theorem (6.18), printed
p.96 (PDF p.100), states that for an abelian variety `X` over a field `k`,
`Pic⁰_{X/k}` is reduced, hence an abelian variety, and that
`dim Pic⁰_{X/k} = dim X = dim_k H¹(X, O_X)`. Definition (6.19) on the same page
names this abelian variety the dual `Xᵗ` of `X`.

The statement is derived content. It concerns the Library's chosen universal
parameter scheme `dualScheme A hA`, not a named identity component of a Picard
scheme. `HasDualScheme A` asserts the existence of a parameter scheme with a
rigidified family that satisfies `IsUniversalPicardZero A`. This property
classifies families over every test scheme, including nonreduced ones, by
translation invariance on fibres over algebraically closed fields. A proof
must compare this functor with the source's `Pic⁰`. Smoothness of relative
dimension `g` combines two parts of the source theorem: the dual is an
abelian variety, hence smooth, and its dimension is `dim X`. The source's
proof of the dimension bound `dim Pic⁰ ≥ dim X` uses the existence of an
ample line bundle. The statement restricts to algebraically closed fields
because that is the case its consumer needs.

## Role

This statement is a prerequisite of the exact proof of
`Langlands.AbelianScheme.AlgClosedFieldPoincareDirectImageStatement`, which
follows the second proof of Theorem (9.1) in the same source, (9.6)–(9.9). That
proof needs the local ring of `dualScheme A hA` at its origin to be a regular
local ring of Krull dimension `g`. Mathlib-level arguments give this from the
present statement: smoothness gives local finite type and regular stalks, and
relative dimension `g` gives the dimension at the closed origin.

The statement and initial exposition are reused from Worker 975's shared
draft. Worker 445 checked the exact formulation against the task and the
cited original passages and prepared this pair for independent review.
