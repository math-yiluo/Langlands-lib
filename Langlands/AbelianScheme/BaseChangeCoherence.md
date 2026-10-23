# Abelian-scheme and rational-category base-change comparisons

This module constructs canonical natural isomorphisms for identity and
successive base change of actual abelian schemes and of their category with
rationalized homomorphisms. All declarations are in
`Langlands.AbelianScheme`. The bases are schemes in a common universe, and
the base morphisms `b : S' ⟶ S` and `c : S'' ⟶ S'` are arbitrary.

## Provenance

This is derived infrastructure for Harris–Taylor, *The Geometry and
Cohomology of Some Simple Shimura Varieties* (2001), printed p.18 / PDF p.26,
and Section III.1, printed p.91 / PDF p.99. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
Page 18 supplies the convention of rationalized actual Hom groups and
isogenies as invertible rational homomorphisms. Page 91 supplies their use
in the pointed PEL problem. The source motivates the construction; these
specific natural-isomorphism implementations are derived here.

The geometric comparisons are the actual group-scheme isomorphisms from
`Tate.BaseChangeCoherence`, built from Mathlib's `Over.pullbackId` and
`Over.pullbackComp`. No comparison map is assumed as input.
`AbelianScheme.Basic` defines abelian-scheme morphisms as the additive
notation for the underlying group-scheme morphisms, so these same
comparisons define abelian-scheme isomorphisms. The existing
`RationalBaseChange` functor extends actual pullback to
`Hom0 A B = ℚ ⊗[ℤ] (A ⟶ B)`.

## Integral comparisons

`baseChangeIdIso A` has type `(id_S)*A ≅ A`.
`baseChangeCompIso b c A` has type `(c ≫ b)*A ≅ c*(b*A)`.
Their homomorphisms and inverses are precisely the corresponding
group-scheme maps, wrapped with `Additive.ofMul`. The inverse equations
follow by applying that wrapper to the group-scheme inverse equations.
The source and target abelian schemes are the actual pullbacks, with
smoothness, properness and geometrically connected fibres supplied by
the existing base-change construction.

`baseChangeIdNatIso` and `baseChangeCompNatIso b c` assemble these
isomorphisms into natural isomorphisms of functors. The proof uses
naturality of Mathlib's lifted group-object comparisons on the underlying
group homomorphism of an abelian-scheme map, then applies the same
additive wrapper.

## Rational comparisons and Hom transport

`rationalBaseChangeIdIso A` and `rationalBaseChangeCompIso b c A`
are the images of the integral comparisons under
`Rationalization.inclusion.mapIso`. Thus their homomorphisms are
`1 ⊗` the integral comparison homomorphisms, and their inverses are
`1 ⊗` the corresponding inverses.

Write `I_A : (id_S)*A ⟶ A` for the integral identity comparison and
`C_A : (c ≫ b)*A ⟶ c*(b*A)` for the integral composition comparison,
and use the same notation for their rational inclusions.
For every actual rational morphism `f : Hom0 A B`,
`rationalBaseChangeHom_id` proves

```text
(id_S)*f ≫ I_B = I_A ≫ f.
```

`rationalBaseChangeHom_base_comp b c` proves

```text
(c ≫ b)*f ≫ C_B = C_A ≫ c*(b*f).
```

These equations are written in Lean with the existing bilinear
composition `comp0`. Tensor induction reduces `f = q ⊗ g` to
integral naturality; the coefficients simplify using `q * 1 = 1 * q`.
Additivity of the pullback maps and bilinearity of composition handle
sums. These equations apply in particular when `A = B`, and to the
homomorphisms and inverses of rational isogenies.

Finally, `rationalBaseChangeIdNatIso` and
`rationalBaseChangeCompNatIso b c` assemble the rational comparisons
into natural isomorphisms on the entire rationalized category, using
these two Hom transport equations for naturality.

## Scope

The comparisons and equations require no finite-étale or rank assumption,
connectedness of the base, geometric point, or invertibility of torsion
orders. They establish identity and binary composition comparisons and
naturality, without asserting separate triangle or pentagon coherence
laws. They do not establish compatibility of the comparison components
with tensor-algebra actions on Tate modules, fundamental-group actions,
Weil pairings, or invariant frame orbits. Those applications remain
separate obligations.
