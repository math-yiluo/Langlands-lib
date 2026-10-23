# Geometry of a chosen dual parameter scheme over a field

`Langlands.AbelianScheme.FieldDualSchemeGeometryStatement` is a
proposition definition. For every field `k : Type u`, every existing
`A : AbelianScheme (Spec k)`, and every proof `hA : HasDualScheme A`,
it asserts that the structural morphism of the chosen parameter scheme
`dualScheme A hA` is smooth, proper and geometrically connected.

The field is arbitrary: no perfection or algebraic-closedness
hypothesis is imposed. The base is exactly `Spec k`. The statement
adds no hypothesis of projectivity, nor any tensor coherence or
ordinary inverse-bundle input.

## Original source and derived formulation

The source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary draft, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Chapter VI §3, printed p.95 (PDF p.99), discusses representability of
the Picard functor of an abelian variety, the rigidified functor and
the universal Poincaré bundle. Theorem (6.18), printed p.96
(PDF p.100), states that `Pic⁰` is reduced and hence an abelian variety.
Definition (6.19) on the same page calls it the dual abelian variety.
The geometric conclusions recorded here are the smoothness, properness
and geometric connectedness required by the Library's existing
`AbelianScheme` definition.

The target concerns the chosen universal parameter scheme, so it is a
derived consequence rather than a literal transcription about a named
Picard-scheme identity component. The bridge uses paragraph (6.2),
printed p.88 (PDF p.92), for actual universal classification of rigidified
line bundles, and Corollary (7.22), printed p.106 (PDF p.110), for the
identification of `Pic⁰` with the kernel of the line-bundle homomorphism.

In this Library, `HasDualScheme A` asserts existence of an actual
parameter scheme and a rigidified line bundle with
`IsUniversalPicardZero A`. The predicate uses translation invariance
on every geometric fibre. Its universal property classifies families
over every test scheme, including nonreduced ones. The statement's
proof must justify the comparison of this exact functor with the
source's `Pic⁰`; equality only of geometric point sets is insufficient.
It can then use uniqueness of the universal parameter scheme to
transport the geometric properties. The stated route describes the
mathematical derivation needed, not an implemented Lean proof.

## Separation from existence and group laws

The hypothesis `hA` is the existing actual representability proposition;
it is not a tuple of geometric properties. This target neither proves
nor assumes that proposition universally. The separate
`FieldDualSchemeExistenceStatement` asks for its existence.

The tensor, origin and inverse group laws are constructed separately in
`DualGroupScheme` under their displayed inputs. Those constructions
leave the underlying object of `Over (Spec k)` equal to
`dualScheme A hA`. A proof of the present statement can therefore
supply exactly the remaining geometric fields when bundling that group
scheme as an abelian scheme.

No proof or new axiom is supplied here. A separate proof task must
prove this exact proposition. The target claims no arbitrary-base
geometry, projectivity, dimension formula, isogeny theorem, additivity
of dualization or polarization.
