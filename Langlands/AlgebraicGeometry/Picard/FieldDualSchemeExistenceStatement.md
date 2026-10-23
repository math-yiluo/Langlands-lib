# Existence of a dual parameter scheme over a field

`Langlands.AbelianScheme.FieldDualSchemeExistenceStatement` is a
proposition definition. For every field `k : Type u` and every
`A : AbelianScheme (Spec k)`, it asserts `HasDualScheme A`.
Unfolding the latter proposition, there exist an actual scheme `P`
over `Spec k` and an actual rigidified line bundle `L` on `P ×_k A`
with `IsUniversalPicardZero A L`. This requires the geometric
Picard-zero condition on `L` and unique classification of every such
rigidified class over every test `k`-scheme by actual pullback of `L`.

The field need not be algebraically closed or perfect. The base of
`A` is exactly `Spec k`; this target says nothing about existence
over an arbitrary base scheme. The universal property still tests
all `k`-schemes, including nonreduced schemes, rather than only
field-valued points.

## Original source and translation

The source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary draft, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Chapter VI §3, printed p.95 (PDF p.99), takes an abelian variety
over a field, invokes representability of its Picard functor, and
identifies this with the rigidified functor with its Poincaré bundle.
Theorem (6.18), printed p.96 (PDF p.100), proves that `Pic⁰` is
an abelian variety; Definition (6.19) on that page calls it the dual
and restricts the Poincaré bundle to it. Paragraph (6.2), printed
p.88 (PDF p.92), spells out the actual universal rigidified pullback
property. Corollary (7.22), printed p.106 (PDF p.110), identifies
the field Picard-zero subgroup with the kernel of the map sending a
line bundle to its associated homomorphism.

This is a derived representability consequence of those passages in
the project's chosen geometric-fibre formulation. In the Library,
`IsPicardZeroFamily` tests translation invariance of the restricted
line bundle at every algebraically closed field-valued point of the
test scheme. This implements the criterion specified in parent-task
item 3; it is not already a formal identification with the identity
component of a Picard scheme. A proof of this target must supply
the comparison and representability arguments required to obtain
the universal family for this exact predicate, including its
classification over all test schemes. It cannot substitute a
classification only on geometric points.

The existing `AbelianScheme` supplies a smooth proper commutative
group scheme with geometrically connected fibres. No projectivity
witness is added as a hypothesis in the field target, in agreement
with the source's statement for an abelian variety over a field.
The usual projectivity result for abelian varieties can be part of
the proof if its chosen route requires it.

## Proof obligation and scope

This file supplies no proof or new axiom. The separate proof task
must prove this exact proposition using the published definitions.
Once such a proof is available, `dualScheme` and `poincareFamily`
select the corresponding scheme and actual bundle, and the
classification constructions apply.

This target asserts existence of the parameter scheme and universal
bundle only. It does not separately construct or certify its
commutative group structure, smoothness, properness, geometric
connectedness, projectivity, or dimension, nor does it assert that
`φ_L` is an isogeny. Those further conclusions of the source
theorem remain distinct obligations.
