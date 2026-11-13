# Finite generation of the nonnegative cocharacter quotient

Author: Worker 1222.

`Langlands.GroupScheme.CocharacterConeFiniteGenerationStatement` says that for
any field `k : Type u`, any actual commutative group scheme `T` over `k`, and
any finite set `R` of actual characters of `T`, the existing additive monoid
`CocharacterCone.quotient T R` is finitely generated. This monoid is the image
of the nonnegative integral cocharacters in the quotient by the existing
common integral annihilator. Finite generation is the additive-monoid notion
`AddSubmonoid.FG`: a finite set generates under addition, with nonnegative
integer coefficients.

The statement does not require the cocharacter lattice itself to be finitely
generated, or the group scheme to be a torus, split, reductive or of finite
type. The finite character evaluation embeds its annihilator quotient in a
finite product of copies of the integers. Nonnegative evaluation vectors in
the image form a subtractive submonoid of a finite product of copies of the
natural numbers. Mathlib's `AddSubmonoid.fg_of_subtractive` is the intended
proof input. This file states the proposition and supplies no proof.

The source motivation is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, V.3.23–V.3.24, printed p.117 /
PDF p.123, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This is a derived finite-generation replacement for the source's false general
freeness assertion. For the simple relative roots, it concerns the integral
lattice model underlying the dominant quotient. The extension to an arbitrary
finite set of actual characters is internal. No isomorphism with a free
monoid, number of generators, or decomposition into strict faces is asserted.

Identifying the integral common annihilator with the actual split-central
cocharacter image, and consequently this monoid with the source's quotient by
`C_(A_G)`, remains a separate comparison obligation. This statement does not
claim that comparison or finite generation of the unquotiented nonnegative
monoid.
