# Nonnegative cocharacters and their integral annihilator quotient

Author: Worker 1222.

This derived construction uses the existing character and cocharacter lattices
of an actual commutative group scheme `T` over a field `k : Type u`, and their
integer pairing `latticePairing`. For any set `R` of actual characters,
`CocharacterCone.nonnegative T R` is the additive submonoid of cocharacters
whose pairing with every member of `R` is nonnegative.

`CocharacterCone.quotient T R` is its image in the quotient of the cocharacter
lattice by the existing submodule
`RealTorusSpace.rootAnnihilatorInt T R`. No new lattice or root datum is
introduced. The annihilator consists exactly of the cocharacters for which
both the cocharacter and its negative are nonnegative. Translation by an
annihilator element preserves nonnegativity. The quotient membership lemma
therefore characterizes membership using any representative.

When `k` is a nonarchimedean local field, with the existing normalized
valuation and chosen uniformizer, `latticeSection_mem_CAplus_iff` proves that
the existing common-uniformizer section takes a cocharacter into the existing
`CocharacterUniformizer.CAplus k T R` exactly when it is in this nonnegative
monoid. The proof uses the published formula
`|alpha(nu(pi))| = q^(-<alpha,nu>)` and `q > 1`. This comparison does not need
splitness or injectivity of the section. There are no characteristic or
positive-rank restrictions.

The motivating source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, V.3.23–V.3.24, printed p.117 /
PDF p.123 (registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
For the simple relative roots of a minimal parabolic and its maximal split
torus, this is the integral lattice model relevant to the dominant section
`C_emptyset^+`. The generalization to any set of actual characters is internal
and needs no reductivity, finiteness, or independence assumptions.

The quotient here is by the integral common annihilator. Its identification
with the image of the split central component, and consequently with Renard's
quotient by `C_(A_G)`, is a separate structural comparison. Finite generation
has not been stated or proved in this unit. A finite-character version can use
Mathlib's `AddSubmonoid.fg_of_subtractive` in
`Mathlib.GroupTheory.Finiteness`; no new generic Gordan proof is needed.

Renard's stronger assertion that this monoid is free on as many generators as
there are simple roots is false in general. For `SL_3`, simple-root
coordinates give the monoid `{(p,q) in N^2 | p = q mod 3}`. The indecomposable
elements `(3,0)`, `(0,3)`, and `(1,1)` satisfy
`(3,0) + (0,3) = 3*(1,1)`. This unit makes no freeness claim and does not
formalize the source's subsequent decomposition into strict faces.
