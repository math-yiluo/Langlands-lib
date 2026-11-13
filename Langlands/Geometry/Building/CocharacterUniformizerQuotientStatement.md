# Integral and common-uniformizer quotients

Author: Worker 1222.

`Langlands.GroupScheme.CocharacterUniformizer.QuotientComparisonStatement`
compares two actual quotient groups over any nonarchimedean local field
`F : Type u`, in either characteristic. Let `T` be an actual split torus,
let `A` be any actual commutative group scheme over `F`, and let `f : A → T`
be any actual commutative-group-scheme morphism.

Write `N` for the image in `T(F)` of the existing common-uniformizer
subgroup `CocharacterUniformizer.CA F A`, and let `q : T(F) → T(F)/N` be
the group quotient map. The statement asserts a group isomorphism from the
integer cocharacter lattice of `T`, modulo the image of the published
postcomposition map `RealTorusSpace.cocharacterMapInt f`, onto the subgroup
`(CA F T).map q`. The additive lattice quotient is written multiplicatively
using Lean's `Multiplicative` type synonym.

The isomorphism is required to send the class of every integral cocharacter
`c` to the class of its value at the existing chosen uniformizer. This
formula specifies the isomorphism on all quotient representatives. The
target is the image of `C_T` in the ambient quotient `T(F)/N`; it expresses
the quotient of `C_T` by `N`, since common-uniformizer naturality puts
`N` inside `C_T`. No presentation or generators for either quotient are
chosen. The source group scheme `A` need not be split or of finite type,
and `f` need not be monic. Splitness of `T` supplies the injectivity of its
common-uniformizer section. This file states the proposition and supplies
no proof.

This is a derived comparison motivated by David Renard, *Représentations
des groupes réductifs p-adiques*, French version dated 9 July 2026,
V.2.5, printed p.107 / PDF p.113, and V.3.24, printed p.117 / PDF p.123,
registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
V.2.5 identifies each split-torus uniformizer subgroup with its integral
cocharacters and records compatibility with split inclusions. V.3.24
uses the quotient relation whose difference lies in the common-uniformizer
subgroup of the split component of the ambient reductive group. The
present statement isolates the quotient comparison for arbitrary actual
morphisms into split tori; its scope for `A` and `f` is an internal
generalization.

The intended proof uses published common-uniformizer naturality and
injectivity of the section of `T`. The kernel of `q` composed with that
section is precisely the image of integral postcomposition along `f`.
The first isomorphism theorem then gives the displayed isomorphism and its
representative formula. All constructions in the statement are existing
shared objects.

The identification of this cocharacter image with a simple-root
annihilator, restriction to a nonnegative monoid, finite generation and
decomposition into strict faces remain separate obligations. No freeness
claim from V.3.24 is asserted here.
