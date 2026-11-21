# The induced character formula at regular semisimple points

This module states, without proof, the ordinary (untwisted) case of
Henniart–Lemaire (2011), II.4.5, formula (3), printed p. 88 (PDF p. 96). The
authors note there that the untwisted formulas are obtained by replacing `E` by
`F` and `σ` by the identity.

## The weight

`relativeDiscriminantWeight B m` is the complex number
`|D_{G/M}(m)|_F^{-1/2}`. Here `m ∈ M(F) = B.Levi F`, and
`D_{G/M}(m) = det_F(1 - Ad(m)⁻¹; g(F)/m(F))` is the Library's
`relativeParabolicDiscriminant B F m` (printed p. 87). `|·|_F` is the
normalized absolute value `LocalField.residueNormalizedAbsoluteValue F`. The
weight is defined as `(√|D|)⁻¹`, which is `0` when `D = 0`. For regular `m` the
Library's `relativeParabolicDiscriminant_ne_zero` shows `D ≠ 0`.

## The statement

`InducedCharacterFormulaStatement.{u, uV}` quantifies over a nonarchimedean
local field `F` in universe `u` of any characteristic, a positive rank `n`, a
block shape `B` of `n`, and block representations `π i` of `GL_{n_i}(F)` on
complex spaces `V i` in universe `uV`, each admissible and irreducible. It
further quantifies over a regular semisimple `γ ∈ GL_n(F)`, a Levi class system
`m : Fin k → B.Levi F` for `γ` (`IsLeviClassSystem`), and complex numbers
`a j`. Suppose the Levi tensor representation `B.blockTensor π` (the Library's
external tensor product `Ξ = π_1 ⊗ ⋯ ⊗ π_r` of `M(F)`) has character value
`a j` at each `m j`, in the sense of the Library's `HasCharacterValue`. Then the
normalized product induction `(LocalFieldData.ofInstances F).normalizedProductInduced B π`
has character value

`∑ j, |D_{G/M}(m j)|_F^{-1/2} * a j`

at `γ`. The topological instances on `GL_{n_i}(F)`, `M(F)` and `GL_n(F)` are the
Library's `LocalFieldTopology` certificates, with product instances on the
Levi.

## Relation to the source

Henniart–Lemaire state (3) for `γ` in a maximal torus `T` of `M` over `F`,
summing over the finite set `W` of II.4.5. By the bijection explained in
`LeviClassSystem.md`, the sum over `W` of the `M(F)`-invariant terms equals the
sum over any Levi class system. Character values are invariant under
conjugation, so the statement for every regular semisimple `γ` follows from the
case `γ ∈ T(F)`. If `γ` is conjugate to no element of `M(F)`, the empty Levi
class system makes the value zero. This is the vanishing assertion in the same
paragraph.

The source assumes the `π i` admissible of finite type. The statement assumes
them irreducible, which implies finite type. The induced representation is not
assumed irreducible. The character values of the factors are hypotheses, so the
statement does not assert that characters are given by functions. The
statement is a target for later proofs. The Library does not prove it, and
consumers use it only as an explicit premise.
