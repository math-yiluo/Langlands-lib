# Ground base change of Weil pairings along actual homomorphisms

Let `b : S' ⟶ S`, let `A` be an abelian scheme over `S`, and write
`A' = (baseChange b).obj A`. The duals `DA` and `DA'` are the existing
`dualAbelianSchemeFromEvaluation` constructions. Their representability, geometry,
and inverse Poincaré evaluation data are explicit. The seven named tensor/Picard inputs
and `universality : PicardZeroUniversalBaseChangeStatement` remain explicit as well.
For a test scheme `T` over `S'`, put `T₀ = (Over.map b).obj T`. Its underlying scheme
is still `T.left`.

## The actual base-changed map

`canonicalDualValuedBaseChange … lam` specializes the published
`dualAbelianBaseChangeMap` to the published proof `dualAbelianBaseChange` of
`DualAbelianBaseChangeStatement`. For any actual homomorphism `lam : A ⟶ DA`, it is
`(baseChange b).map lam` followed by the forward canonical dual abelian-scheme comparison.
Thus its target is the actual constructed dual of `A'`. This convenience definition
uses the already proved group compatibility; it introduces no new geometric theorem
and requires no additional proof of that compatibility from its caller.

`groupHom_dualAbelianBaseChangeIso` identifies the group homomorphism underlying that
abelian comparison with the forward map of the existing `dualGrpBaseChangeIso` used by
[WeilBaseChange](WeilBaseChange.md). The proof uses `Grp.hom_ext` and the published
`dualAbelianBaseChangeIso_hom`: both underlying maps are the prescribed
`dualSchemeBaseChangeIso`. Consequently the new map and the dual Tate comparisons
use the same canonical comparison, with opposite directions where appropriate.

## Tate-map squares

For an order `n` and an actual torsion point `y` of `A'` over `T`,
`dualLevelBaseChange_canonicalDualValuedBaseChange` proves

`dualLevelBaseChange(T(lam')(y)) = T(lam)(levelBaseChange(y))`,

where `lam' = canonicalDualValuedBaseChange(lam)` and the maps in this equation
are the finite torsion maps. The proof rewrites `groupHom(lam')` as the pulled-back
`groupHom(lam)` followed by `dualGrpBaseChangeIso.hom`. On underlying sections,
postcomposition by its inverse cancels that last map. The published
`levelBaseChange_map` then supplies naturality of the pullback adjunction.

`dualIntegralBaseChange_canonicalDualValuedBaseChange` proves the same square on
actual coherent families by coordinate extensionality.
`dualRationalBaseChange_canonicalDualValuedBaseChange` proves it after rationalization
over `ℤ → ℚ`, using tensor induction, the integral square on pure tensors, and additivity.
These three results do not require quasi-separated bases or any relative Weil-transition
hypothesis. The predicate `P : ℕ → Prop` selects positive orders as in the existing Tate
module definitions. Full and away systems are its usual specializations.

## Pairing compatibility

The pairing results assume quasi-separated `S` and `S'`. The integral and rational
results also retain `compatibility : RelativeFiniteWeilTransitionStatement`.
`finiteWeilLevelAlongHom_baseChange` proves

`e_n(A', x, T(lam')(y)) =
 e_n(A, levelBaseChange(x), T(lam)(levelBaseChange(y)))`.

It applies the published finite intrinsic pairing equation and then the finite map square.
It holds for every natural order `n` for which the existing level construction is defined;
there is no additional invertibility or finiteness assumption in this comparison.

`integralWeilAlongHomBilinearMap_baseChange` and
`rationalWeilAlongHomBilinearMap_baseChange` similarly identify the existing second-variable
pullback pairings of `lam'` and `lam`, using the actual integral or rational primal
base-change equivalence on both arguments. Their proofs expose the second-variable
homomorphism map, apply the corresponding intrinsic equation from `WeilBaseChange`,
and use the respective Tate-map square.

`adelicWeilAlongHomBilinearMap_baseChange` gives the equation with
`GroupScheme.Tate.finiteAdeleBaseChange` and one shared full scalar comparison `h`.
`awayAdelicWeilAlongHomBilinearMap_baseChange` uses
`primeToFiniteAdeleBaseChange` and one coupled `hAway`. Each is the rational equation
on the underlying values of the published adelic bundles. The away modulus `m` is an
arbitrary natural number; no primality assumption is introduced.

In all these equations both values lie in the same actual roots-of-unity twist over
`Γ(T.left, ⊤)`, since `T` and `T₀` have the same underlying scheme. The finite normalization
is `beta(y)(x)`, and `lam` acts in the second variable throughout. No roots of unity,
basis, or twist trivialization is chosen.

## Provenance and scope

This unit is derived from the Library's
[DualAbelianBaseChange](../../AlgebraicGeometry/Picard/DualAbelianBaseChange.md),
[DualAbelianBaseChangeProof](../../AlgebraicGeometry/Picard/DualAbelianBaseChangeProof.md),
[FiniteWeilBaseChange](../../AlgebraicGeometry/Picard/FiniteWeilBaseChange.md),
[WeilBaseChange](WeilBaseChange.md), and [WeilRationalAlongHom](WeilRationalAlongHom.md).
The finite comparison behind this derivation follows the base-change-compatible character
construction in Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft
built 2012-02-08, Chapter VII, Proposition (7.4) and Theorem (7.5), printed pp.99–100 /
PDF pp.103–104. Chapter XI, Definition (11.11), printed p.162 / PDF p.166, specifies
`beta(y)(x)` and the second-variable homomorphism pullback. The relative comparison laws
here are the explicit deductions from the published Library constructions described above;
they are not new existence results quoted from the field-level source.
Harris–Taylor (2001), printed p.18 / PDF p.26, gives the full and away Tate rationalizations;
Section III.1, printed p.91 / PDF p.99, supplies their pointed PEL motivation.

The map `lam` is any actual dual-valued homomorphism; this unit asserts neither that it
is a polarization nor that the constructed map preserves a polarization predicate.
Alternation, nondegeneracy, rank, finite-level perfectness, compact-open topology,
compatible-frame transport, and unpointed canonicity are separate obligations. All named
tensor, Picard base-change, geometry, and transition inputs retain their existing meanings.
