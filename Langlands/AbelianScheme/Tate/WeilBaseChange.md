# Ground base change of integral and rational Weil pairings

Let `b : S' ⟶ S`, let `A` be an abelian scheme over `S`, and put
`A' = (baseChange b).obj A`. For a test scheme `T` over `S'`, write
`T₀ = (Over.map b).obj T`. The schemes `T.left` and `T₀.left` are the same.
This module lifts the published canonical dual torsion comparison and finite Weil
base-change theorem to the actual selected integral Tate limits and their rationalizations.

## Inputs and actual duals

The dual group schemes are the existing `dualCommGroupSchemeFromEvaluation` constructions
for `A` and `A'`. The inputs `hA`, `MA`, `evaluationA`, and their primed counterparts are
their existing dual-representability and inverse Poincaré evaluation data. The construction
retains the seven named tensor and Picard hypotheses `preservation`, `composition`,
`unitCoherence`, `associativity`, `comparison`, `symmetry`, and `stability`.
`universality : PicardZeroUniversalBaseChangeStatement` supplies the existing canonical
`dualGrpBaseChangeIso`. No alternative comparison is supplied as data, and no abelian
geometry on these dual group schemes is needed here.

The selection `P : ℕ → Prop` is arbitrary; its index consists of positive orders satisfying
`P`. Full modules use `P = fun _ => True`; away modules use
`P = fun n => Nat.Coprime n m` for a natural number `m`, with no primality assumption.

## Canonical dual comparisons

`dualLevelBaseChange_transition` proves that the published additive equivalence
`dualLevelBaseChange … T n` commutes with the multiplication-by-quotient transition for
`n ∣ k`. It unfolds that comparison as the torsion map of the inverse canonical dual
isomorphism followed by the pullback-adjunction comparison, and applies their existing
transition laws. Injectivity gives `dualLevelBaseChange_symm_transition`.

`dualIntegralBaseChange … T P` is the coordinatewise additive equivalence
from the selected integral Tate module of the dual of `A'` over `T` to the selected
integral Tate module of the dual of `A` over `T₀`. Its inverse uses the inverse level
comparison in every coordinate. The two evaluation lemmas specify these maps exactly.
The transition laws prove coherence; the level equivalences prove inverse and additive laws.

`continuous_dualIntegralBaseChange` and its inverse version use the product-subspace
inverse-limit topology and the discrete topology at each torsion level. Coordinatewise
`ZMod.map_smul` proves the full and away residue scalar laws.
`dualIntegralBaseChangeLinearEquiv` bundles the map as a continuous linear equivalence over
`Global.ProfiniteIntegerRing`; `dualAwayBaseChangeLinearEquiv` bundles its away version over
`Global.PrimeToProfiniteIntegerRing m`. No finiteness or compactness is asserted.

`dualRationalBaseChange` is the scalar extension of the additive equivalence over
`ℤ → ℚ`. Its pure-tensor formulas, in both directions, are
`q ⊗ y ↦ q ⊗ dualIntegralBaseChange(y)` and the corresponding inverse formula.
`dualIntegralBaseChange_restrictAway` and `dualRationalBaseChange_restrictAway` show that
restriction from full to away orders commutes with these comparisons. The integral identity
is coordinatewise definitional; the rational identity follows by tensor induction.

`dualFiniteAdeleBaseChange` bundles the rational comparison over the actual
`Global.FiniteAdeles ℚ` using the same scalar comparison `h` on both modules.
`dualPrimeToFiniteAdeleBaseChange` uses one coupled `hAway` (parameterized by `h`) on both
away modules. Both scalar laws follow from `TateScalarExtension.map_action` applied to
the corresponding integral residue-linear map. Rational topological continuity is not
asserted.

## Pairing equations

For the pairing results, `S` and `S'` have quasi-separated underlying spaces and
`compatibility : RelativeFiniteWeilTransitionStatement` is explicit. The pairing is the
published Poincaré-derived finite pairing with normalization `beta(y)(x)`, extended to
coherent families and then rationalized.

For `x` in the selected integral Tate module of `A'` over `T` and `y` in that of its dual,
`integralWeilValue_baseChange` states

`integralWeilValue(A', T, x, y) =
 integralWeilValue(A, T₀, integralBaseChange(x), dualIntegralBaseChange(y))`.

The proof applies subtype and function extensionality. At each selected order it is exactly
the published `finiteWeilLevelBilinearMap_baseChange` theorem. Since `T.left = T₀.left`,
both sides lie in the very same actual selected roots-of-unity limit
`TateTwist.Divisibility.Integral Γ(T.left, ⊤) P`.

`rationalWeilBilinearMap_baseChange` states the same equation for the rational pairing,
using `GroupScheme.Tate.rationalBaseChange` and `dualRationalBaseChange` on its inputs.
The values lie in `TateTwist.Divisibility.Rational Γ(T.left, ⊤) P`. The proof uses tensor
induction in both inputs. On pure tensors the factors multiply and the integral equation
identifies the remaining value; additivity handles sums. Specializing `P` gives full and
away equations. The adelic pairings have these same underlying values, and the bundled
comparisons use the same scalar witnesses. No roots, basis, or twist trivialization is chosen.

## Provenance and scope

This is derived infrastructure built from the Library modules
[FiniteWeilBaseChange](../../AlgebraicGeometry/Picard/FiniteWeilBaseChange.md),
[IntegralBaseChange](IntegralBaseChange.md), [RationalBaseChange](RationalBaseChange.md),
[WeilIntegral](WeilIntegral.md), and [WeilRational](WeilRational.md).
Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft built 2012-02-08,
Chapter VII, Proposition (7.4) and Theorem (7.5), printed pp.99–100 / PDF pp.103–104,
provide the base-change-compatible character construction behind the finite theorem.
Chapter XI, Definition (11.11), printed p.162 / PDF p.166, fixes the finite pairing's
normalization. The limit and rational comparison proofs here are the explicit Library
derivations described above, rather than new geometric existence results from that source.
Harris–Taylor (2001), printed p.18 / PDF p.26, defines the full and away Tate modules and
their rationalizations; Section III.1, printed p.91 / PDF p.99, motivates their pointed
PEL use.

This module proves comparison of the intrinsic pairing of `A` with that of its actual base
change. It does not yet construct base change of a dual-valued homomorphism or polarization,
transport compatible PEL frames, identify geometric monodromy actions, or prove unpointed
canonicity. Perfectness, nondegeneracy, rank, compact-open topology, and frame existence
are separate obligations. The named tensor, Picard base-change, and relative transition
propositions remain explicit dependencies.
