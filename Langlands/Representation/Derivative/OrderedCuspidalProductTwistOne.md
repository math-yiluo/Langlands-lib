# A cuspidal datum is not fixed by the twist by `ν`

Author: Worker 1168 (proof). Worker 818, first executor of proof task
`451717b1-3d17-41d3-81e7-29b78f0b6112`, moved it into this module and fixed its
interface.

This is an internal helper of the proof of Bernstein–Zelevinsky 1977, Theorem
4.11 (sufficient direction), in module
`Langlands.Representation.Derivative.OrderedCuspidalProductNondegeneracyProof`.
It is not a translation of a separate literature statement. Its only consumer is
`Langlands.Derivative.OrderedCuspidalProductHeadShift.headShift_false`, the
head-shift step of Case 2 of BZ77 §4.15 (printed pp. 458–459). Lemma 4.7(b) gives
a block `ρ_j = ν ρ_{i₀}` there, and this module excludes `j = i0`. Here
`ν = |det|^1` is the Library's residue-normalized real power twist.

The Library already proves the same fact, as
`Langlands.Classification.RepeatedCuspidalSupport.twist_one_ne_self`, by way of
`Langlands.Classification.cuspidalIntegralTwistFreeness`
(`Classification.CuspidalIntegralTwistFreenessProof`). The earliest published
artifact of that proof module, `a7545313`, belongs to task
`67279e36-f3c2-42e3-9302-11729784042e`, which the contract of task `451717b1`
excludes. This module gives an independent proof and imports neither module.

## Exact scope

The module states and proves two theorems in namespace
`Langlands.Derivative.OrderedCuspidalProductTwistOne`. Fix a prime `p`,
`F : PadicField.{uF} p` and topological data `T`, with `letI := T.topology`.

`exponent_eq_zero` (line 31) takes `r : ℕ` with `0 < r`, a smooth representation
`A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)` that is admissible
(`A.IsAdmissible`) and irreducible (`A.IsIrreducible`), a real number `s`, and an
equivalence of representations
`e : A.representation.Equiv (twist (T.determinantPowerCharacter r s) A.representation)`.
Its conclusion is `s = 0`. Here `T.determinantPowerCharacter r s` is the Library's
character `g ↦ |det g|^s` of `GL_r(F)`, for the residue-normalized absolute value.

`twist_one_ne_self` (line 81) states `ρ.twist 1 ≠ ρ` for every
`ρ : T.CuspidalDatum.{uV, uF}`. `CuspidalDatum.twist 1` keeps the rank and
applies `T.supercuspidalClassRealPowerTwist ρ.rank 1` to the supercuspidal class.

## Implemented proof

`exponent_eq_zero`. Irreducibility makes `A` nontrivial, so there is a vector
`v ≠ 0`, and `e v ≠ 0`. The published admissible Schur theorem
`Langlands.admissibleSchur_centralCharacter` (module `Smooth.Schur.Proof`) gives a
character `ω` of the centre with `A(z) w = ω(z) • w` for all central `z` and all
vectors `w`. Take `z = scalarToCenter ϖ`, the scalar matrix of the uniformizer
unit `LocalFactor.PadicAbelian.uniformizerUnit T`. Evaluating the intertwining
identity of `e` at `z` and `v` and applying the central character on both sides
gives `ω(z) • e v = χ(z) ω(z) • e v`, where `χ = T.determinantPowerCharacter r s`.
Cancelling the nonzero vector `e v` and the unit `ω(z)` gives `χ(z) = 1`.
The Library lemmas `coe_realPowerCharacter`, `T.determinantNorm_scalar`,
`T.normalizedAbsUnits_coe`, `uniformizerUnit_coe` and `T.normalizedAbs_uniformizer`
rewrite this as `((q⁻¹)^r)^s = 1`, where `q = T.residueCardinality`. Since
`q > 1` (`T.residueCardinality_gt_one`), injectivity of `t ↦ q^t` turns
`q^{-r s} = q^0` into `-r s = 0`. Since `r ≠ 0`, it follows that `s = 0`.

`twist_one_ne_self`. Write `ρ = ⟨r, hr, c⟩` and suppose `ρ.twist 1 = ρ`.
Comparing the class fields gives `T.supercuspidalClassRealPowerTwist r 1 c = c`.
Induction on the quotient class `c` gives a representative `A`. The twisted class
is the class of `SupercuspidalRep.twist (T.determinantPowerCharacter r 1) … A`, so
`SupercuspidalRep.isoClass_eq_iff` gives an isomorphism between that twist and `A`.
Its inverse, mapped to `SmoothRep` and converted by `SmoothRep.equivOfIso`, is an
equivalence from `A.obj` to its twist by `|det|^1`. `A.obj` is irreducible
(`A.property.1`) and admissible (`A.property.2.1`), so `exponent_eq_zero` gives
`(1 : ℝ) = 0`, a contradiction.

## Normalizations and universes

`ν` is the twist by `T.determinantPowerCharacter r 1`, the Library's
residue-normalized `|det|`, which is also used by `CuspidalDatum.twist` and hence
by Lemma 4.7(b) as published. The universes `uF` (field) and `uV` (carriers) are
independent. No other normalization enters.

## Imports and provenance

Direct imports:

- `Langlands.Representation.Classification.SupercuspidalSupport` (cuspidal data,
  supercuspidal classes and their twists);
- `Langlands.Representation.Smooth.Schur.Proof` (admissible Schur lemma with
  central character, proof `b97b88e5`, task `7418b301`);
- `Langlands.LocalField.Uniformizer` (the uniformizer as a field unit: an
  integrator extraction from `LocalFactor.Abelian.Padic`, constructions of
  Worker 33 and Worker 20);
- `Langlands.LocalField.Normalization.Proof` (`normalizedAbs_uniformizer`,
  `residueCardinality_gt_one`);
- `Langlands.Group.GL.NormalizedCharacter` (`determinantNorm_scalar`,
  `normalizedAbsUnits_coe`);
- `Langlands.Representation.Twist.RealPower` (`coe_realPowerCharacter`).

The recursive project import closure of this module has 61 `Langlands` modules.
All except two lie in the import closure of the published Lemma 4.7(b) proof
module `Langlands.Representation.Classification.CuspidalProductMirabolicSupportShiftProof`,
which the head-shift step already imports: this module itself and
`Langlands.LocalField.Uniformizer`. Their audit against the exclusions of task
`451717b1` is part of that task's final proof Markdown.

The proof was written by Worker 1168 as a scratch module and sent to Worker 818
in peer message `84dff951a4b050be9a3da1a574b76b42`. Worker 818 changed only the
module name, the namespace placement of `open`, and the docstrings, and dropped
the scratch bridge declarations that the consumer does not use.
