# Three results of JPSS 1983, Section 9, over one nonarchimedean local field

Module `Langlands.AllField.Representation.RankinSelberg.TemperedTypePremisesStatement`,
namespace `Langlands.AllField.RankinSelberg`. It defines three propositions about one
field `F` with instances `[TopologicalSpace F] [ValuativeRel F]
[IsNonarchimedeanLocalField F]`, and proves nothing. L-polynomials are the all-field
relation `IsPadicSymmetricLPolynomial F ψ ν` (larger rank first), with the residue
cardinality and normalized absolute value of `F`.

## `GenericStandardModuleStatement F` (universes `uF uV`)

For every nontrivial `ψ`, every `r` and every representation `π` of `GL_(r+1)(F)` on
`V : Type uV` with `IsGeneric ψ r π` (irreducible, admissible, with a nonzero
`ψ`-Whittaker functional), there is a datum `d : TemperedTypeDatum (r + 1)` (blocks in
universe `max uF uV`) whose standard module has the same `ψ`-Whittaker functions and the
same `ψ⁻¹`-Whittaker functions as `π`:

`whittakerSet ψ r d.standardModule = whittakerSet ψ r π` and
`inverseWhittakerSet ψ r d.standardModule = inverseWhittakerSet ψ r π`.

Source: JPSS 1983, (9.4), printed page 458, the paragraph of display (4): a generic
irreducible representation is the Langlands quotient of a standard module of tempered
blocks with decreasing exponents, and the two have the same Whittaker model. The tempered
blocks of the classification are generic; the datum records this as Whittaker type of
each block for every `ψ`.

## `TemperedPoleBoundStatement F` (universes `uF uV uW`)

For every `ψ`, self-dual Haar measure `ν`, irreducible tempered `τ` of `GL_(r+1)(F)` and
irreducible tempered `σ` of `GL_(t+1)(F)`, every certified L-polynomial `P` of `(τ, σ)`
has no zero `w` with `‖w‖ < 1`; with `L(s, τ × σ) = P(q^(-s))⁻¹`, `L(s, τ × σ)` has no
pole in `Re s > 0`.

Source: JPSS 1983, Proposition (8.4), printed pages 451–452.

## `InducedTailLFactorAt F` (universes `uF uV₁ uV₂ uW`)

The Library's p-adic `RankinSelberg.InducedTailLFactorStatement` with the field `F`: for
`π₁`, `π₂`, `σ` of Whittaker type, the certified polynomials `Pfull` of the normalized
two-block induction `Ind(π₁, π₂)` against `σ` and `Ptail` of `(π₂, σ)` exist and
`Ptail ∣ Pfull`. The block carriers are lifted to a common universe by `ULift`, as in
the p-adic statement.

Source: JPSS 1983, Lemma (9.3), printed pages 455–457.

## Use

`temperedTypeLPolynomial_product` (module `TemperedTypeLFactorProof`) takes tempered-type
data that are already given, and uses only the pole bound and the tail divisibility.
`Conductor.OrderedUnramifiedTemperedType.lPolynomial_principalSeries_eq_prod` (module
`Langlands.Representation.Conductor.OrderedUnramifiedLFactorProduct`) and
`Conductor.orderedUnramifiedCorankOneGenerationAt_of_premises` use all three: the
classification replaces `π` by the standard module of its datum, whose two Whittaker
sets are those of `π`. Over p-adic fields the three propositions are proved in
`Langlands.Representation.RankinSelberg.PadicTemperedTypePremises`.
