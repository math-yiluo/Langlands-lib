# Finite admissible irreducible tensor factorization for standard p-adic Levis

Author: Worker 161.

The closing theorem
`Langlands.CuspidalSupport.padicLeviAdmissibleFactorization.{uF,uW}` proves
exactly the published proposition
`Langlands.CuspidalSupport.PadicLeviAdmissibleFactorizationStatement.{uF,uW}`.
The statement pair and its imports are unchanged.

For every prime `p`, actual finite extension `F : PadicField.{uF} p`,
supplied `T : F.TopologicalData`, positive rank `n`, and ordered block shape
`B : GeneralLinear.BlockShape n`, the proof installs exactly `T.topology`.
Every irreducible admissible
`σ : SmoothRep.{0,uF,uW} ℂ (B.Levi F.Carrier)` then has a family of irreducible
admissible smooth representations of the block groups and a representation
equivalence from `σ.representation` to
`B.blockTensor (fun i => (A i).representation)`. The field universe `uF` and
carrier universe `uW` remain independent, and every factor carrier stays in
`Type uW`. The one-block case is included.

## Provenance and conventions

This is the finite iteration described in the target's
[derived-content discussion](LeviAdmissibleFactorizationStatement.md).
That discussion relates the two-factor existence statement to Flath,
*Decomposition of representations into tensor products* (1979), Theorem
1(1.2), printed pp.179–180, and the standard Levi product to
Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), sections 2.1–2.2, printed p.446. The finite-product assertion is
derived content, rather than a translation of a single printed theorem.

The Lean proof uses the proved Library theorem
`Langlands.admissibleProductFactorization`, imported from
`Langlands.Representation.Smooth.Factorization.TwoFactorExistenceProof`.
Its [proof description](../Smooth/Factorization/TwoFactorExistenceProof.md)
explains its internal multiplicity-space argument. This module does not
repeat that argument or assume its conclusion. Both its input and output
use the Library's all-open-subgroups admissibility convention:
smoothness and finite-dimensional fixed vectors for every open subgroup.

The finite group and tensor identifications are the published constructions
in `Langlands.Representation.Tensor.FiniteEquivalences`; their
[documentation](../Tensor/FiniteEquivalences.md) gives the coordinate maps,
tensor generator formulas, and intertwining proofs. The remaining helpers
in this module are private, derived steps in the closing proof.

## Topological preparation

`fieldTotallyDisconnected` works under the supplied topology. It installs
`T.valuativeRel`, `T.localField`, and `T.fieldT2`. Mathlib's
`ValuativeRel.nonarchimedeanRing` gives a nonarchimedean ring for the
valuation topology, and `Valuation.toTopologicalSpace_eq` identifies that
topology with the installed one. The Hausdorff nonarchimedean-ring instance
then supplies total disconnectedness. This argument reuses the generic
valuative-topology proof pattern in the Library module
`Langlands.Representation.RankinSelberg.PadicGammaFactor`; it does not
identify the supplied topology with a separately chosen canonical topology.

`generalLinearTotallyDisconnected` first obtains total disconnectedness of
matrices from the coordinatewise product instance. The continuous injective
map `Units.val` from matrix units to matrices pulls that property back to
`GeneralLinear m F.Carrier`. `leviTotallyDisconnected` applies the product
instance to the block groups. The induction also uses the ordinary finite
product instances for its tail groups.

The existing `Langlands.CuspidalSupport.length_pos_of_pos` from
[AssociationReduction](AssociationReduction.md) proves that the block count is
positive. If it were zero,
the index type would be empty, and `B.sum_eq` would force the total rank to
be zero, contradicting `0 < n`.

## Transport and two-factor existence

`tensorEquiv` constructs the tensor of two representation equivalences.
Its underlying linear equivalence is `TensorProduct.congr`; the tensor of
the two intertwining maps supplies action compatibility.

`equivOfPullback` reflects an equivalence through a group isomorphism. If
the pullbacks of `ρ` and `τ` along `e : H ≃* G` are equivalent, the same
linear equivalence intertwines `ρ` and `τ`: evaluate the pulled-back
intertwining identity at `e.symm g`.

`factorAlongProduct` takes a continuous group equivalence
`e : (G × H) ≃ₜ* K` and an irreducible admissible smooth representation of
`K`. It pulls that representation back along `e`. The published
`isAdmissible_comp_continuousMulEquiv` transports admissibility, including
smoothness, and `isIrreducible_comp_of_surjective` transports irreducibility
using the surjectivity of the group equivalence.

The helper applies `Langlands.admissibleProductFactorization` to this
pullback. Its two carriers are `ModuleCat.{uW} ℂ` objects. Each action is
bundled by `SmoothRep.of`, using the smoothness conjunct of its
admissibility proof. This retains the same carrier, action, irreducibility,
admissibility, and two-factor representation equivalence.

## Finite induction

`finiteFactorization` proves the internal result for a dependent family
`H : Fin (r + 1) → Type uF` of Hausdorff, locally compact, totally
disconnected topological groups. Its source is a smooth representation of
`∀ i, H i` with carrier in `Type uW`. The conclusion gives the factor
family, factorwise irreducibility and admissibility, and a representation
equivalence to `FiniteTensor.external` of their actions.

For `r = 0`, the group family has one member. Pull the source back along
`(FiniteTensor.evalOneContinuous H).symm`, transport the two hypotheses,
and bundle the resulting action as `A0`. Define the singleton factor family
by `Fin.cons A0` with its empty tail. The inverse of
`FiniteTensor.singletonEquiv` identifies this pulled-back source with the
pullback of its singleton external tensor. `equivOfPullback` then gives the
equivalence over the original product group. No two-factor result is used
in this base case.

For the successor step, use
`(FiniteTensor.headTailContinuous H).symm` to view the source as a
representation of `H 0 × (∀ j, H j.succ)`. Apply `factorAlongProduct` to
obtain the first factor `A0`, a tail representation `B`, and their
two-factor equivalence. Apply the induction hypothesis to `B`. Combine
the resulting tail family with `A0` by `Fin.cons`; `Fin.cases` combines
their irreducibility and admissibility proofs.

Pull the tail equivalence back along the second projection using the
published `equivComp`. Tensor it with the identity equivalence of the
first factor using `tensorEquiv`. Compose this with the two-factor
equivalence and the inverse of `FiniteTensor.headTailEquiv`. This produces
the required equivalence after pullback along the group splitting.
Finally, `equivOfPullback` returns it to the original group. The dependent
group and carrier families are retained throughout.

## Specialization to the actual Levi

The closing theorem installs `T.topology` and the published block-group
structures `T.generalLinearTopologicalGroup`, `T.generalLinearT2Space`,
and `T.generalLinearLocallyCompactSpace`, together with the total
disconnectedness proved above. Apply the finite induction at
`r = B.length.pred`. The equality `B.length.pred + 1 = B.length` follows
from `length_pos_of_pos B hn` and identifies its index family with the block
family. Take `H i = GeneralLinear (B.size i) F.Carrier`.

The resulting product group is definitionally `B.Levi F.Carrier`, and its
finite external tensor action is definitionally `B.blockTensor`. Thus the
inductive conclusion has exactly the target type.

There is no additional factorization, cuspidality, countability, local
finiteness, cardinal bound, or shrinking hypothesis. The conclusion asserts
neither uniqueness nor factorwise cuspidality nor realization in a smaller
carrier universe. The module introduces no axioms and uses no proof holes.
