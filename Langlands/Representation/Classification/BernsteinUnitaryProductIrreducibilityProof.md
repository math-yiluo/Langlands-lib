# Irreducibility and unitarizability of finite normalized products

Authors: Worker 103 and Worker 105.

`Langlands.Classification.bernsteinUnitaryProductIrreducibility` proves the
exact published proposition
`Langlands.Classification.BernsteinUnitaryProductIrreducibility.{uF, uV} F T`.
Its parameters are arbitrary `{p : ℕ} [Fact p.Prime]`,
`F : PadicField.{uF} p` and `T : F.TopologicalData`, with independent field
and representation universes. It has no additional hypothesis.

For every `n`, every actual block shape `B : GeneralLinear.BlockShape n`,
and every family of irreducible unitarizable smooth blocks `σ i` on
`GL_(B.size i)(F)` with carrier in `Type (max uF uV)`, the theorem gives
irreducibility and unitarizability of
`(T.normalizedProductInductionFunctor B).obj σ`. It uses the supplied
topology `T.topology` and the Library's actual normalized induction functor.
The empty product at rank zero is included.

The proof composes the rank induction in `BernsteinUnitaryRankInduction`
with four separately proved Library inputs. The helper
`bernsteinUnitaryInductionInputs` supplies their conjunction:

- `bernsteinShiftedHighestDerivativeUnitarity` proves irreducibility and
  unitarizability of every shifted highest derivative of an irreducible
  unitarizable factor.
- `bernsteinUnitaryLowerDerivativePositivity` proves positivity of the
  shifted derivatives below that highest order.
- `bernsteinUnitaryTopDerivativeProductPositivity` transfers the factor
  bounds and unitarity of the shifted highest derivatives to the required
  positivity bounds for their product.
- `bernsteinUnitaryFiniteLengthIrreducibilityCriterion` proves
  irreducibility of a finite-length unitarizable representation from those
  bounds and its irreducible unitarizable shifted highest derivative.

The final theorem applies
`bernsteinUnitaryProductIrreducibility_of_inductionInputs` to this proved
conjunction. Thus every analytic premise of that reduction is discharged.
The fixed statement and all of its imports are unchanged.

The reduction inducts strongly on the sum of two factor ranks. Rank-zero
irreducible factors are isomorphic to the actual binary unit. For positive
ranks, choose a nontrivial unitary additive character and positive highest
derivative orders for the factors. Their shifted highest derivatives are
irreducible and unitarizable by the first input, and their ranks have a
strictly smaller sum. The induction hypothesis therefore applies to their
binary product. The actual shifted highest-product isomorphism identifies
it, after rank transport, with the shifted derivative of the original
product at the sum of the two orders. Nonvanishing there and vanishing
above that sum give highest-order data for the original product. The
positivity inputs and finite-length criterion then give irreducibility.
Unitarity is supplied by normalized induction and the unit equivalences.
Finally, the published binary-to-block reduction uses the actual
head-and-tail induction isomorphism to cover every finite block family,
including the empty product.

This is the structural rank-induction route of J. N. Bernstein,
*P-invariant distributions on GL(N) and the classification of unitary
representations of GL(N) (non-archimedean case)*, LNM 1041 (1984),
§8.2, Corollary 8.2(a), printed p.89 (registered source
`bernstein-1984-p-invariant`). The resulting binary assertion is also
M. Tadić, *Classification of unitary representations in irreducible
representations of general linear group (non-archimedean case)*,
Ann. Sci. ENS 19 (1986), Theorem 2.5(i), printed p.346
(`tadic-1986-unitary`). The finite-family formulation follows through the
explicit block reduction described above. This module introduces no
further analytic result: it composes the separately published proofs and
the structural reduction.
