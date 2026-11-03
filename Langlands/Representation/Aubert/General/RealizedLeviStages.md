# Normalized induction in stages through a realized source Levi

Author: Worker 1212.

This internal adapter compares direct ambient normalized induction with the
actual source induction inside a represented dynamic Levi, followed by outer
normalized induction. It uses the exact simultaneous realization identities.
The source representation carrier universe is independent of the field universe.

The ambient group `G` is connected reductive over any nonarchimedean local
field `F`. The point topology on `G(F)` is `rationalPointTopology`, and its
local compactness and nonarchimedean group structure are retained inputs.
Let `j : L → G` be a closed representative of `Z(χ)`. Both schemes are assumed
affine and separated. For a source cocharacter `ν` and an ambient cocharacter
`ψ`, assume exactly

- `P(ψ) = extendFromCentralizer χ j hj P(ν)`;
- `Z(ψ) = Z(ν).map j`;
- `U(ψ) = extendFromCentralizer χ j hj U(ν)`.

Assume the actual ambient subgroups `U(ψ)(F)`, `U(χ)(F)` and `Z(χ)(F)` are
closed. These are explicit hypotheses of this comparison. Local compactness
of the outer Levi follows from its closedness. Local compactness and the
nonarchimedean group structure of `L(F)`, with its pinned point topology,
follow through the canonical represented-point homeomorphism `e : L(F) ≃ₜ* Z(χ)(F)`.
No reductivity hypothesis on `L` is used.

`ambientInductionIso` derives the parabolic, centralizer and reverse-radical
inclusions from the realization identities using `Dynamic.RealizedLeviNesting`.
Its all-test nested decomposition gives the literal radical product at the
identity test. The literal inner semidirect decomposition is the one already
constructed by `RealizedLeviTransport.insideDecomposition`.

The existing local-field and affine-coordinate results give second countability
of `G(F)`. `continuous_dynamic_projection` supplies continuity of the actual
outer projection. Published dynamic unipotent compact containment supplies
compact-subgroup containment for both radicals, hence their unimodular
conjugation characters. The published `NestedParabolic.halfCharacterProduct`
then derives the full-parabolic half-character product from the actual radical
product. Applying `NestedInduction.iso` gives the ambient stages comparison.
This application needs the three proved inclusions and the radical product;
no common-torus compatibility input occurs.

`innerSourceIso` identifies the literal inner stage with actual normalized
induction in `L(F)`, transported back to `Z(χ)(F)`. It uses
`RealizedLeviTransport.inductionIso` and cancels pullback along `e` and
`e.symm` with the identity linear map. Coefficients are first pulled from
`Z(ψ)(F)` to its literal copy inside `Z(χ)(F)` and then along the restricted
source-centralizer homeomorphism to `Z(ν)(F)`. Source radical closedness is
the preimage result already proved in `RealizedLeviTransport`.

`inductionInStagesIso` composes these comparisons and applies the outer
normalized induction functor to the inner isomorphism. Its component sends a
direct ambient induced function `f` to the function whose value at `g ∈ G(F)`
is the source induced function

`l ↦ c(e(l))⁻¹ • f(e(l) g)`,

where `c` is the positive half Haar-conjugation character of the outer radical
on `Z(χ)(F)`, and `e(l)` is read in `G(F)` in the product. The evaluation theorem
states this formula on the actual smooth induced carriers.

All functors use the full-parabolic Haar normalization already defined in the
Library. No replacement character or assumed normalization identity is used.
The input carrier is in universe `uV`, independent of the field universe `u`;
both direct and iterated outputs are in `max u uV`.

The provenance is an internal composition of published exact-extension,
topology, compact-containment, Haar-product and actual-function stages results,
together with the earlier source-realization comparison. This adapter proves
neither finite-length existence nor cuspidal embedding nor connected
reductivity of the source representative. Actual standard-parabolic
specialization and the representation-theoretic VI.5.4 theorem remain separate
obligations for the exact VI.6.2 proof.
