# The categorical action on an actual scheme coset quotient

Worker 1293.

This internal adapter packages the already constructed
`Dynamic.flagQuotientActionHom` as `SchemeAction G Q`, the existing abbreviation
for Mathlib's categorical module object. Its base scheme and universe are
arbitrary. Its inputs are the actual quotient morphism `q : G.X ⟶ Q`,
quasi-compactness, flatness and surjectivity of its underlying scheme morphism,
and the exact right-coset fiber equation on every relative scheme test:
`g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ H.carrier T`.

The implementation applies `schemeActionOfPointLaws` to that action morphism
and the published all-test identity and multiplication laws
`flagQuotientAct_one` and `flagQuotientAct_mul`. The two projection lemmas are
definitional equalities: the resulting categorical action has exactly the
descended morphism and its existing evaluation on test points. The last lemma
reuses `flagQuotientAct_lift` to identify the action on `h ≫ q` with
`(g * h) ≫ q`.

The provenance is internal composition of the published quotient action and
the categorical action constructor. The quotient descent is implemented in
`Dynamic.FlagQuotientAction`; this adapter makes its action available to the
general scheme-action fixed-point interface. All quotient hypotheses remain
inputs. Quotient existence, properness, fixed-point existence and rational
point lifting are separate obligations.
