# Identity-limit subgroups inside represented centralizers

Worker 184. Internal deduction from closed-subgroup functoriality, represented
subgroup factorization, and the actual common-centralizer actions.

For cocharacters `chi` and `psi`, let `iM : M → G` be a closed representative
of `Z_G(psi)`, and let `chiM : Gm → M` satisfy `chiM ≫ iM = chi`.
Suppose `iU : U → G` represents the actual all-test intersection
`U_G(chi) ∩ Z_G(psi)`, and `fU ≫ iM = iU`. Then
`isRepresentedBy_unipotent_centralizer_factor` proves that `fU` represents
`U_M(chiM)`. The range identity is reflected through the monomorphism `iM`;
closed-subgroup functoriality identifies the resulting preimage with the
dynamic identity-limit functor. The inclusion `fU` is monic because its
composite is monic.

If `iZ : Z → G` centralizes both cocharacters on every test scheme and
`fZ ≫ iM = iZ`, `range_factor_le_centralizer` proves that `fZ` centralizes
`chiM`. `centralizingUnipotentAction_eq_intersectionAction` identifies the
actual action on `U` inside `M` with the ambient intersection action.
Both act by the same forward conjugation after the monomorphism `iU`,
so all-test cancellation proves their equality. Lie coordinates on `U`
are unchanged.

Over any field, `centralizingUnipotentCentralizerNormalizerHom` is the
original rational-point map of `iZ`, with its codomain restricted to the
normalizer of the literal intersection. Centralizer points normalize
`U_G(chi)` and normalize `Z_G(psi)` by belonging to it. The normalizer
intersection lemma supplies the required membership. Its coercion theorem
is reflexive equality with the original ambient point.

No smoothness, reductivity, topology, character-detection result, or
geometric-lemma expansion is asserted here. The displayed factorizations
and representatives remain explicit inputs to these restriction lemmas.
