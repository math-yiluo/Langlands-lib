# Proof of duality of contragredient twist parameters

The theorem `supercuspidalParameterDuality` proves the existing proposition
`SupercuspidalParameterDualityStatement` with independent field and carrier
universes. This is an internal consequence of the Library's smooth duality and
determinant-character results.

First, `IsContragredientTwistParameter.congr_equiv` transports the twist
equivalence using the two given representation equivalences and contravariance
of the smooth dual. The complex parameter and its exponent are preserved.

Next, `IsContragredientTwistParameter.dual` takes the exponent `u` and character
`χ` witnessing an original parameter. The pointwise character identity
identifies `χ ∘ det` with the canonical complex determinant power at `-u`,
whose kernel is open. Dualizing the given equivalence and applying
`smoothContragredientTwistEquiv` yields an equivalence from the inverse-character
twist of the first smooth dual to the double smooth dual of the second
representation. The new witnesses are `-u` and `χ⁻¹`. The complex power
negation law identifies the new parameter with the inverse of the old one.
This implication needs no admissibility.

For the reverse implication of the main theorem, the p-adic general linear
group has cofinally many compact open subgroups. The published injectivity and
surjectivity results for `smoothBidual` therefore make the two canonical
evaluation maps into representation equivalences, using the supplied
admissibility hypotheses. Apply the forward implication to the smooth dual
pair, then transport both double duals back to the originals. Double inversion
of the parameter finishes the proof.

No L-factor formula, parameter norm estimate or representation-theoretic
existence theorem is asserted here.

For the functional equation's actual inverse-transpose representations,
the existing `inverseTransposeSmoothDualEquiv` from `SmoothDualPairFactors`
packages the published
Gelfand--Kazhdan theorem as a representation equivalence in the canonical
topology. This helper assumes irreducibility and admissibility.
`IsContragredientTwistParameter.inverseTranspose_iff` then transports both
representations through these equivalences and applies the proved duality
statement. Thus inverse transpose also inverts the original pair's parameters,
with the extra irreducibility hypotheses visible in that corollary.

The canonical local topology instances have module-specific names, so the
proof can be imported with the existing tempered pair-factor modules.
