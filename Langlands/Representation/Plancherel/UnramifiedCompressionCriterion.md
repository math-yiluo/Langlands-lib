# Normalized coefficient Jacquet finiteness and actual compact compression

Worker 1755, with interface and reuse guidance from Worker 1751. Internal
normalization comparison for the actual unramified coefficient models used
in Renard 2026 VI.9.2, printed p.199 / PDF p.205.
Registered source `renard-2026-representations-groupes-reductifs-padiques`,
SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This is derived implementation content connecting the existing normalized
model to the unnormalized quotient used by compact compression.

On the compact intersection of a compact open subgroup with a closed Levi,
the actual inverse-half normalization character is trivial. Its constant
coefficient extension is therefore trivial as well. The fixed-vector
submodule of the actual normalized coefficient Jacquet action agrees
with that of the character-one unnormalized action. The existing trivial
character quotient equivalence then gives an actual coefficient-linear
equivalence with the native unnormalized Jacquet fixed space.

Precisely, the coefficient ring is the existing
`B = unramifiedRegularFunctions ν` for any norm family `ν`.
The group is locally compact and nonarchimedean. The input
`ρ : Representation B G V` is an actual coefficient representation,
and the subgroup conditions are closedness of `N` and `M` and
`M ≤ normalizer N`.
`normalizedJacquetFixedEquiv` compares
`fixedVectors (jacquetRepresentation ν ρ N M hN hMN) (K ∩ M)`
with `fixedVectors (Jacquet.action ρ N M hMN) (K ∩ M)`;
the Lean subgroup is `K.toSubgroup.comap M.subtype`.

Its proof reuses `NormalizedJacquetBridge.character_trivial`, applied
to the compact intersection and the actual inverse-half character,
and `constantCharacter_ker` for its coefficient extension.
The published twist fixed-space equality removes the normalization
on that subgroup, and `Localization.trivialEquiv` identifies the two
actual character-one and unnormalized relation quotients.
The equivalence is `B`-linear. There is no dimension, Noetherianity,
smoothness or finite-generation premise for this comparison.

Finiteness of the normalized fixed space thus supplies precisely the target
finiteness input to the native coefficient compression criterion. The final
corollary explicitly retains Noetherianity of the regular coefficient algebra
and finite generation of both source and normalized target fixed spaces.
It proves eventual stability of actual complex compression after scalar
restriction, not an unconditional family finiteness or uniform exponent.

The corollary is
`compressedAction_eventuallyStable_of_normalized_finite`. In addition to
the comparison's geometric hypotheses it assumes a compatible complex
module structure on `V` with `IsScalarTower ℂ B V`, smoothness of `ρ`,
the actual Iwahori contraction conditions for the chosen `g`, and
Levi centrality of `g`. The fixed-space equivalence transfers the normalized
target finiteness to native unnormalized target finiteness; the earlier
`CoefficientRestriction.compressedAction_eventuallyStable_of_native_finite`
then supplies the positive stable power with both kernel and range
square equalities.

This criterion applies in particular to the existing
`universalInducedRepresentation` and rational normalized induced model
once their coefficient finiteness inputs have been proved. It does not
prove those inputs. In the source's universal supercuspidal case, native
Jacquet fixed-space finiteness is obtained from the coefficient geometric
lemma, which remains a separate representation-theoretic obligation.
The arbitrary norm-family and topological-group setting of this adapter is
derived scope. The norm-family, group and carrier universes are independent.
