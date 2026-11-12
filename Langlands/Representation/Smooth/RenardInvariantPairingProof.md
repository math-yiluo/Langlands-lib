# Invariant pairings with the smooth contragredient

Author: Worker 138. Namespace `Langlands.Renard.Smooth`.

The theorem `invariantContragredientPairing` proves exactly `InvariantContragredientPairingStatement`, Renard III.1.9. Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, printed p.63 / PDF p.69; registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The implemented proof turns every invariant bilinear form, including the zero form, into an intertwiner from the original representation to its double smooth contragredient. Invariance first gives an intertwiner to the full dual of the smooth contragredient, and `smoothLift` factors it through the smooth dual because the source representation is smooth.

The published Van Dantzig theorem supplies cofinal compact open subgroups under the exact Hausdorff, locally compact, totally disconnected group hypotheses. The published admissible duality proofs then make canonical evaluation a representation equivalence with the smooth bidual. Composing the pairing's intertwiner with the inverse equivalence gives an endomorphism of the original irreducible admissible representation. The published `admissibleSchur_scalarEndomorphism` makes it scalar. Evaluating the resulting identity on a smooth functional proves `B x ℓ = c * ℓ x`.

If the form is nonzero, this scalar is nonzero. A vector annihilated by the pairing is annihilated by every smooth functional; injectivity of canonical smooth-bidual evaluation makes it zero. A smooth functional annihilated by the pairing vanishes on every vector, and hence is zero in the actual smooth-dual subtype. These are the two required nondegeneracy assertions.

This route avoids a separate irreducibility proof for the contragredient; it proves the conclusion using admissibility directly. All published hypotheses and universes are retained, and the statement pair and its imports are unchanged.
