# Auxiliary characters to Harris general position: proof

Authors: Worker 84 (proof and original Markdown) and Worker 20 (adoption,
source verification and validation).

`Langlands.Global.auxiliaryGeneralPositionReduction.{u}` proves
`Langlands.Global.AuxiliaryGeneralPositionReductionStatement.{u}`.
The entire existing `AuxiliaryCharacterStatement.{u,u}` remains its
explicit premise. The proof derives the unchanged local
`HarrisGeneralPositionStatement.{u}` and does not prove auxiliary-character
existence.

## The actual field presentation

Fix `F`, its finite common-closure extension `E`, a supplied normalized
reciprocity family `e`, and a depth `s`. Let `M` be the actual normal
closure of `E/F`, `h` its inclusion, and `L := IntermediateField.restrict h`.
The proof installs the existing composite p-adic algebra structure of
`M`, its compatible scalar tower, its canonical norm and the Galois
instance of this normal closure.

Write `a` for the unit equivalence induced by `restrictAlgEquiv h`.
The helper `restrictAlgEquiv_continuous` proves continuity from the
`fieldData F E` topology on `E.field` to the subfield topology on `L`
induced by the canonical norm of `M.field`. It first treats the actual
inclusion as a p-adic algebra homomorphism. The published
`extension_isometry` gives continuity for the canonical norms, and
`topology_eq_canonicalNormTopology` changes the source topology to the
specified `fieldData` topology. Continuity into the subtype then gives
the required map to `L`. `Continuous.units_map` lifts it to a continuous
homomorphism `c` on unit groups with underlying map `a`.

The helper `restrictAlgEquiv_norm` reuses the published
`canonicalNorm_map` for that inclusion, so

\[
 \lVert a(x)\rVert_M=\lVert x\rVert_E.
\]

The equality uses the base-extending canonical norms throughout. No
equality with a residue-cardinality normalization is assumed.

## Preserving the auxiliary character

Apply the supplied auxiliary existence premise to `F`, `M`, `L` and
`s`. It yields a continuous finite-order character `χL`, a unit `xL`
with canonical norm distance from one less than `p^(-s)` and
`χL xL ≠ 1`, and the exact unit-norm stabilizer.

Define the field character `χ := χL.comp c` on `E.fieldˣ`. Its
continuity is supplied by the constructed map `c`. If `χL^n = 1`
with `n > 0`, pointwise evaluation of this same equality at `a x`
gives `χ^n = 1` with the same exponent. Moreover,

\[
 \chi\circ a^{-1}=\chi_L
\]

as algebraic monoid homomorphisms, by the inverse identities of `a`.
Thus the supplied exact unit-norm stabilizer has precisely the form
required by `unitNormWeilStabilizerTransport`. That theorem supplies
the exact Weil stabilizer of `weilCharacter F e E χ`.

Take `x := a.symm xL`. The norm helper applied to `x-1` transports
the same strict depth inequality from `M` to the canonical norm of `E`.
The character value is still `χL xL`, so it remains nontrivial.
The proof uses the algebraic inverse to choose this witness; continuity
of the inverse is not an additional premise.

## Conductors and the original local conjunction

For the fixed `F`, `E` and `e`, let `P χ` mean finite order together
with the exact Weil stabilizer. The preceding construction gives a
character satisfying this same `P` and nontriviality at every canonical
depth. The published `canonicalConductorDepth` equivalence applied to
`E.asPadicField`, its actual `fieldData` and this `P` therefore gives
characters satisfying `P` with arbitrarily large multiplicative
conductor. The private helper `exactStabilizer_of_auxiliary` returns
these identical witnesses in the order required by
`ExactStabilizerCharacterStatement`.

The final theorem takes `generalPositionOfExactStabilizer` for the
first conjunct of `HarrisGeneralPositionStatement`, the helper just
proved for the second, and applies that same published general-position
theorem to each character witness for the third. Finite order and the
conductor bound are kept unchanged. The cyclic tower and every Mackey
constituent are supplied by the published theorem, not introduced as
assumptions.

## Dependencies and source relationship

The proof imports its target, the separate unit-norm-to-Weil transport
proof, `GeneralPositionOfExactStabilizerProof`,
`CanonicalConductorDepthProof` and `Weil.Local.ExtensionResidue`.
The new argument transports characters between two actual presentations
and assembles these results; it introduces no parallel norm, conductor,
Weil or induction construction.

The source motivation is Harris 1998, Definition 4.5 and Lemma 4.7,
printed p.201 / one-based PDF p.25, and the proof printed pp.204–206 /
PDF pp.28–30, especially (4.12). Source
`harris-1998-local-langlands`, SHA256
`7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
This proof implements the derived reduction of the Library formulations.
It does not implement the character-existence construction on pp.205–206
or its characteristic-two repair, and has no global automorphic output.

The existing helpers `restrictAlgEquiv_continuous`, `restrictAlgEquiv_norm` are public so related modules can reuse their unchanged proofs.
