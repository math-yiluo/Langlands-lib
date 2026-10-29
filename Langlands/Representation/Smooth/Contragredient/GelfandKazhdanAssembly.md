# Conditional assembly of Gelfand–Kazhdan from character inputs

Author: Worker 51. This helper module is submitted together with
`Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof` (Worker 249
and Worker 51) for task `2206daa6-e219-4ed6-9ad1-4f4d47efed93`. Its theorem
`Langlands.gelfandKazhdanContragredient_of_character_inputs` is conditional, so
it does not by itself prove the unconditional target. The final theorem
`Langlands.gelfandKazhdanContragredient` in that module applies it to the two
published inputs.

The theorem explicitly assumes character separation and transpose invariance of
conjugation-invariant distributions. Character transport and normalized Haar
symmetries use the published theorems `Langlands.characterTransport` and
`Langlands.RankinSelberg.generalLinearHaarSymmetries`. Its conclusion is the unchanged
`GelfandKazhdanContragredientStatement`, with independent field and carrier
universes and every positive rank, including rank one.

The implementation installs the canonical nonarchimedean structure of the
actual general linear group, which supplies total disconnectedness, and its
canonical local compactness. It then chooses the existing normalized Haar measure and the actual
inverse-transpose continuous group automorphism. Character transport gives
admissibility and the two character formulas for the actual pullback and actual
smooth dual. Compact-open cofinality, smooth separation, and admissible bidual
reflexivity supply irreducibility of the smooth dual through the published
conditional irreducibility transfer. Surjective group transport gives
irreducibility of the actual pullback.

The original character is conjugation invariant because the chosen Haar measure
is preserved by inner automorphisms. The assumed distribution theorem makes
that character transpose invariant. Applied to the inverted test function, this
identifies the inverse-transpose pullback formula with the smooth-dual formula.
Character separation then produces the actual equivariant linear equivalence
from the original carrier to its smooth dual, in precisely the target direction.

This is an internal assembly of the character argument in Bernstein–Zelevinsky
(1976), Theorem 7.3, printed/PDF page 57. It uses ordinary inverse transpose
directly, so no signed-Weyl conversion is needed within this implementation.
The theorem keeps both inputs as hypotheses and proves neither of them. The
final module `GelfandKazhdanProof` supplies them with two published theorems:

- `Langlands.characterSeparation`, at universes `.{uF,uV,uV}`: candidate
  `a68eef2b-3e88-46b5-ba92-6d95da98f52e`, version 1 (Worker 203), accepted in
  review `1cd9f168-e3ac-49b5-8962-3ef264ad30ac` and published in Library commit
  `123284c0f07314aa4544e028a94932bf9eb256af`.
- `Langlands.generalLinearConjugationDistributionTranspose`, at universe
  `.{uF}`: candidate `a273f153-573e-4de5-a169-47a467c37f10`, version 1
  (Worker 33), accepted in review `be0b16e9-53cb-4570-8d5d-3a401fa89e13` and
  published in Library commit `910a6df80701415e9aa68c646393c66ac9bc7512`.

No orbit-preservation argument is treated as distribution transpose
invariance, and no pullback representation is renamed as the smooth dual.

The conditional theorem compiles with no errors or warnings in the pinned Lean
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, over Library commit
`910a6df80701415e9aa68c646393c66ac9bc7512`, in the local check
`cc75de6f-a869-4ef9-b5df-88fd72391cab` that also compiles `GelfandKazhdanProof`.
Declaration inspection reports independent universes `uF` and `uV` and only the
standard axioms `propext`, `Classical.choice`, and `Quot.sound`. The machine
validation, independent acceptance and publication of this helper are all
pending. Each of them is carried out together with `GelfandKazhdanProof`, whose
Markdown records their status.
