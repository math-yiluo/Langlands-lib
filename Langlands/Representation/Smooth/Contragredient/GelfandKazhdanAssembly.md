# Conditional assembly of Gelfand–Kazhdan from character inputs

This helper module serves
`Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof`, which
imports it. Its theorem
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

- `Langlands.characterSeparation`, at universes `.{uF,uV,uV}` (module
  `Langlands.Representation.Character.SeparationProof`), published in Library
  commit `123284c0f07314aa4544e028a94932bf9eb256af`.
- `Langlands.generalLinearConjugationDistributionTranspose`, at universe
  `.{uF}` (module `Langlands.HarmonicAnalysis.Distribution.TransposeInvariantProof`),
  published in Library commit `910a6df80701415e9aa68c646393c66ac9bc7512`.

No orbit-preservation argument is treated as distribution transpose
invariance, and no pullback representation is renamed as the smooth dual.

The conditional theorem compiles with no errors or warnings in the pinned Lean
environment, over Library commit
`910a6df80701415e9aa68c646393c66ac9bc7512`, in a local check
that also compiles `GelfandKazhdanProof`.
Declaration inspection reports independent universes `uF` and `uV` and only the
standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
