# Reduction of Henniart's cuspidal factor comparison

Author: Worker 5178.

This module proves the implication from the published
`Langlands.ClassField.Global.RelativeWeilGroup.AssociatedSupercuspidalInductionStatement`
and `Langlands.ClassField.Global.RelativeWeilGroup.AssociatedTemperedFactorStatement`
to the exact published
`Langlands.ClassField.Global.RelativeWeilGroup.AssociatedCuspidalFactorStatement`.
The two input propositions are explicit premises. The module is an
intermediate reduction and does not supply an unconditional proof of any
of those three propositions.

The source is Henniart (2000), §2.4, printed page 445 (PDF page 7),
specifically the deduction of Corollaire 2.4 from Théorème 2.4 and
Corollaire 2.3. It is registered as `henniart-2000-simple-proof`,
SHA-256 `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The reduction is an internal composition of published propositions and
proved Library theorems that implements this deduction.

`AssociatedCuspidalFactorReductionStatement` is a `Prop`-valued
definition of the implication, with all five universe levels independent.
The theorem
`associatedCuspidalFactor_of_supercuspidalInduction_of_tempered`
proves that implication with the two global inputs as named parameters.
`associatedCuspidalFactorReduction` packages the same proof at the
new proposition definition.

The implemented proof introduces every hypothesis and quantified object
of the unchanged cuspidal factor statement. Applying the supplied
supercuspidal induction theorem separately to the two actual cuspidal
realizations and their original spectral presentations produces two
ordered block shapes, unitarizable supercuspidal objects, and
equivalences of their entire normalized product inductions with the
original local actions.

For each action the proof applies the published theorem
`Langlands.Classification.isTempered_of_equiv_unitarizableSupercuspidalProduct`
from `Langlands.Representation.Classification.UnitarySupercuspidalInductionTempered`.
Its field, block carrier, and equivalent action carrier universes are
all specialized to `u`; thus its block carrier universe `max u u` is
exactly the universe required by the supplied induction statement.
The local ranks are `r + 1` and `t + 1`, so `Nat.succ_pos` supplies
positivity. Each temperedness proof installs precisely
`(padicField v).canonicalTopologicalData.topology`, as required by the
published tempered statement. No transport between merely
propositionally equal topology instances is needed.

The other proved Library input is
`Langlands.ClassField.Global.RelativeWeilGroup.localComponent_isUnitary`
from `Langlands.LocalFactor.UnitaryArithmeticPair`.
It restricts each supplied globally unitary Weil action along the
original local map `ι`. The proof then applies the supplied tempered
factor comparison at the original presentations, finite place, place
above it, reciprocity candidate, local map and additive character.
Its conclusion is definitionally the requested `IsPairFactorMatch`,
including the original L equality, the equality for every smooth dual
class, and the epsilon equality for every local-constant system.

The reduction neither chooses a spectral presentation nor imposes an
extra local hypothesis in its conclusion. It preserves the independent
universes for the field, Weil carrier, association witness presentation,
compared presentation and local-constant assignment. It makes no use of
continuity of the Weil actions or of a local Langlands correspondence.
The imported pairs are unchanged. An unconditional proof of Corollaire
2.4 still requires unconditional proofs of the two explicitly supplied
global statements.
