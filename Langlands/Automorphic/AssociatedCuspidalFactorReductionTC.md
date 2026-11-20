# Henniart's cuspidal factor reduction over totally complex fields

Worker 836, Task 7362.

`Langlands.ClassField.Global.RelativeWeilGroup.associatedCuspidalFactorReductionTC`
proves `AssociatedCuspidalFactorReductionTCStatement` from
`Langlands.Automorphic.AssociatedFactorTCReductionStatement` at the five
independent universe levels `u`, `uV`, `uP`, `uQ`, and `uE`. The target
assumes the totally complex forms of Théorème 2.4 and Corollaire 2.3 and
concludes the totally complex form of Corollaire 2.4. These three
propositions come from `Langlands.Automorphic.AssociatedFactorTCStatement`.

The proof follows Henniart's deduction in §2.4 and adapts the Library's
unrestricted argument in Worker 5178's
`associatedCuspidalFactor_of_supercuspidalInduction_of_tempered` from
`Langlands.Automorphic.AssociatedCuspidalFactorReduction`.
It introduces the totally complex instance on the given base field `F`
and works at its given extension `E` and finite place `v` throughout.
Two applications of Théorème 2.4, one to each original spectral
presentation, give ordered blocks of unitarizable supercuspidal
representations and equivalences of the local actions with their
normalized product inductions.

The proof installs the canonical topology of `padicField v` and applies
`Langlands.Classification.isTempered_of_equiv_unitarizableSupercuspidalProduct`
from `Langlands.Representation.Classification.UnitarySupercuspidalInductionTempered`.
This theorem transfers temperedness of each normalized induction to
the equivalent local action. Its field and representation universes
are instantiated at `u`, the common universe of these particular local
objects. `Nat.succ_pos` gives positivity of the two local ranks.

`localComponent_isUnitary` from `Langlands.LocalFactor.UnitaryArithmeticPair`
restricts each given global unitary Weil action along the original local
map `ι`. Corollaire 2.3 then applies to the same local data, using the
two temperedness and two unitarity witnesses. Its result is the required
`IsPairFactorMatch`, giving the pair's L comparison, the L comparison
for every smooth dual pair, and the epsilon comparison for every
supplied local-constant system.

The source is Guy Henniart, *Une preuve simple des conjectures de
Langlands pour GL(n) sur un corps p-adique*, Inventiones Mathematicae
139 (2000), 439–455, §2.4, printed page 445 (PDF page 7), registered as
`henniart-2000-simple-proof` with SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
