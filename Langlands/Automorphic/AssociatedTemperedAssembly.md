# Global assembly of the associated tempered factor comparison

This internal helper assembles the exact conclusion
`Langlands.ClassFieldTheory.Global.RelativeWeilGroup.AssociatedTemperedFactorStatement`
from three explicitly supplied propositions: the associated gamma statement,
common-closure normalized reciprocity existence, and existence of a
local-constant system for each normalized reciprocity family. It does not
assert proofs of those three propositions.

The entry construction `localConstantSystemOfExistence` first chooses a
normalized reciprocity family from its supplied existential proof, then
chooses an actual assignment satisfying `NonabelianSystem.IsSystem`.
Its returned dependent pair retains that system proof. This is an internal
choice construction directly from the published definitions, without a
claim of canonical choice or uniqueness.

The theorem `associatedTemperedFactor_of_gamma_and_existence` introduces
every hypothesis and quantifier of the published tempered statement.
It specializes common-closure reciprocity existence to the canonical
topological data on the completion at the supplied finite place, and
uses `localConstantSystemOfExistence` to supply one local-constant system.
`certifiedAutomorphicPoleRegions_of_tempered` applies to the actual
`padicObject` representations of the two presented local components.
Their classes are definitionally the `padicClass` classes of the target.
The supplied associated gamma theorem gives the common gamma factors for
every local-constant system at these same original local objects.
`isPairFactorMatch_localPairClass_of_unitary_gamma` then supplies the
original L-factor equality, the L-factor equality for every smooth dual
class, and the epsilon equality for every local-constant system.

The theorem retains five independent universe levels: the global field,
the Weil carrier, the witness presentation for weak association, the
compared presentation, and the local-system assignment. Its conclusion is
the unchanged published statement, but the theorem itself is conditional.
In particular, it is not an exact-target proof of the corollary until all
three supplied propositions have unconditional Library proofs.

The imported pole-region helper is the module
`Langlands.Global.Factors.TemperedPoleRegions`, and the imported local assembly
and dual-transport helper is the module
`Langlands.Automorphic.AssociatedTemperedLocalProof`.
