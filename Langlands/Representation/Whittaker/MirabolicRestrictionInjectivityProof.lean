import Langlands.Representation.Whittaker.MirabolicCoefficientKernel
import Langlands.Representation.Whittaker.LocalFieldMultiplicityOneProof
import Langlands.Representation.Whittaker.LocalFieldMirabolicNondegeneracyProof

/-!
# Injectivity of restriction to the mirabolic subgroup: proof

Jacquet and Shalika 1981, Section (1.1), injective half, in the formulation
`Langlands.Whittaker.MirabolicRestrictionInjectivityStatement`, over every nonarchimedean local
field of any characteristic. It applies the published reduction
`mirabolicRestrictionInjectivity_of_multiplicityOne_of_nondegeneracy` to the published proofs of
all-field Whittaker multiplicity one and of Bernstein–Zelevinsky Theorem 4.9.
-/

namespace Langlands.Whittaker

universe uF uV

/-- **Jacquet–Shalika, Section (1.1), injective half.** Over every nonarchimedean local field,
for an irreducible admissible generic representation `π` of `GL_(n+1)(F)` and a nonzero standard
Whittaker functional `ℓ`, the map `v ↦ (p ↦ ℓ(π(p) v))` to functions on the mirabolic subgroup
is injective. -/
theorem mirabolicRestrictionInjectivity :
    MirabolicRestrictionInjectivityStatement.{uF, uV} :=
  mirabolicRestrictionInjectivity_of_multiplicityOne_of_nondegeneracy
    localFieldMultiplicityOne localFieldMirabolicNondegeneracy

end Langlands.Whittaker
