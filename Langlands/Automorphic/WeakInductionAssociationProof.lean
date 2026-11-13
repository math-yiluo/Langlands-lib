import Langlands.Automorphic.WeakInductionAssociationReduction
import Langlands.ClassFieldTheory.Local.WeilReciprocityExistenceProof
import Langlands.ClassField.Global.LocalRelativeWeilMapExistenceProof
import Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionProof

/-!
# Weak automorphic induction gives weak association with the induced Weil representation

The published reduction `weakInductionAssociation_reduction`, applied to the three proved
local inputs: existence and uniqueness of geometric local Weil reciprocity, existence of
local-to-relative Weil maps, and the local restriction formula for induced relative Weil
representations.
-/

noncomputable section

set_option autoImplicit false

universe u uV uP

namespace Langlands.ClassField.Global.RelativeWeilGroup

/-- **Weak induction association** (Henniart (2000), §3.4, with Harris (1998),
Definition 1.3(b)). For every arithmetic class family with the restriction compatibility,
every tower `F ⊆ E' ⊆ L` of number fields with `L / F` Galois, every cuspidal class `π` of
`GL_r(𝔸_F)` and every Hecke character `ξ` of `E'`, if `π` is a weak automorphic induction
of `ξ`, then `π` is weakly associated with `Ind_{W_{L/E'}}^{W_{L/F}} (ξ ∘ τ_{E'})`. -/
theorem weakInductionAssociation : WeakInductionAssociationStatement.{u, uV, uP} :=
  weakInductionAssociation_reduction
    LocalClassField.geometricWeilReciprocityExistenceUniqueness.{u}
    localRelativeWeilMapExistence.{u}
    localInducedRestriction.{uV, u}

end Langlands.ClassField.Global.RelativeWeilGroup
