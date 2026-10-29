import Langlands.Representation.Smooth.Definitions
import Langlands.Representation.Exponents.DualJacquet

/-!
# Local conversion from central transpose eigenfunctionals to primal vectors

A derived algebraic interface for a general admissible representation.
This module states a proposition and supplies no proof.
-/

namespace Langlands

universe uG uA uV

/-- An ordinary eigencharacter of the full transpose dual of a central action
on an admissible representation occurs as a uniform-power generalized
eigencharacter of the original central action. -/
def AdmissibleCentralDualToPrimalStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    (∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G,
      IsCompact (K : Set G) ∧ K ≤ H) →
    ∀ (A : Type uA) [CommGroup A]
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ G V) (c : A →* Subgroup.center G),
      IsAdmissible ρ →
      ∀ χ : A →* ℂˣ,
        commutativeCharacterSpace
          (commutativeTranspose (ρ.comp ((Subgroup.center G).subtype.comp c)))
          χ 1 ≠ ⊥ →
        IsGeneralizedEigencharacter
          (ρ.comp ((Subgroup.center G).subtype.comp c)) χ

end Langlands
