import Langlands.Representation.Smooth.FiniteLengthGrothendieck
import Langlands.Representation.Smooth.Definitions
import Langlands.Representation.Exponents.Jacquet

/-!
# Central generalized spectrum and exact finite-length classes

This internal algebraic interface states that equal exact Grothendieck classes
of admissible finite-length smooth representations have the same generalized
eigencharacters after restriction along a continuous central homomorphism.
The module defines a proposition and supplies no proof.
-/

namespace Langlands

universe uG uA uV

/-- Equality of actual exact finite-length classes preserves the generalized
eigencharacters of a supplied continuous central action. -/
def ExactClassCentralSpectrumStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    (∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G,
      IsCompact (K : Set G) ∧ K ≤ H) →
    ∀ (A : Type uA) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
      (c : A →* Subgroup.center G),
      Continuous c →
      ∀ (R S : SmoothRep.{0, uG, uV} ℂ G)
        (hR : R.HasFiniteLength) (hS : S.HasFiniteLength),
        IsAdmissible R.representation →
        IsAdmissible S.representation →
        SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation R hR =
          SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation S hS →
        ∀ χ : A →* ℂˣ,
          IsGeneralizedEigencharacter
            (R.representation.comp ((Subgroup.center G).subtype.comp c)) χ ↔
          IsGeneralizedEigencharacter
            (S.representation.comp ((Subgroup.center G).subtype.comp c)) χ

end Langlands
