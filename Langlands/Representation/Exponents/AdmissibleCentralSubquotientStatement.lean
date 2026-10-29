import Langlands.Representation.Exponents.DualJacquet

/-!
# Detecting a central scalar subquotient in the full dual

A local finite-fixed-space interface for a general admissible complex
representation. This is an internal derived statement, with no proof.
-/

namespace Langlands

universe uG uA uV uW

/-- On a group with cofinal compact open subgroups, a scalar character of an
actual nonzero subquotient of an admissible representation, through a
continuous central map, has open kernel and occurs as an ordinary
eigencharacter of the full transpose dual of the same restricted central
action. No global spectral finiteness is asserted. -/
def AdmissibleCentralSubquotientStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    (∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G,
      IsCompact (K : Set G) ∧ K ≤ H) →
    ∀ (A : Type uA) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ G V) (c : A →* Subgroup.center G),
      Continuous c → IsAdmissible ρ →
      ∀ (χ : A →* ℂˣ) (U : Subrepresentation ρ)
        (W : Type uW) [AddCommGroup W] [Module ℂ W] [Nontrivial W]
        (q : U.toSubmodule →ₗ[ℂ] W),
        Function.Surjective q →
        (∀ (a : A) (u : U.toSubmodule),
          q (U.toRepresentation (c a : G) u) = (χ a : ℂ) • q u) →
        IsOpen (χ.ker : Set A) ∧
          commutativeCharacterSpace
            (commutativeTranspose (ρ.comp ((Subgroup.center G).subtype.comp c)))
            χ 1 ≠ ⊥

end Langlands
