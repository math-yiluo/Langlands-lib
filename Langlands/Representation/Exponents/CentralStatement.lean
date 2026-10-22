import Langlands.Representation.Exponents.Central
import Langlands.Representation.Smooth.Definitions
import Langlands.Representation.Smooth.Contragredient.Definitions
import Langlands.Representation.Twist.Definitions
import Mathlib.Algebra.DirectSum.Module
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Topology.Algebra.Group.CompactOpen

/-!
# Central-character prerequisites for Jacquet exponents

These are proposition definitions, not proofs of the decomposition theorems.
The spaces are the published uniform generalized central-character spaces.
-/

noncomputable section

namespace Langlands

universe uR uG uV

/-- Every vector lies in a finite-dimensional subrepresentation of the
restriction to the actual center. This does not assert a decomposition. -/
def IsCenterFinite {R : Type uR} [Field R] {G : Type uG} [Group G]
    {V : Type uV} [AddCommGroup V] [Module R V]
    (ρ : Representation R G V) : Prop :=
  ∀ v : V, ∃ W : Subrepresentation (ρ.comp (Subgroup.center G).subtype),
    Module.Finite R W.toSubmodule ∧ v ∈ W

/-- Casselman's admissible center-finiteness and generalized-character
decomposition, including finite support and one uniform exponent.

The group assumptions spell out the source's locally compact Hausdorff group
with a compact-open subgroup neighborhood basis. Algebraic closedness is
required only by the decomposition and finite-support clauses. -/
def CentralCharacterDecompositionStatement : Prop :=
  ∀ (R : Type uR) [Field R] [CharZero R]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G],
    (∀ U : Set G, IsOpen U → (1 : G) ∈ U →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) →
    ∀ (V : Type uV) [AddCommGroup V] [Module R V]
      (ρ : Representation R G V),
      (IsAdmissible ρ → IsCenterFinite ρ) ∧
      (∀ [IsAlgClosed R], IsSmooth ρ → IsCenterFinite ρ →
        (iSupIndep (fun χ : {χ : Subgroup.center G →* Rˣ //
            IsOpen (χ.ker : Set (Subgroup.center G))} =>
          (generalizedCentralCharacterSpace ρ χ.val).toSubmodule) ∧
        (⨆ χ : {χ : Subgroup.center G →* Rˣ //
            IsOpen (χ.ker : Set (Subgroup.center G))},
          (generalizedCentralCharacterSpace ρ χ.val).toSubmodule) = ⊤) ∧
        (Module.Finite (MonoidAlgebra R G) ρ.asModule →
          {χ : Subgroup.center G →* Rˣ | IsCentralExponent ρ χ}.Finite ∧
          ∃ n : ℕ, 0 < n ∧
            ∀ χ : Subgroup.center G →* Rˣ,
              IsOpen (χ.ker : Set (Subgroup.center G)) →
              generalizedCentralCharacterSpace ρ χ = centralCharacterSpace ρ χ n))

/-- Scalar twisting multiplies the central character by the restriction of
the twisting character, without changing the underlying subspaces or powers.
The final clause retains the open-kernel requirement for central exponents. -/
def CentralCharacterTwistStatement : Prop :=
  ∀ (R : Type uR) [Field R] [CharZero R]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : Type uV) [AddCommGroup V] [Module R V]
    (ρ : Representation R G V) (η : G →* Rˣ)
    (χ : Subgroup.center G →* Rˣ),
    (∀ n : ℕ,
      (centralCharacterSpace (twist η ρ)
        ((η.comp (Subgroup.center G).subtype) * χ) n).toSubmodule =
        (centralCharacterSpace ρ χ n).toSubmodule) ∧
    (generalizedCentralCharacterSpace (twist η ρ)
      ((η.comp (Subgroup.center G).subtype) * χ)).toSubmodule =
      (generalizedCentralCharacterSpace ρ χ).toSubmodule ∧
    (IsOpen (η.ker : Set G) →
      (IsCentralExponent (twist η ρ) ((η.comp (Subgroup.center G).subtype) * χ) ↔
        IsCentralExponent ρ χ))

/-- On the actual smooth contragredient, a scalar central character becomes
its inverse. This is algebraic duality, with no complex conjugation. -/
def CentralCharacterContragredientStatement : Prop :=
  ∀ (R : Type uR) [Field R] [CharZero R]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : Type uV) [AddCommGroup V] [Module R V]
    (ρ : Representation R G V) (χ : Subgroup.center G →* Rˣ),
    IsSmooth ρ → IsOpen (χ.ker : Set (Subgroup.center G)) →
    centralCharacterSpace ρ χ 1 = ⊤ →
    centralCharacterSpace (smoothContragredient ρ) χ⁻¹ 1 = ⊤

/-- The coherent central-character family used before the split-center
Jacquet exponent criteria. No analytic exponent criterion is included. -/
def CentralExponentPrerequisitesStatement : Prop :=
  CentralCharacterDecompositionStatement.{uR, uG, uV} ∧
  CentralCharacterTwistStatement.{uR, uG, uV} ∧
  CentralCharacterContragredientStatement.{uR, uG, uV}

end Langlands
