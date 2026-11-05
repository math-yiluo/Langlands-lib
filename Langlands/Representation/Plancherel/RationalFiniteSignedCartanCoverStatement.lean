import Langlands.Representation.Aubert.General.RationalCartanLatticeModel
import Langlands.Representation.Aubert.General.RationalIwasawaCartan
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! # Actual Cartan charts retaining every central lattice direction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.Cartan
open Langlands.BruhatTits.SpecialCompact Langlands.Plancherel.RenardCartan
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily

namespace Langlands.Plancherel

/-- The supplied actual Levi-Cartan witness gives finitely many independent
weakly positive cocharacter charts, covering the entire rational point group. -/
def RationalFiniteSignedCartanCoverStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    ∀ [Fintype (SimpleRoot i ν)], IsGenericCocharacter i ν →
      StandardCocharacterStatement.{u} →
      ∀ (D : KPApartmentData i (localFieldOrder F)) (x : D.Apartment)
        (Z : GroupScheme (Spec (CommRingCat.of F))) (j : Z ⟶ G)
        (s : S.toGrp ⟶ Z) (h : Function.Bijective (restrictionEvaluation s)),
        s ≫ j = i →
        SpecialCompactStandardLeviCompatibility D x ν s h j →
        ∀ (F₀ : Set (rationalPoints Z)), IsFiniteLatticeTransversal s F₀ →
          ∃ (k : ℕ)
            (gen : (Fin k → Bool) → (SimpleRoot i ν ⊕ Fin k) → cocharacterLattice S),
            (∀ ε, LinearIndependent ℤ (gen ε)) ∧
            (∀ ε a α, 0 ≤ simpleRootPairing i ν α (gen ε a)) ∧
            ∃ T : Set (rationalPoints G), T.Finite ∧
              ∀ g : rationalPoints G, ∃ ε : Fin k → Bool,
                ∃ n : (SimpleRoot i ν ⊕ Fin k) → ℕ,
                ∃ k₁ ∈ D.specialCompactSubgroup x, ∃ t ∈ T,
                ∃ k₂ ∈ D.specialCompactSubgroup x,
                  g = k₁ * uniformizerPowers i (.ofAdd (∑ a, n a • gen ε a)) * t * k₂

end Langlands.Plancherel
