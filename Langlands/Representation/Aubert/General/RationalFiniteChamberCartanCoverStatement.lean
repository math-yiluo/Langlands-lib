import Langlands.Representation.Aubert.General.RationalCartanLatticeModel
import Langlands.Representation.Aubert.General.RationalIwasawaCartan
import Mathlib.GroupTheory.Subgroup.Center

/-! # Actual uniformizer charts modulo the full rational-point center -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.Cartan
open Langlands.BruhatTits.SpecialCompact Langlands.Plancherel.RenardCartan
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General.RationalPointFamily

/-- The supplied actual special-compact and Levi-Cartan witness gives finite
uniformizer charts modulo the full center, including empty-root compactness. -/
def RationalFiniteChamberCartanCoverStatement : Prop :=
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
        SpecialCompactProperties F i ν (D.specialCompactSubgroup x) →
        SpecialCompactStandardLeviCompatibility D x ν s h j →
        ∀ (F₀ : Set (rationalPoints Z)), IsFiniteLatticeTransversal s F₀ →
          letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
          letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
          ∃ gen : SimpleRoot i ν → cocharacterLattice S,
            (∀ α, 0 < simpleRootPairing i ν α (gen α)) ∧
            (∀ α β, β ≠ α → simpleRootPairing i ν β (gen α) = 0) ∧
            ∃ T : Set (rationalPoints G), T.Finite ∧
              (∀ g : rationalPoints G, ∃ n : SimpleRoot i ν → ℕ,
                ∃ k₁ ∈ D.specialCompactSubgroup x, ∃ t ∈ T,
                ∃ k₂ ∈ D.specialCompactSubgroup x, ∃ z ∈ Subgroup.center (rationalPoints G),
                  g = k₁ * uniformizerPowers i (.ofAdd (∑ α, n α • gen α)) * t * k₂ * z) ∧
              (IsEmpty (SimpleRoot i ν) →
                CompactSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G)))

end Langlands.Aubert.General.RationalPointFamily
