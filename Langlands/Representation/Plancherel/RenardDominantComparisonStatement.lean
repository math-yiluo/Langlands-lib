import Langlands.Representation.Plancherel.RenardRepresentativeData
import Langlands.BruhatTits.Cartan.CentralizerValuationConsequences
import Langlands.GroupScheme.Rational.TorusCentralizer

/-! # Actual dominant centralizer sections and finite positive covers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.GroupScheme Langlands.BruhatTits.Cartan
open scoped CategoryTheory.MonObj Pointwise TensorProduct

namespace Langlands.Plancherel.RenardCartan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {Z : GroupScheme (Spec (CommRingCat.of F))}

/-- The exact chamber comparisons and finite representative conclusions.
The closed statement below imposes the actual maximal-split-centralizer
conditions; this predicate does not assume any of its conclusions. -/
def DominantCentralizerLatticeConclusions (i : S.toGrp ⟶ G)
    (ν : cocharacterLattice S) (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (restrictionEvaluation s)) : Prop :=
  let D := dominantCentralizer i ν s h
  let Φplus := positiveRelativeRoots i ν
  (∀ c : cocharacterLattice S,
    (centralizerValuation s h
      (rationalPoints.map s (uniformizerSection S (Multiplicative.ofAdd c)))).toAdd =
        1 ⊗ₜ[ℤ] c) ∧
  C0Plus S s Φplus = (C0 S s : Set (rationalPoints Z)) ∩ D ∧
  centralizerValuationImageEquiv s h '' dominantValuationImage i ν s h =
    (rationalCharacterValuation Z).rangeRestrict '' D ∧
  (∃ F0 : Set (rationalPoints Z),
    IsFiniteLatticeTransversal s F0 ∧ F0 ⊆ D) ∧
  (∀ F0 : Set (rationalPoints Z), IsFiniteLatticeTransversal s F0 →
    IsDominantValuationSection D (tildeC0Plus s F0 D) ∧
    Set.BijOn (centralizerValuation s h).rangeRestrict (tildeC0Plus s F0 D)
      (dominantValuationImage i ν s h)) ∧
  (∃ Fcover : Set (rationalPoints Z),
    IsFinitePositiveProductCover s Φplus D Fcover) ∧
  (∀ F0 : Set (rationalPoints Z),
    IsChamberCompatibleTransversal s Φplus D F0 →
      IsDominantValuationSection D (C0Plus S s Φplus * F0) ∧
      HasNonrepeatingPositiveProducts s Φplus F0)

/-- For the actual centralizer of a chosen maximal split torus, uniformizer
positivity agrees with the corrected dominant chamber. Full transversals
cut to dominant sections, finite positive covers exist, and a separately
chamber-compatible transversal gives nonrepeating positive products. -/
def RenardDominantComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom],
      IsConnectedReductive G →
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
        IsMaximalSplitTorus i →
        ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
          ∀ (Z : GroupScheme (Spec (CommRingCat.of F))) (j : Z ⟶ G),
            IsClosedSubgroup j → (torusCentralizer i).IsRepresentedBy j →
            ∀ s : S.toGrp ⟶ Z, s ≫ j = i →
              ∀ h : Function.Bijective (restrictionEvaluation s),
                DominantCentralizerLatticeConclusions i ν s h

end Langlands.Plancherel.RenardCartan
