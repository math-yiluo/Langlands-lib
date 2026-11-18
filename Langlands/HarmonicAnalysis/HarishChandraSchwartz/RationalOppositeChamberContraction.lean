import Langlands.Representation.Aubert.General.RationalOppositeChamber
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalChamberContraction

/-! # Inversion of actual chambers and the opposite contraction estimate -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.BruhatTits.Cartan

namespace Langlands.HarishChandraSchwartz

section Roots

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- Opposite positive roots are the negatives of the original ones. -/
theorem mem_positiveRelativeRoots_neg_iff
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i) (α : characterLattice S) :
    α ∈ positiveRelativeRoots i (-ν) ↔ -α ∈ positiveRelativeRoots i ν :=
  by simpa only [neg_neg] using (neg_mem_positiveRelativeRoots_iff i ν hneg (-α))

/-- The simple roots of the opposite chamber are exactly the negatives of
the original simple roots, including empty and nonreduced root systems. -/
theorem mem_simpleRelativeRoots_neg_iff
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i) (α : characterLattice S) :
    α ∈ simpleRelativeRoots i (-ν) ↔ -α ∈ simpleRelativeRoots i ν :=
  by simpa only [neg_neg] using (neg_mem_simpleRelativeRoots_iff i ν hneg (-α))

end Roots

section Rational

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

omit [LocallyOfFiniteType G.X.hom] in
/-- Inversion exchanges the full actual minimal chamber with its opposite. -/
theorem inv_mem_rationalMinimalChamber_neg
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {a : rationalPoints G} (ha : a ∈ rationalMinimalChamber i ν) :
    a⁻¹ ∈ rationalMinimalChamber i (-ν) := by
  have := hi.isSplitSubtorus.mono
  have hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i := fun α hα =>
    (relativeRootSystem F G hG S i hi).neg_mem_relativeRoots i hi.isSplitSubtorus.1 hα
  obtain ⟨s, rfl, hs⟩ := (mem_rationalMinimalChamber_iff_order i ν a).mp ha
  apply (mem_rationalMinimalChamber_iff_order i (-ν) _).mpr
  refine ⟨s⁻¹, by simp, ?_⟩
  intro α hα
  have h := hs (-α) ((mem_simpleRelativeRoots_neg_iff i ν hneg α).mp hα)
  simpa only [RenardLeviCones.characterOrder, map_neg, map_inv,
    toAdd_inv, AddMonoidHom.neg_apply] using h

/-- The opposite-minimal-parabolic version of II.3.3 used in the tail
cutoff argument: inverse conjugation by the original positive chamber. -/
theorem exists_one_add_rationalHeight_inv_conj_le_on_opposite
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation G n) :
    ∃ C ≥ 1, ∀ a ∈ rationalMinimalChamber i ν,
      ∀ p ∈ standardParabolicPoints i (-ν) ∅,
        1 + rationalHeight (F := F) ρ (a⁻¹ * p * a) ≤
          C * (1 + rationalHeight (F := F) ρ p) := by
  obtain ⟨C, hC, hb⟩ := exists_one_add_rationalHeight_conj_le_on_chamber hG hi
    (IsGenericCocharacter.neg i ν hν) ρ
  refine ⟨C, hC, fun a ha p hp => ?_⟩
  simpa only [inv_inv] using hb a⁻¹ (inv_mem_rationalMinimalChamber_neg hG hi ha) p hp

end Rational

/-- Closed opposite-minimal-parabolic contraction statement, with the
original positive chamber and the original arbitrary matrix realization. -/
def RationalOppositeChamberConjugationHeightStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)),
      ∃ C ≥ 1, ∀ a ∈ rationalMinimalChamber i ν,
        ∀ p ∈ standardParabolicPoints i (-ν) ∅,
          1 + rationalHeight (F := F) ρ (a⁻¹ * p * a) ≤
            C * (1 + rationalHeight (F := F) ρ p)

/-- The opposite contraction follows from the same actual height theorem,
with every source and target inverse accounted for. -/
theorem rationalOppositeChamberConjugationHeight :
    RationalOppositeChamberConjugationHeightStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν N _ ρ
  exact exists_one_add_rationalHeight_inv_conj_le_on_opposite hG hi hν ρ

end Langlands.HarishChandraSchwartz
