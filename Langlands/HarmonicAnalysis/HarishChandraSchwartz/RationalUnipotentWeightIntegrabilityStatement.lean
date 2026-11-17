import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiUpperBoundStatement
import Langlands.Representation.Aubert.General.RationalCartanSupportReduction
import Langlands.Representation.Aubert.General.RationalOppositeParabolic

/-! # Waldspurger's Lemma II.4.2 on the actual opposite radical -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- Lemma II.4.2 with the actual opposite contraction subgroup and Iwasawa weight. -/
def RationalUnipotentWeightIntegrabilityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ (J : Set (characterLattice S)) (ζ : cocharacterLattice S),
      IsStandardCocharacter i ν J ζ →
    ∀ K0 : Subgroup (rationalPoints G), IsOpen (K0 : Set (rationalPoints G)) →
      IsCompact (K0 : Set (rationalPoints G)) → SimultaneousStandardBasisAt i ν K0 →
      Aubert.General.RationalPointFamily.FiniteCartanCovering F i ν K0 →
    ∀ K : Subgroup (rationalPoints G), IsOpen (K : Set (rationalPoints G)) →
    ∀ (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K),
      IsCompact (K : Set (rationalPoints G)) →
    ∀ (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∀ (nuU : Measure (Aubert.General.RationalPointFamily.oppositeUnipotent i ζ))
      [nuU.IsHaarMeasure],
    ∃ d : ℕ,
      ∫⁻ u : Aubert.General.RationalPointFamily.oppositeUnipotent i ζ,
        ENNReal.ofReal
          (iwasawaWeight hPK (rationalMinimalModulus i ν) (u : rationalPoints G) *
            (1 + rationalHeight (F := F) ρ (u : rationalPoints G)) ^ (-(d : ℝ))) ∂nuU < ⊤

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

/-- The natural-exponent estimate supplies the abstract integrability hypothesis. -/
theorem RationalUnipotentWeightIntegrabilityStatement.unipotentWeightIntegrable
    (h : RationalUnipotentWeightIntegrabilityStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice S)}
    {ζ : cocharacterLattice S} (hζ : IsStandardCocharacter i ν J ζ)
    {K0 : Subgroup (rationalPoints G)}
    (hK0o : IsOpen (K0 : Set (rationalPoints G)))
    (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0)
    (hcover : Aubert.General.RationalPointFamily.FiniteCartanCovering F i ν K0)
    {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    {N : ℕ} [Nonempty (Fin N)] {ρ : MatrixRepresentation G (Fin N)}
    (hρ : IsClosedSubgroup ρ)
    (nuU : Measure (Aubert.General.RationalPointFamily.oppositeUnipotent i ζ))
    [nuU.IsHaarMeasure] :
    UnipotentWeightIntegrable nuU
      (fun u : Aubert.General.RationalPointFamily.oppositeUnipotent i ζ =>
        iwasawaWeight hPK (rationalMinimalModulus i ν) (u : rationalPoints G))
      (rationalHeight (F := F) ρ) := by
  obtain ⟨d, hd⟩ := h F G hG S i hi ν hν J ζ hζ K0 hK0o hK0c hbasis hcover
    K hKo hPK hKc N ρ hρ nuU
  exact ⟨d, hd⟩

end Langlands.HarishChandraSchwartz
