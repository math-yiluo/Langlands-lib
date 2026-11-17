import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiUpperBoundStatement
import Langlands.Representation.Aubert.General.RationalCartanSupportReduction
import Langlands.GroupScheme.Rational.TitsStandardParabolic

/-! # The global Iwasawa-weight upper bound on actual rational points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- The global form of the upper bound used in Waldspurger's Lemma II.4.4. -/
def RationalXiGlobalUpperBoundStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ K0 : Subgroup (rationalPoints G), IsOpen (K0 : Set (rationalPoints G)) →
      IsCompact (K0 : Set (rationalPoints G)) → SimultaneousStandardBasisAt i ν K0 →
      Aubert.General.RationalPointFamily.FiniteCartanCovering F i ν K0 →
    ∀ K : Subgroup (rationalPoints G), IsOpen (K : Set (rationalPoints G)) →
    ∀ (hKc : IsCompact (K : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
      (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∃ (D : ℕ) (C : ℝ), 0 < C ∧ ∀ g : rationalPoints G,
      rationalXi hKc hPK g ≤
        C * iwasawaWeight hPK (rationalMinimalModulus i ν) g *
          (1 + rationalHeight (F := F) ρ g) ^ D

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

/-- Restatement in the abstract global-upper-bound interface. -/
theorem RationalXiGlobalUpperBoundStatement.xiUpperBound
    (h : RationalXiGlobalUpperBoundStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {K0 : Subgroup (rationalPoints G)}
    (hK0o : IsOpen (K0 : Set (rationalPoints G)))
    (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0)
    (hcover : Aubert.General.RationalPointFamily.FiniteCartanCovering F i ν K0)
    {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    {N : ℕ} [Nonempty (Fin N)] {ρ : MatrixRepresentation G (Fin N)}
    (hρ : IsClosedSubgroup ρ) :
    XiUpperBound (rationalXi hKc hPK) (rationalHeight (F := F) ρ) Set.univ
      (iwasawaWeight hPK (rationalMinimalModulus i ν)) := by
  obtain ⟨D, C, -, hC⟩ := h F G hG S i hi ν hν K0 hK0o hK0c hbasis hcover K hKo hKc hPK N ρ hρ
  exact ⟨C, D, fun g _ => by simpa only [Real.rpow_natCast] using hC g⟩

/-- Lemma II.4.4 for any subgroup `U`, in particular the opposite radical of a
standard parabolic, and every point of the minimal Levi `Z_G(S)(F)`. -/
theorem RationalXiGlobalUpperBoundStatement.unipotentXiBound
    (h : RationalXiGlobalUpperBoundStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {K0 : Subgroup (rationalPoints G)}
    (hK0o : IsOpen (K0 : Set (rationalPoints G)))
    (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0)
    (hcover : Aubert.General.RationalPointFamily.FiniteCartanCovering F i ν K0)
    {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    {N : ℕ} [Nonempty (Fin N)] {ρ : MatrixRepresentation G (Fin N)}
    (hρ : IsClosedSubgroup ρ) (U : Subgroup (rationalPoints G)) :
    UnipotentXiBound (U := U) (rationalXi hKc hPK) (rationalHeight (F := F) ρ)
      (Set.univ : Set (centralizerPoints i))
      (fun m => iwasawaWeight hPK (rationalMinimalModulus i ν) (m : rationalPoints G))
      (fun u : U => iwasawaWeight hPK (rationalMinimalModulus i ν) (u : rationalPoints G)) := by
  exact (h.xiUpperBound hG hi hν hK0o hK0c hbasis hcover hKo hKc hPK hρ).unipotentXiBound_iwasawaWeight
      (fun p hp => rationalMinimalModulus_eq_one i ν hKo hKc p hp)
      (fun m _ => centralizerPoints_le_standardParabolicPoints i ν ∅ m.2)

end Langlands.HarishChandraSchwartz
