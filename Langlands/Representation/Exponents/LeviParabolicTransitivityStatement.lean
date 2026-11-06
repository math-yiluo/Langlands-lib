import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.GroupScheme.Reductive.Basic

/-! # Transitivity of normalized induction and Jacquet restriction for represented parabolics

Renard 2026, VI.1.4, Lemma (printed pp.136–137/PDF pp.142–143): for parabolic subgroups
`P = MN ⊂ Q = LU` of `G`, the intersection `L ∩ P` is a parabolic subgroup of `L` with
Levi factor `M`, and there are natural isomorphisms `i_P^G ≅ i_Q^G ∘ i_{L∩P}^L` and
`r_P^G ≅ r_{L∩P}^L ∘ r_Q^G`. Here the three parabolics are actual rational parabolic
triples; the parabolic `L ∩ P` of `L` is given by explicit data with the same Levi group
scheme `M`, and is pinned down by its rational points.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.1.4, Lemma: for actual rational parabolics `P = MN` and `Q = LU` of `G` with
`P(F) ⊆ Q(F)`, and an actual rational parabolic `P_L = M N_L` of `L` with the same Levi
group scheme `M`, the same embedding of `M` in `G`, and `P_L(F) = L(F) ∩ P(F)` inside
`G(F)`, normalized induction satisfies `i_P^G ≅ i_{P_L}^L ⋙ i_Q^G` and normalized
Jacquet restriction satisfies `r_P^G ≅ r_Q^G ⋙ r_{P_L}^L`. -/
def LeviParabolicTransitivityStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N Q L U PL NL : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
      (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (hmul : IsIso (subgroupMultiplication m n))
      (q : Q ⟶ G) (l : L ⟶ Q) (uQ : U ⟶ Q)
      (hq : IsParabolicSubgroup q) (hl : IsRationalLeviSubgroup l)
      (huQ : LeviSubgroup.IsGeometricUnipotentRadical uQ)
      (hmulQ : IsIso (subgroupMultiplication l uQ))
      (pL : PL ⟶ L) (mL : M ⟶ PL) (nL : NL ⟶ PL)
      (hpL : IsParabolicSubgroup pL) (hmL : IsRationalLeviSubgroup mL)
      (hnL : LeviSubgroup.IsGeometricUnipotentRadical nL)
      (hmulL : IsIso (subgroupMultiplication mL nL)),
      pointImage p ≤ pointImage q →
      mL ≫ pL ≫ l ≫ q = m ≫ p →
      pointImage (pL ≫ l ≫ q) = pointImage (l ≫ q) ⊓ pointImage p →
        haveI := hl.isConnectedReductive.isAffineHom
        letI : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
        haveI : LocallyCompactSpace (rationalPoints L) :=
          leviPoints_locallyCompactSpace q l hq hl
        haveI : NonarchimedeanGroup (rationalPoints L) :=
          leviPoints_nonarchimedeanGroup q l hq hl
        haveI := hm.isConnectedReductive.isAffineHom
        letI : TopologicalSpace (rationalPoints M) := leviPointTopology m hm
        Nonempty (leviInductionFunctor.{u, v} p m n hp hn hm hmul ≅
            leviInductionFunctor.{u, v} pL mL nL hpL hnL hmL hmulL ⋙
              leviInductionFunctor.{u, max u v} q l uQ hq huQ hl hmulQ) ∧
          Nonempty (leviJacquetFunctor.{u, v} p m n hp hn hm hmul ≅
            leviJacquetFunctor.{u, v} q l uQ hq huQ hl hmulQ ⋙
              leviJacquetFunctor.{u, v} pL mL nL hpL hnL hmL hmulL)

end Langlands.Aubert.General.RepresentedParabolic
