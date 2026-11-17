import Langlands.GroupScheme.Reductive.AffineSplitIsogenyCommonPowerRelations
import Langlands.GroupScheme.Reductive.LocalSplitTargetWordLaws

/-! # All standard rank-two word laws for powered target maps -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffineRootDatumIsogeny

open LocalSplitCell

variable {R : Type u} [CommRing R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced] {p : ℕ}
  {H : GroupScheme (Spec (CommRingCat.of R))}
  (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
  (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)
  {b : P.Base} {b' : Q.Base}

/-- All standard A2, B2 and G2 source word formulas for the actual powered maps. -/
def StandardPoweredWordRelations (W : ∀ α, SimpleWord P b α)
    (u' : J' → (Ga R ⟶ H)) : Prop :=
  (∀ {a c : J}, a ∈ b.support → c ∈ b.support → a ≠ c →
    P.pairingIn ℤ a c = -1 → P.pairingIn ℤ c a = -1 →
    CommRel (weylFamily P W (poweredRootFamily f hchar u') a)
      (weylFamily P W (poweredRootFamily f hchar u') c)
      (wordTerms (P := P) (poweredRootFamily f hchar u')
        (weylFamily P W (poweredRootFamily f hchar u')) [([a], c, -1, 1, 1)])) ∧
  (∀ {a c : J}, a ∈ b.support → c ∈ b.support → a ≠ c →
    P.pairingIn ℤ a c = -1 → P.pairingIn ℤ c a = -2 →
    PoweredB2WordRelations f hchar W u' a c) ∧
  (∀ {a c : J}, a ∈ b.support → c ∈ b.support → a ≠ c →
    P.pairingIn ℤ a c = -1 → P.pairingIn ℤ c a = -3 →
    PoweredG2WordRelations f hchar W u' a c)

variable [IsLocalRing R] [DecidableEq I'] [IsAffineHom H.X.hom]
  {i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H}

/-- The complete root-factor classification supplies every standard powered word law
from genuine normalized target data. -/
theorem standardPoweredWordRelations_of_normalData
    (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support)
    (W : ∀ α, SimpleWord P b α) (u' : J' → (Ga R ⟶ H))
    (hd : IsNormalSimpleData i' Q b' (targetSimpleWords f hb W) u') :
    StandardPoweredWordRelations f hchar W u' := by
  have pattern (a c : J) (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c) :
      Langlands.LinearAlgebra.RootDatumIsogeny.RankTwoScalingPattern
        (Q.pairingIn ℤ (f.indexEquiv.symm a) (f.indexEquiv.symm c))
        (Q.pairingIn ℤ (f.indexEquiv.symm c) (f.indexEquiv.symm a))
        (P.pairingIn ℤ a c) (P.pairingIn ℤ c a)
        (f.rootFactor (f.indexEquiv.symm a)) (f.rootFactor (f.indexEquiv.symm c)) := by
    simpa only [Equiv.apply_symm_apply] using
      f.rankTwoScalingPattern b' b (hb a ha) (hb c hc)
        (fun h => hac (f.indexEquiv.symm.injective h))
        (by simpa only [Equiv.apply_symm_apply] using ha)
        (by simpa only [Equiv.apply_symm_apply] using hc)
  refine ⟨?_, ?_, ?_⟩
  · intro a c ha hc hac h1 h2
    cases pattern a c ha hc hac with
    | orthogonal _ _ hs1 hs2 => omega
    | equal e1 e2 _ =>
      exact a2_wordCommRel_of_normalData f hchar hb W u' hd ha hc hac h1
        (e1.trans h1) (e2.trans h2)
    | doubleForward _ _ hs1 hs2 _ => omega
    | doubleReverse _ _ hs1 hs2 _ => omega
    | tripleForward _ _ hs1 hs2 _ => omega
    | tripleReverse _ _ hs1 hs2 _ => omega
  · intro a c ha hc hac h1 h2
    cases pattern a c ha hc hac with
    | orthogonal _ _ hs1 hs2 => omega
    | equal e1 e2 _ =>
      exact b2_wordRelations_equalFactors_of_normalData f hchar hb W u' hd ha hc hac h1
        (e1.trans h1) (e2.trans h2)
    | doubleForward _ _ hs1 hs2 _ => omega
    | doubleReverse e1 e2 _ _ _ =>
      exact poweredB2WordRelations_of_normalData f hchar hb W u' hd ha hc hac h1 e2 e1
    | tripleForward _ _ hs1 hs2 _ => omega
    | tripleReverse _ _ hs1 hs2 _ => omega
  · intro a c ha hc hac h1 h2
    cases pattern a c ha hc hac with
    | orthogonal _ _ hs1 hs2 => omega
    | equal e1 e2 _ =>
      exact g2_wordRelations_equalFactors_of_normalData f hchar hb W u' hd ha hc hac h1
        (e1.trans h1) (e2.trans h2)
    | doubleForward _ _ hs1 hs2 _ => omega
    | doubleReverse _ _ hs1 hs2 _ => omega
    | tripleForward _ _ hs1 hs2 _ => omega
    | tripleReverse e1 e2 _ _ _ =>
      exact poweredG2WordRelations_of_normalData f hchar hb W u' hd ha hc hac h1 e2 e1

/-- For the target-word law bundle, only no-cone commutation remains after standard
rank-two transport has been established. -/
theorem targetWordRelations_powered_of_noCone
    (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support)
    (W : ∀ α, SimpleWord P b α) (u' : J' → (Ga R ⟶ H))
    (hd : IsNormalSimpleData i' Q b' (targetSimpleWords f hb W) u')
    (hno : ∀ {x y : J}, P.root x ≠ -P.root y →
      (∀ (α : J) (s t : ℕ), 1 ≤ s → 1 ≤ t →
        (s : ℤ) • P.root x + (t : ℤ) • P.root y ≠ P.root α) →
      PointsCommute (weylFamily P W (poweredRootFamily f hchar u') x)
        (weylFamily P W (poweredRootFamily f hchar u') y)) :
    TargetWordRelations P b W (poweredRootFamily f hchar u') := by
  obtain ⟨hA, hB, hG⟩ := standardPoweredWordRelations_of_normalData f hchar hb W u' hd
  exact ⟨hno, hA, hB, hG⟩

end Langlands.GroupScheme.AffineRootDatumIsogeny
