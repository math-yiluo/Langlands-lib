import Langlands.GroupScheme.Quaternionic.LocalSpinRankOneStatement
import Langlands.GroupScheme.CentralIsogeny.AlmostSimpleTransfer
import Langlands.GroupScheme.Rational.CentralIsogenySplitRank

/-! # Almost simplicity and split rank of quaternionic spin covers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] {σ : FirstKindInvolution K D}
  {n : Type} [Fintype n] [DecidableEq n] {q : σ.QuadraticForms n}
  [Smooth (σ.isometryGroup q).X.hom]
  {S : GroupScheme (Spec (CommRingCat.of K))}
  {π : S ⟶ σ.isometryGroup q}

/-- A spin cover of a form with almost-simple connected isometry group is
almost simple. -/
theorem IsSpinCover.isAlmostSimple (hπ : σ.IsSpinCover q π)
    (hG : IsAlmostSimple (σ.connectedIsometryGroup q)) :
    IsAlmostSimple S := by
  obtain ⟨p, hp, _⟩ := hπ.exists_centralIsogeny
  exact IsAlmostSimple.of_isCentralIsogeny p hp hG
    hπ.isSimplyConnected.isSemisimple.isConnectedReductive.smooth
    hπ.isSimplyConnected.isSemisimple.isConnectedReductive.connectedSpace

/-- Every spin cover has the same split rank as the connected isometry group. -/
theorem IsSpinCover.splitRank_eq (hπ : σ.IsSpinCover q π) :
    splitRank S = splitRank (σ.connectedIsometryGroup q) := by
  let : IsAffineHom S.X.hom :=
    hπ.isSimplyConnected.isSemisimple.isConnectedReductive.isAffineHom
  obtain ⟨p, hp, _⟩ := hπ.exists_centralIsogeny
  exact hp.splitRank_eq

/-- Almost simplicity and split rank one of the connected isometry group imply
the requested properties of every spin cover. -/
theorem IsSpinCover.properties_of_connectedIsometryGroup
    (hπ : σ.IsSpinCover q π)
    (hG : IsAlmostSimple (σ.connectedIsometryGroup q))
    (hrank : splitRank (σ.connectedIsometryGroup q) = 1) :
    IsSimplyConnected S ∧ IsAlmostSimple S ∧ splitRank S = 1 :=
  ⟨hπ.isSimplyConnected, hπ.isAlmostSimple hG, hπ.splitRank_eq.trans hrank⟩

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution

namespace Langlands.GroupScheme.Quaternionic

/-- The general property-transfer step for quaternionic spin covers. -/
def SpinCoverPropertiesReductionStatement : Prop :=
  ∀ (K D : Type u) [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
    (σ : FirstKindInvolution K D)
    (n : Type) [Fintype n] [DecidableEq n] (q : σ.QuadraticForms n)
    (hsm : Smooth (σ.isometryGroup q).X.hom),
    letI := hsm
    IsAlmostSimple (σ.connectedIsometryGroup q) →
      ∀ (S : GroupScheme (Spec (CommRingCat.of K))) (π : S ⟶ σ.isometryGroup q),
        σ.IsSpinCover q π →
          IsSimplyConnected S ∧ IsAlmostSimple S ∧
            splitRank S = splitRank (σ.connectedIsometryGroup q)

theorem spinCoverPropertiesReduction : SpinCoverPropertiesReductionStatement.{u} := by
  intro K D _ _ _ _ σ n _ _ q hsm
  let := hsm
  intro hG S π hπ
  exact ⟨hπ.isSimplyConnected, hπ.isAlmostSimple hG, hπ.splitRank_eq⟩

end Langlands.GroupScheme.Quaternionic
