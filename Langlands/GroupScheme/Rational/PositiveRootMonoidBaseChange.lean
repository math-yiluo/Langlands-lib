import Langlands.GroupScheme.Rational.FundamentalRepresentations
import Langlands.GroupScheme.Reductive.PinningBaseChange

/-! # Positive simple-root monoids under algebraic field extension -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  [Algebra.IsAlgebraic k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (p : SplitPinning G)

local notation "bc" => algebraBaseMap k K

local instance positiveRootBaseChangeAffine :
    IsAffineHom ((GroupScheme.baseChange bc).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom bc)
  infer_instance

/-- The positive simple-root monoid is carried to the new positive simple-root monoid. -/
theorem map_positiveRootMonoid_baseChange :
    p.positiveRootMonoid.map (characterLattice.baseChange bc p.torus) =
      (p.baseChange (F := K)).positiveRootMonoid := by
  change (AddSubmonoid.closure
    (Set.range (fun a : p.base.support => p.rootDatum.root a))).map
      (characterLattice.baseChange bc p.torus) =
    AddSubmonoid.closure (Set.range (fun a : (p.baseChangeBase (F := K)).support =>
      (p.baseChangeRootDatum (F := K)).root a))
  rw [AddMonoidHom.map_mclosure]
  apply congrArg AddSubmonoid.closure
  ext χ
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨p.baseChangeSimpleEquiv (F := K) a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨p.rootDatum.root ((p.baseChangeSimpleEquiv (F := K)).symm a),
      ⟨(p.baseChangeSimpleEquiv (F := K)).symm a, rfl⟩, rfl⟩

/-- Canonical pullback identifies the additive monoids of positive simple-root combinations. -/
def positiveRootMonoidBaseChangeEquiv :
    p.positiveRootMonoid ≃+ (p.baseChange (F := K)).positiveRootMonoid :=
  (p.positiveRootMonoid.equivMapOfInjective
    (characterLattice.baseChange bc p.torus)
    (p.isSplitTorus.characterLattice_baseChange_bijective bc p.torus).injective).trans
      (AddEquiv.addSubmonoidCongr (map_positiveRootMonoid_baseChange (K := K) p))

/-- Membership of a pulled-back character in the positive-root monoid is reflected. -/
theorem mem_positiveRootMonoid_baseChange_iff (χ : characterLattice p.torus) :
    characterLattice.baseChange bc p.torus χ ∈
      (p.baseChange (F := K)).positiveRootMonoid ↔ χ ∈ p.positiveRootMonoid := by
  rw [← map_positiveRootMonoid_baseChange (K := K) p]
  constructor
  · rintro ⟨ψ, hψ, heq⟩
    exact (p.isSplitTorus.characterLattice_baseChange_bijective bc p.torus).injective heq ▸ hψ
  · intro hχ
    exact ⟨χ, hχ, rfl⟩

end Langlands.GroupScheme.SplitPinning
