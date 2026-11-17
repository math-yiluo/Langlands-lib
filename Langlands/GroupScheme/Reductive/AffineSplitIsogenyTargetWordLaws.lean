import Langlands.GroupScheme.Reductive.AffineSplitIsogenyStandardWordLaws
import Langlands.GroupScheme.Reductive.IsogenyNoConeCommutation

/-! # Complete target word laws for the actual powered family -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.AffineRootDatumIsogeny

open LocalSplitCell

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [DecidableEq I']
  [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced] {p : ℕ}
  {H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom H.X.hom]
  (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
  (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)
  {b : P.Base} {b' : Q.Base}
  {i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H}

/-- Source no-cone pairs commute in the powered target Weyl family. -/
theorem pointsCommute_poweredWeylFamily
    (hi' : IsClosedSubgroup i')
    (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support)
    (W : ∀ α, SimpleWord P b α) (u' : J' → (Ga R ⟶ H))
    (hd : IsNormalSimpleData i' Q b' (targetSimpleWords f hb W) u')
    {x y : J} (hneg : P.root x ≠ -P.root y)
    (hcone : ∀ (α : J) (s t : ℕ), 1 ≤ s → 1 ≤ t →
      (s : ℤ) • P.root x + (t : ℤ) • P.root y ≠ P.root α) :
    PointsCommute (weylFamily P W (poweredRootFamily f hchar u') x)
      (weylFamily P W (poweredRootFamily f hchar u') y) := by
  have h := IsogenyNoCone.pointsCommute_correspondingRoots f hd.reductive i' hi'
    hd.maximal hd.rootDatum hchar (hd.isRootParametrization (f.indexEquiv.symm x))
    (hd.isRootParametrization (f.indexEquiv.symm y)) hneg hcone
  rw [weylFamily_powered_eq f hchar hb W u',
    weylFamily_powered_eq f hchar hb W u']
  exact h.precompose_powers
    (rootPower f hchar (f.indexEquiv.symm x)) (rootPower f hchar (f.indexEquiv.symm y))
    (f.rootFactor (f.indexEquiv.symm x)) (f.rootFactor (f.indexEquiv.symm y))
    (rootPoint_rootPower f hchar _) (rootPoint_rootPower f hchar _)

/-- The complete target law bundle follows from the actual normalized target data and
the original root-datum-isogeny characteristic condition. -/
theorem targetWordRelations_powered
    (hi' : IsClosedSubgroup i')
    (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support)
    (W : ∀ α, SimpleWord P b α) (u' : J' → (Ga R ⟶ H))
    (hd : IsNormalSimpleData i' Q b' (targetSimpleWords f hb W) u') :
    TargetWordRelations P b W (poweredRootFamily f hchar u') :=
  targetWordRelations_powered_of_noCone f hchar hb W u' hd
    (fun {x y} hneg hcone =>
      pointsCommute_poweredWeylFamily f hchar hi' hb W u' hd (x := x) (y := y) hneg hcone)

end Langlands.GroupScheme.AffineRootDatumIsogeny

namespace Langlands.GroupScheme

open LocalSplitCell AffineRootDatumIsogeny

/-- Complete actual powered target word laws over arbitrary local coefficient rings. -/
def PoweredTargetWordRelationsStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (I I' J J' : Type u) [Fintype I] [Fintype I'] [DecidableEq I'] [Finite J] [Finite J']
    (P : RootDatum J (I → ℤ) (I → ℤ)) (Q : RootDatum J' (I' → ℤ) (I' → ℤ))
    [P.IsReduced] [Q.IsReduced] (p : ℕ) (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)
    (H : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom H.X.hom]
    (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H),
    IsClosedSubgroup i' →
    ∀ (b : P.Base) (b' : Q.Base)
    (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support)
    (W : ∀ α, SimpleWord P b α) (u' : J' → (Ga R ⟶ H)),
    IsNormalSimpleData i' Q b' (targetSimpleWords f hb W) u' →
      TargetWordRelations P b W (poweredRootFamily f hchar u')

/-- Every no-cone and standard-rank-two field is supplied by the actual target maps. -/
theorem poweredTargetWordRelations : PoweredTargetWordRelationsStatement.{u} := by
  intro R _ _ I I' J J' _ _ _ _ _ P Q _ _ p f hchar H _ i' hi' b b' hb W u' hd
  exact targetWordRelations_powered f hchar hi' hb W u' hd

end Langlands.GroupScheme
