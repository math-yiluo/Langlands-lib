import Langlands.GroupScheme.IntegralModel.GreenbergPointModel

/-! # Characteristic cases and the first congruence level of Greenberg point models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

/-- The complete point-model conclusion for one ring, congruence level and target group.
The target model and its point equivalence are fixed before any source homomorphism. -/
def HasGreenbergPointModel (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ+)
    (X : GroupScheme (Spec (CommRingCat.of R))) : Prop :=
  ∃ (G : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))
    (eX : rationalPoints ((GroupScheme.baseChange (congruenceBaseMap R n)).obj X) ≃*
      rationalPoints G),
    IsAffineHom G.X.hom ∧ Smooth G.X.hom ∧
    ∀ (Z : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom Z.X.hom],
      Smooth Z.X.hom → ∀ h : Z ⟶ X,
      ∃ (GZ : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))
        (eZ : rationalPoints ((GroupScheme.baseChange (congruenceBaseMap R n)).obj Z) ≃*
          rationalPoints GZ)
        (g : GZ ⟶ G),
        IsAffineHom GZ.X.hom ∧ Smooth GZ.X.hom ∧
        (∀ z, eX (rationalPoints.map ((GroupScheme.baseChange (congruenceBaseMap R n)).map h)
            z) = rationalPoints.map g (eZ z)) ∧
        (GeometricallyConnected Z.X.hom → GeometricallyConnected GZ.X.hom)

/-- Greenberg point models over equal-characteristic DVRs, with all the conclusions
and the full source naturality of `GreenbergPointModelStatement`. -/
def EqualCharacteristicGreenbergPointModelStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)],
    ringChar R = ringChar (IsLocalRing.ResidueField R) →
    ∀ (n : ℕ+) (X : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom X.X.hom],
      Smooth X.X.hom → HasGreenbergPointModel R n X

/-- Greenberg point models over DVRs whose ring and residue-field characteristics
differ, retaining every point, naturality and connectedness conclusion. -/
def MixedCharacteristicGreenbergPointModelStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)],
    ringChar R ≠ ringChar (IsLocalRing.ResidueField R) →
    ∀ (n : ℕ+) (X : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom X.X.hom],
      Smooth X.X.hom → HasGreenbergPointModel R n X

/-- The pair of all-level characteristic cases needed for the original theorem. -/
def GreenbergPointModelCasesStatement : Prop :=
  EqualCharacteristicGreenbergPointModelStatement.{u} ∧
    MixedCharacteristicGreenbergPointModelStatement.{u}

/-- The original theorem follows from its exhaustive characteristic cases. -/
theorem greenbergPointModel_of_characteristicCases
    (heq : EqualCharacteristicGreenbergPointModelStatement.{u})
    (hmix : MixedCharacteristicGreenbergPointModelStatement.{u}) :
    GreenbergPointModelStatement.{u} := by
  intro R _ _ _ _ n X _ hX
  by_cases hchar : ringChar R = ringChar (IsLocalRing.ResidueField R)
  · exact heq R hchar n X hX
  · exact hmix R hchar n X hX

/-- The case statements are exactly a decomposition of the original theorem. -/
theorem greenbergPointModel_iff_characteristicCases :
    GreenbergPointModelStatement.{u} ↔ GreenbergPointModelCasesStatement.{u} := by
  constructor
  · intro h
    constructor
    · intro R _ _ _ _ _ n X _ hX
      exact h R n X hX
    · intro R _ _ _ _ _ n X _ hX
      exact h R n X hX
  · rintro ⟨heq, hmix⟩
    exact greenbergPointModel_of_characteristicCases heq hmix

/-- At level one the model is the ordinary special fibre, using the canonical
isomorphism between the congruence quotient and the residue field. -/
def greenbergLevelOnePointsEquiv (R : Type u) [CommRing R] [IsLocalRing R]
    (X : GroupScheme (Spec (CommRingCat.of R))) :
    rationalPoints ((GroupScheme.baseChange (congruenceBaseMap R 1)).obj X) ≃*
      rationalPoints ((GroupScheme.baseChange (residueBaseMap R)).obj X) :=
  (baseChangeBasePointsEquiv (congruenceBaseMap R 1) X).trans
    ((X.points.mapIso (congruenceResidueTestIso R).op).groupIsoToMulEquiv.trans
      (baseChangeBasePointsEquiv (residueBaseMap R) X).symm)

/-- The canonical level-one comparison respects every original homomorphism. -/
theorem greenbergLevelOnePointsEquiv_naturality (R : Type u) [CommRing R] [IsLocalRing R]
    {Z X : GroupScheme (Spec (CommRingCat.of R))} (h : Z ⟶ X)
    (z : rationalPoints ((GroupScheme.baseChange (congruenceBaseMap R 1)).obj Z)) :
    greenbergLevelOnePointsEquiv R X
        (rationalPoints.map ((GroupScheme.baseChange (congruenceBaseMap R 1)).map h) z) =
      rationalPoints.map ((GroupScheme.baseChange (residueBaseMap R)).map h)
        (greenbergLevelOnePointsEquiv R Z z) := by
  exact baseChangePointRestriction_naturality (congruenceBaseMap R 1) (residueBaseMap R)
    (congruenceResidueBaseIso R).hom (congruenceResidueBaseIso_comm R) h z

/-- Every smooth affine group over a local ring has the required level-one model.
No valuation, perfectness or characteristic hypothesis is needed at this level. -/
theorem hasGreenbergPointModel_one (R : Type u) [CommRing R] [IsLocalRing R]
    (X : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom X.X.hom]
    (hX : Smooth X.X.hom) : HasGreenbergPointModel R 1 X := by
  have : Smooth X.X.hom := hX
  refine ⟨(GroupScheme.baseChange (residueBaseMap R)).obj X,
    greenbergLevelOnePointsEquiv R X, ?_, ?_, ?_⟩
  · change IsAffineHom (Limits.pullback.snd X.X.hom (residueBaseMap R))
    infer_instance
  · change Smooth (Limits.pullback.snd X.X.hom (residueBaseMap R))
    infer_instance
  · intro Z _ hZ h
    have : Smooth Z.X.hom := hZ
    refine ⟨(GroupScheme.baseChange (residueBaseMap R)).obj Z,
      greenbergLevelOnePointsEquiv R Z,
      (GroupScheme.baseChange (residueBaseMap R)).map h, ?_, ?_, ?_, ?_⟩
    · change IsAffineHom (Limits.pullback.snd Z.X.hom (residueBaseMap R))
      infer_instance
    · change Smooth (Limits.pullback.snd Z.X.hom (residueBaseMap R))
      infer_instance
    · exact greenbergLevelOnePointsEquiv_naturality R h
    · intro hconn
      have : GeometricallyConnected Z.X.hom := hconn
      change GeometricallyConnected (Limits.pullback.snd Z.X.hom (residueBaseMap R))
      infer_instance

end Langlands.GroupScheme.IntegralModel
