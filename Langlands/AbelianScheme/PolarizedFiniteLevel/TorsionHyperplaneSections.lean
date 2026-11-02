import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicTorsionHyperplaneBoundStatement

/-! # Actual torsion sections in projective hyperplanes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry GroupScheme.Tate

variable {K : Type u} [Field K] [IsAlgClosed K]
  {A : AbelianScheme (Spec (CommRingCat.of K))} {g n m : ℕ}

/-- A supplied full level gives the actual cardinality of the torsion module
at every geometric point. -/
theorem FullLevel.card_fibreLevel {S : Scheme.{u}} {B : AbelianScheme S}
    (v : FullLevel B g n) (s : Spec (CommRingCat.of K) ⟶ S) :
    Nat.card (Level B.toGrp (Over.mk s) n) = n ^ (2 * g) := by
  rw [← Nat.card_congr (v.fibreCoordinates K s).toEquiv, Nat.card_fun,
    Nat.card_zmod, Nat.card_fin]

/-- Positive full level makes the actual geometric torsion module finite. -/
theorem FullLevel.finite_fibreLevel {S : Scheme.{u}} {B : AbelianScheme S}
    (v : FullLevel B g n) (s : Spec (CommRingCat.of K) ⟶ S) (hn : 0 < n) :
    Finite (Level B.toGrp (Over.mk s) n) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact Finite.of_equiv (Fin (2 * g) → ZMod n) (v.fibreCoordinates K s).toEquiv

/-- Actual torsion sections whose image belongs to the specified homogeneous
linear hyperplane, using the incidence convention of the published target. -/
def TorsionHyperplaneSections (i : A.X.left ⟶ ProjectiveSpace K m)
    (f : projectiveSpaceGrading K m 1) (n : ℕ) :=
  {x : Level A.toGrp (Over.mk (𝟙 (Spec (CommRingCat.of K)))) n //
    (f : ProjectiveCoordinateRing K m) ∈
      (i ((Additive.toMul x).val.left (IsLocalRing.closedPoint K))).asHomogeneousIdeal}

/-- The supplied full level restricts to coordinates for the actual hyperplane
sections; the incidence predicate is evaluated after the actual coordinate map. -/
def FullLevel.hyperplaneCoordinateEquiv (v : FullLevel A g n)
    (i : A.X.left ⟶ ProjectiveSpace K m) (f : projectiveSpaceGrading K m 1) :
    {c : Fin (2 * g) → ZMod n //
      (f : ProjectiveCoordinateRing K m) ∈
        (i ((Additive.toMul (v.fibreCoordinates K (𝟙 _) c)).val.left
          (IsLocalRing.closedPoint K))).asHomogeneousIdeal} ≃
      TorsionHyperplaneSections i f n := by
  unfold TorsionHyperplaneSections
  exact (v.fibreCoordinates K (𝟙 _)).toEquiv.subtypeEquivOfSubtype
    (p := fun x : Level A.toGrp (Over.mk (𝟙 (Spec (CommRingCat.of K)))) n =>
      (f : ProjectiveCoordinateRing K m) ∈
        (i ((Additive.toMul x).val.left
          (IsLocalRing.closedPoint K))).asHomogeneousIdeal)

/-- Every actual hyperplane count is at most the total torsion count. -/
theorem FullLevel.card_hyperplaneSections_le (v : FullLevel A g n)
    (i : A.X.left ⟶ ProjectiveSpace K m) (f : projectiveSpaceGrading K m 1)
    (hn : 0 < n) :
    Nat.card (TorsionHyperplaneSections i f n) ≤ n ^ (2 * g) := by
  let := v.finite_fibreLevel (𝟙 _) hn
  calc
    Nat.card (TorsionHyperplaneSections i f n) ≤
        Nat.card (Level A.toGrp (Over.mk (𝟙 (Spec (CommRingCat.of K)))) n) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = n ^ (2 * g) := v.card_fibreLevel (𝟙 _)

/-- The exact uniform constant follows from total cardinality in the range
where the square of the level is already at most that constant. -/
theorem FullLevel.card_hyperplaneSections_le_of_sq_le (v : FullLevel A g n)
    (i : A.X.left ⟶ ProjectiveSpace K m) (f : projectiveSpaceGrading K m 1)
    (d : ℕ) (hg : 0 < g) (hn : 0 < n)
    (hsq : n ^ 2 ≤ 6 ^ g * d * Nat.factorial g) :
    Nat.card (TorsionHyperplaneSections i f n) ≤
      6 ^ g * d * Nat.factorial g * n ^ (2 * g - 2) := by
  calc
    Nat.card (TorsionHyperplaneSections i f n) ≤ n ^ (2 * g) :=
      v.card_hyperplaneSections_le i f hn
    _ = n ^ 2 * n ^ (2 * g - 2) := by
      rw [← pow_add]
      congr 1
      omega
    _ ≤ 6 ^ g * d * Nat.factorial g * n ^ (2 * g - 2) :=
      Nat.mul_le_mul_right _ hsq

end Langlands.AbelianScheme.PolarizedFiniteLevel
