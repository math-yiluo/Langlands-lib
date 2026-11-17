import Langlands.GroupScheme.Reductive.PowerCommutatorTransport

/-! # Commutator transport with separate powers on the root terms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.LocalSplitCell

/-- Data for transforming one actual commutator term by a specified
additive-line endomorphism, with new coefficient and exponents. -/
structure CommTermPowerData (R : Type u) [CommRing R] where
  powerMap : Ga R ⟶ Ga R
  exponent : ℕ
  coefficient : R
  leftDegree : ℕ
  rightDegree : ℕ

namespace CommTermPowerData

variable {R : Type u} [CommRing R]
    {G : GroupScheme (Spec (CommRingCat.of R))}

/-- The actual transformed commutator term. -/
def applyTo (D : CommTermPowerData R) (t : CommTerm R G) : CommTerm R G :=
  (D.powerMap ≫ t.1, D.coefficient, D.leftDegree, D.rightDegree)

/-- Exact coefficient and exponent balances that make the transformed
term equal to the old term evaluated on separately powered arguments. -/
structure IsBalanced (D : CommTermPowerData R)
    (leftPower rightPower : ℕ) (t : CommTerm R G) : Prop where
  pointFormula : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
    rootPoint D.powerMap Z x =
      VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ D.exponent)
  coefficient_power : D.coefficient ^ D.exponent = t.2.1
  left_balance : D.leftDegree * D.exponent = leftPower * t.2.2.1
  right_balance : D.rightDegree * D.exponent = rightPower * t.2.2.2

/-- A balanced term has the required equality of actual points on every
scheme test. -/
theorem termPoint_applyTo (D : CommTermPowerData R) {a b : ℕ}
    (t : CommTerm R G) (hD : D.IsBalanced a b t)
    (Z : Over (Spec (CommRingCat.of R))) (x y : Γ(Z.left, ⊤)) :
    termPoint Z x y (D.applyTo t) =
      termPoint Z (x ^ a) (y ^ b) t := by
  unfold termPoint applyTo
  rw [rootPoint_precompose_power (F := D.powerMap) (q := D.exponent) hD.pointFormula]
  congr 1
  simp only [mul_pow, ← map_pow, ← pow_mul,
    hD.coefficient_power, hD.left_balance, hD.right_balance]

end CommTermPowerData

variable {R : Type u} [CommRing R]
    {G : GroupScheme (Spec (CommRingCat.of R))}

/-- Apply the specified transformation to each annotated commutator
term, preserving the list order. -/
def powerCommTermsWith (L : List (CommTerm R G × CommTermPowerData R)) :
    List (CommTerm R G) :=
  L.map fun t => t.2.applyTo t.1

/-- A literal commutator formula transfers through separate input powers
and term powers when their coefficient and exponent balances hold. -/
theorem CommRel.precompose_balanced_powers
    {w₁ w₂ : Ga R ⟶ G}
    {L : List (CommTerm R G × CommTermPowerData R)}
    (h : CommRel w₁ w₂ (L.map Prod.fst))
    (F₁ F₂ : Ga R ⟶ Ga R) (a b : ℕ)
    (hF₁ : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint F₁ Z x = VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ a))
    (hF₂ : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint F₂ Z x = VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ b))
    (hL : ∀ t ∈ L, t.2.IsBalanced a b t.1) :
    CommRel (F₁ ≫ w₁) (F₂ ≫ w₂) (powerCommTermsWith L) := by
  intro B _ s x y
  have h₁ (z : Γ((Over.mk s).left, ⊤)) :
      rootPoint (F₁ ≫ w₁) (Over.mk s) z = rootPoint w₁ (Over.mk s) (z ^ a) :=
    rootPoint_precompose_power (G := G) hF₁ w₁ (Over.mk s) z
  have h₂ (z : Γ((Over.mk s).left, ⊤)) :
      rootPoint (F₂ ≫ w₂) (Over.mk s) z = rootPoint w₂ (Over.mk s) (z ^ b) :=
    rootPoint_precompose_power (G := G) hF₂ w₂ (Over.mk s) z
  simp only [h₁, h₂]
  rw [h B s (x ^ a) (y ^ b)]
  simp only [powerCommTermsWith, List.map_map]
  apply congrArg (fun l : List (Over.mk s ⟶ G.X) => l.prod)
  exact List.map_congr_left fun t ht =>
    (t.2.termPoint_applyTo t.1 (hL t ht) (Over.mk s) x y).symm

end Langlands.GroupScheme.LocalSplitCell
