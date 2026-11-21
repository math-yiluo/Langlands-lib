import Langlands.Geometry.FormalGroup.PDivisibleCartierDual
import Langlands.Geometry.FormalGroup.PDivisibleGroupProduct
import Langlands.GroupScheme.Cartier.SplitPairingPerfectness

/-! # The split p-divisible group with its tautological polarization -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.PDivisibleGroup

open GroupScheme GroupScheme.Cartier GroupScheme.Cartier.FiniteDual

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime]

/-- A principal polarization in terms of the perfect alternating pairings of all actual
finite levels, with inclusions and transfers adjoint to one another. -/
structure PrincipalPolarization (G : PDivisibleGroup R p) where
  perfect : ∀ n : ℕ, additivePoints (G.inclusions.obj n).toGrp ≅ characters (G.inclusions.obj n)
  alternating : ∀ (n : ℕ) (T : Over (Spec R)) (x : T ⟶ (G.inclusions.obj n).X),
    characterEvaluation ((perfect n).hom.app (op T) (Additive.ofMul x)) x = 1
  adjoint : ∀ {m n : ℕ} (i : m ⟶ n) (T : Over (Spec R))
      (x : T ⟶ (G.inclusions.obj m).X) (y : T ⟶ (G.inclusions.obj n).X),
    characterEvaluation ((perfect n).hom.app (op T)
      (Additive.ofMul (x ≫ (G.inclusions.map i).toMul.hom.hom))) y =
    characterEvaluation ((perfect m).hom.app (op T) (Additive.ofMul x))
      (y ≫ (G.transfer i).toMul.hom.hom)

variable (G : PDivisibleGroup R p)

local instance splitLevelFinite (n : ℕ) : IsFinite (G.inclusions.obj n).X.hom :=
  (G.finiteLocallyFree n).1
local instance splitLevelFlat (n : ℕ) : Flat (G.inclusions.obj n).X.hom :=
  (G.finiteLocallyFree n).2.1
local instance splitLevelFinitePresentation (n : ℕ) :
    LocallyOfFinitePresentation (G.inclusions.obj n).X.hom := (G.finiteLocallyFree n).2.2

/-- The p-divisible group whose two factors are the original group and its actual Cartier dual. -/
def splitWithDual (hExact : FiniteCartierDualExactnessStatement.{u}) : PDivisibleGroup R p :=
  G.prod (G.dual hExact)

theorem splitWithDual_inclusion (hExact : FiniteCartierDualExactnessStatement.{u}) {m n : ℕ} (i : m ⟶ n) :
    (G.splitWithDual hExact).inclusions.map i =
      productWithDualMap (G.inclusions.map i) (schemeDualMap (G.transfer i)) :=
  rfl

theorem splitWithDual_transfer (hExact : FiniteCartierDualExactnessStatement.{u}) {m n : ℕ} (i : m ⟶ n) :
    (G.splitWithDual hExact).transfer i =
      productWithDualMap (G.transfer i) (schemeDualMap (G.inclusions.map i)) :=
  rfl

private theorem splitLevels_adjoint {H J : CommGroupScheme (Spec R)}
    [IsFinite H.X.hom] [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom]
    [IsFinite J.X.hom] [Flat J.X.hom] [LocallyOfFinitePresentation J.X.hom]
    (f : H ⟶ J) (g : J ⟶ H) (T : Over (Spec R))
    (x : T ⟶ (CommGroupScheme.prod H (schemeDual H)).X)
    (y : T ⟶ (CommGroupScheme.prod J (schemeDual J)).X) :
    let a := CommGroupScheme.prodMap f (schemeDualMap g)
    let b := CommGroupScheme.prodMap g (schemeDualMap f)
    @characterEvaluation _ (CommGroupScheme.prod J (schemeDual J)) T
      ((splitPairingPerfect J).hom.app (op T) (Additive.ofMul (x ≫ a.toMul.hom.hom))) y =
    @characterEvaluation _ (CommGroupScheme.prod H (schemeDual H)) T
      ((splitPairingPerfect H).hom.app (op T) (Additive.ofMul x)) (y ≫ b.toMul.hom.hom) := by
  let a := CommGroupScheme.prodMap f (schemeDualMap g)
  let b := CommGroupScheme.prodMap g (schemeDualMap f)
  have h₁ := splitPairingCharacters_evaluation J T (x ≫ a.toMul.hom.hom) y
  have h₂ := productWithDualPairing_adjoint (G := H) (H := J) f g T x y
  have h₃ := splitPairingCharacters_evaluation H T x (y ≫ b.toMul.hom.hom)
  exact h₁.trans (h₂.trans h₃.symm)

/-- The split p-divisible group has the tautological principal polarization. -/
def splitPrincipalPolarization (hExact : FiniteCartierDualExactnessStatement.{u}) :
    PrincipalPolarization (G.splitWithDual hExact) where
  perfect n := splitPairingPerfect (G.inclusions.obj n)
  alternating n T x := by
    let H := G.inclusions.obj n
    exact (splitPairingCharacters_evaluation H T x x).trans (productWithDualPairing_self H T x)
  adjoint {m n} i T x y := by
    dsimp only [splitWithDual, prod, dual, dualInclusions] at x y ⊢
    have h := splitLevels_adjoint (H := G.inclusions.obj m) (J := G.inclusions.obj n)
      (G.inclusions.map i) (G.transfer i) T x y
    dsimp only at h
    with_reducible exact h

end Langlands.PDivisibleGroup
