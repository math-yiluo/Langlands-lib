import Langlands.GroupScheme.IdentityJetSheaf

/-! # Points of identity jets and their centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityJet

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- A point of `G` on a test scheme lies in the order-`n` identity jet when its
underlying scheme morphism factors through the jet's closed immersion. -/
def IsJetPoint (n : ℕ) {V : Over S} (x : V ⟶ G.X) : Prop :=
  ∃ y : V.left ⟶ scheme G n, y ≫ inclusion G n = x.left

/-- A point `g` of `G` on a test scheme `U` centralizes the order-`n` identity
jet: after every refinement `a : V ⟶ U`, the restricted point `a ≫ g` commutes
with every point of `G` on `V` lying in the jet. -/
def CentralizesJet (n : ℕ) {U : Over S} (g : U ⟶ G.X) : Prop :=
  ∀ (V : Over S) (a : V ⟶ U) (x : V ⟶ G.X), IsJetPoint G n x →
    (a ≫ g) * x = x * (a ≫ g)

end Langlands.GroupScheme.IdentityJet
