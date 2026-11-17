import Langlands.AlgebraicGeometry.Modules.FiniteProjectiveAffineLocalBases

/-! # Actual finite local frames of finite-projective associated sheaves -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Scheme.Modules

open Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.Modules

variable {R : CommRingCat.{u}} (C : ModuleCat.{u} R)
    [Module.Finite R C] [Module.Projective R C]

/-- The actual associated sheaf of every finite-projective base module has
finite local bases, with no global constant-rank premise. -/
theorem tilde_hasFiniteLocalBasis_of_finite_projective : HasFiniteLocalBasis (tilde C) := by
  let : Module.Finite R ((moduleSpecΓFunctor (R := R)).obj (tilde C)) :=
    Module.Finite.equiv (tilde.isoTop C).toLinearEquiv
  let : Module.Projective R ((moduleSpecΓFunctor (R := R)).obj (tilde C)) :=
    Module.Projective.of_equiv (tilde.isoTop C).toLinearEquiv
  choose n U hx e using DerivedSections.exists_freeNeighborhood_of_finite_projective (tilde C)
  refine ⟨freeNeighborhoodGenerators (tilde C) U hx
    (fun x => ULift.{u} (Fin (n x))) (fun x => (e x).some),
    freeNeighborhoodGenerators_isLocallyFreeData (tilde C) U hx
      (fun x => ULift.{u} (Fin (n x))) (fun x => (e x).some), ?_⟩
  constructor
  intro x
  change ((SheafOfModules.free.generatingSections
    (ULift.{u} (Fin (n x)))).ofEpi _).IsFiniteType
  exact ⟨inferInstanceAs (Finite (ULift.{u} (Fin (n x))))⟩

/-- Choose actual finite frames only from the proved finite-projective
associated-sheaf local-basis property. -/
def tildeFiniteProjectiveFrames : FiniteLocalFrames (tilde C) :=
  FiniteLocalFrames.choose (tilde_hasFiniteLocalBasis_of_finite_projective C)

end Langlands.Scheme.Modules
