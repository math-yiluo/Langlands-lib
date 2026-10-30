import Langlands.Shimura.Coefficients.VaryingCoverLocalTrivialization
import Langlands.Shimura.Coefficients.HarrisEtaleCoefficients

/-! # Compatible Harris coefficient trivializations through a fixed exponent -/

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory AlgebraicGeometry Langlands.Global

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ) (U : CompactOpenLevel σ.FiniteAdelicPoints) (m : ℕ)
variable (X : Scheme.{u})
variable (Y : EquivariantDiagram (harrisCongruenceGroups ρ p U m) X.Etale)
variable (hY : ∀ n, IsFiniteGeometricTorsor X (Y.action n))

local notation "R" => HarrisCoefficientIntegers L p
local notation "M" => harrisCoefficientDiagram ρ p U m
local notation "J" => Scheme.smallEtaleTopology X

/-- The whole Harris coefficient diagram through exponent k, on the fixed
slice site over its source torsor. -/
def harrisEtaleLocalCoefficientSystem (k : ℕᵒᵖ) :
    Under k ⥤ Sheaf ((J).over (Y.obj.obj k)) (ModuleCat.{u} R) :=
  Under.forget k ⋙ harrisEtaleCoefficientSystem ρ p U m X Y hY ⋙
    (J).overPullback (ModuleCat.{u} R) (Y.obj.obj k)

/-- The original full-lattice coefficient reductions on that same slice site. -/
def harrisEtaleLocalConstantSystem (k : ℕᵒᵖ) :
    Under k ⥤ Sheaf ((J).over (Y.obj.obj k)) (ModuleCat.{u} R) :=
  etaleConstantSourceSystem X Y k M

/-- Invariant evaluation trivializes all lower Harris coefficient levels
compatibly with their original transition maps. -/
def harrisEtaleLocalCoefficientDiagramIso (k : ℕᵒᵖ) :
    harrisEtaleLocalCoefficientSystem ρ p U m X Y hY k ≅
      harrisEtaleLocalConstantSystem ρ p U m X Y k :=
  etaleAssociatedSourceTrivialization X Y hY k M

/-- The component at k to j evaluates at the actual map of torsor covers. -/
@[simp] theorem harrisEtaleLocalCoefficientDiagramIso_hom_app
    (k : ℕᵒᵖ) (i : Under k) :
    (harrisEtaleLocalCoefficientDiagramIso ρ p U m X Y hY k).hom.app i =
      etaleAssociatedEvaluationAlong X Y M i.right (Y.obj.map i.hom) := rfl

/-- The local diagram isomorphism carries each genuine sheaf transition to
the original whole-Harris coefficient reduction. -/
@[reassoc] theorem harrisEtaleLocalCoefficientDiagramIso_transition
    (k : ℕᵒᵖ) {i j : Under k} (f : i ⟶ j) :
    ((J).overPullback (ModuleCat.{u} R) (Y.obj.obj k)).map
        ((harrisEtaleCoefficientSystem ρ p U m X Y hY).map f.right) ≫
      (harrisEtaleLocalCoefficientDiagramIso ρ p U m X Y hY k).hom.app j =
    (harrisEtaleLocalCoefficientDiagramIso ρ p U m X Y hY k).hom.app i ≫
      ((J).overPullback (ModuleCat.{u} R) (Y.obj.obj k)).map
        ((constantSheaf J (ModuleCat.{u} R)).map ((M).obj.map f.right)) :=
  (harrisEtaleLocalCoefficientDiagramIso ρ p U m X Y hY k).hom.naturality f

/-- At the identity arrow, the diagram isomorphism recovers the previously
constructed single-exponent invariant-evaluation trivialization. -/
@[simp] theorem harrisEtaleLocalCoefficientDiagramIso_identity_hom (k : ℕᵒᵖ) :
    (harrisEtaleLocalCoefficientDiagramIso ρ p U m X Y hY k).hom.app
        (Under.mk (𝟙 k)) =
      (harrisEtaleCoefficientTrivialization ρ p U m X Y hY k).hom := by
  change associatedEvaluationAlong J (Y.action k) (Y.obj.map (𝟙 k)) _ = _
  rw [Y.obj.map_id]
  exact associatedEvaluationAlong_id J (Y.action k) _

end Langlands.Shimura.Coefficients
