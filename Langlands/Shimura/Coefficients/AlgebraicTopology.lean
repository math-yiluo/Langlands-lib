import Langlands.Shimura.Coefficients.Algebraic

noncomputable section

universe u v w

namespace Langlands.Shimura.AlgebraInvolution

open scoped TensorProduct

section Tower

variable {A : Type v} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A)
variable (L : Type u) [Field L] [Algebra ℚ L]
variable (S : Type u) [CommRing S] [Algebra ℚ S] [Algebra L S]
variable [TopologicalSpace S]

/-- The actual coefficient-tower map is continuous in the tensor module topologies. -/
theorem continuous_towerMap :
    letI : TopologicalSpace (S ⊗[ℚ] A) := moduleTopology S (S ⊗[ℚ] A)
    letI : TopologicalSpace (S ⊗[L] (L ⊗[ℚ] A)) :=
      moduleTopology S (S ⊗[L] (L ⊗[ℚ] A))
    Continuous (towerMap (A := A) L S) := by
  let : TopologicalSpace (S ⊗[ℚ] A) := moduleTopology S (S ⊗[ℚ] A)
  let : TopologicalSpace (S ⊗[L] (L ⊗[ℚ] A)) :=
    moduleTopology S (S ⊗[L] (L ⊗[ℚ] A))
  let : ContinuousAdd (S ⊗[L] (L ⊗[ℚ] A)) := IsModuleTopology.toContinuousAdd S _
  exact IsModuleTopology.continuous_of_linearMap (towerMap L S).toLinearMap

/-- The point map through the actual tensor tower preserves the canonical topology. -/
theorem continuous_towerPoints : Continuous (σ.towerPoints L S) := by
  let : TopologicalSpace (S ⊗[ℚ] A) := moduleTopology S (S ⊗[ℚ] A)
  let : TopologicalSpace (S ⊗[L] (L ⊗[ℚ] A)) :=
    moduleTopology S (S ⊗[L] (L ⊗[ℚ] A))
  exact (((continuous_towerMap L S).units_map (towerMap L S).toMonoidHom).comp
    (continuous_fst.comp continuous_subtype_val)).prodMk
    (continuous_snd.comp continuous_subtype_val) |>.subtype_mk _

end Tower

section Place

open Langlands.Global

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable (σ : AlgebraInvolution ℚ A)
variable {L : Type u} [Field L] [NumberField L]
variable (p : FinitePlace ℚ) (l : FinitePlace L) [l.asIdeal.LiesOver p.asIdeal]

/-- The actual continuous point map from finite adeles to the coefficient completion,
including the change from the rational group to its coefficient-field base change. -/
def coefficientPlaceMap : σ.FiniteAdelicPoints →ₜ* (σ.baseChange L).Points (FiniteCompletion L l) where
  toMonoidHom := (σ.towerPoints L (FiniteCompletion L l)).comp
    ((σ.pointsMap (AdelicFunctoriality.FiniteExtension.completionMap p l).toRatAlgHom).comp
      (σ.finiteLocalMap p).toMonoidHom)
  continuous_toFun := by
    have hcompletion :
        Continuous (AdelicFunctoriality.FiniteExtension.completionMap p l) :=
      AdelicFunctoriality.FiniteExtension.continuous_completionMap p l
    have hpoints :
        Continuous (σ.pointsMap
          (AdelicFunctoriality.FiniteExtension.completionMap p l).toRatAlgHom) :=
      σ.continuous_pointsMap
        (S := FiniteCompletion ℚ p) (T := FiniteCompletion L l)
        (AdelicFunctoriality.FiniteExtension.completionMap p l).toRatAlgHom
        hcompletion
    have htower :
        Continuous (σ.towerPoints L (FiniteCompletion L l)) :=
      continuous_towerPoints σ L (FiniteCompletion L l)
    have hlocal : Continuous (σ.finiteLocalMap p) :=
      (σ.finiteLocalMap p).continuous
    exact htower.comp (hpoints.comp hlocal)

namespace AlgebraicRepresentation

variable {σ} {W : Type u} [AddCommGroup W] [Module L W]
variable (ρ : (σ.baseChange L).AlgebraicRepresentation W)

/-- The published local action is the algebraic action composed with the continuous point map. -/
theorem placeAction_eq_comp_coefficientPlaceMap :
    ρ.placeAction p l = (ρ.act (FiniteCompletion L l)).comp
      (coefficientPlaceMap σ p l).toMonoidHom := rfl

/-- Continuous orbit maps of the algebraic local action give continuous adelic orbit maps. -/
theorem continuous_placeAction_orbit
    (hρ : letI : TopologicalSpace (FiniteCompletion L l ⊗[L] W) :=
        moduleTopology (FiniteCompletion L l) (FiniteCompletion L l ⊗[L] W)
      ∀ x : FiniteCompletion L l ⊗[L] W,
        Continuous (fun g : (σ.baseChange L).Points (FiniteCompletion L l) =>
          ρ.act (FiniteCompletion L l) g x)) :
    letI : TopologicalSpace (FiniteCompletion L l ⊗[L] W) :=
      moduleTopology (FiniteCompletion L l) (FiniteCompletion L l ⊗[L] W)
    ∀ x : FiniteCompletion L l ⊗[L] W, Continuous (fun g : σ.FiniteAdelicPoints =>
      ρ.placeAction p l g x) := by
  let : TopologicalSpace (FiniteCompletion L l ⊗[L] W) :=
    moduleTopology (FiniteCompletion L l) (FiniteCompletion L l ⊗[L] W)
  intro x
  exact (hρ x).comp (coefficientPlaceMap σ p l).continuous

end AlgebraicRepresentation
end Place

end Langlands.Shimura.AlgebraInvolution
