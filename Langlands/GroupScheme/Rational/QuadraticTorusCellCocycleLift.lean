import Langlands.GroupScheme.Rational.QuadraticOppositeTorusCell
import Langlands.GroupScheme.Rational.QuadraticCocycleOppositeCell
import Langlands.GroupScheme.Rational.RootSubgroupGaloisTransport

/-! # Scheme cocycle lifting in the quadratic opposite torus cell -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisCocycle

open GaloisPointComparison

set_option maxRecDepth 6000
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 120000
set_option backward.isDefEq.respectTransparency false

variable {F Q : Type u} [Field F] [Field Q] [Algebra F Q]
  [FiniteDimensional F Q] [IsGalois F Q]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {t : T.toGrp ⟶ G}

local notation "b" => algebraBaseMap F Q
local notation "C" => GroupScheme.baseChange b
local notation "GQ" => Functor.obj C G
local notation "TQ" => Functor.obj (CommGroupScheme.baseChange b) T
local notation "tQ" => CategoryTheory.Functor.map C t
local notation "pt" => Over.mk (𝟙 (Spec (CommRingCat.of Q)))

variable [IsAffine ((GroupScheme.baseChange (algebraBaseMap F Q)).obj G).X.left]
  (χ : (Gm (Spec (CommRingCat.of Q))).toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap F Q)).obj G)

/-- A twist in the actual three-factor cell lifts to a torus cocycle whose
coefficient value is exactly the middle coordinate of the cell point. -/
theorem exists_torusCocycle_of_torusOppositeCell
    (hdeg : Module.finrank F Q = 2) (σ : Q ≃ₐ[F] Q) (hσ : σ ≠ 1)
    [Mono t.hom.hom]
    (hU : SubgroupFunctor.galoisTransport F Q G σ (Dynamic.unipotent χ) =
      Dynamic.unipotent (Dynamic.oppositeCocharacter χ))
    (hopen : IsOpenImmersion (Dynamic.torusOppositeCell (T := (CommGroupScheme.baseChange b).obj T)
      χ tQ).left)
    (ξ : Cocycle G (cover F Q)) (f : cover F Q ⟶ G.X)
    (x : rationalPoints (Dynamic.Affine.unipotentScheme χ))
    (middle : rationalPoints (TQ).toGrp)
    (y : rationalPoints (Dynamic.Affine.unipotentScheme (Dynamic.oppositeCocharacter χ)))
    (hq : lift x (lift middle y) ≫ Dynamic.torusOppositeCell (T := (TQ)) χ tQ =
      (baseChangeCoeffEquiv F Q G).symm (value (ξ.twist f) σ)) :
    ∃ δ : Cocycle T.toGrp (cover F Q), (δ.map t).Cohomologous ξ ∧
      value δ σ = baseChangeCoeffEquiv F Q T.toGrp middle := by
  let e : (pt ⟶ (GQ).X) ≃* (cover F Q ⟶ G.X) := baseChangeCoeffEquiv F Q G
  let eT : (pt ⟶ (TQ).X) ≃* (cover F Q ⟶ T.X) := baseChangeCoeffEquiv F Q T.toGrp
  let U := Dynamic.Affine.unipotentScheme χ
  let V := Dynamic.Affine.unipotentScheme (Dynamic.oppositeCocharacter χ)
  let i := Dynamic.Affine.unipotentHom χ
  let j := Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter χ)
  let m := Dynamic.torusOppositeCell (T := (CommGroupScheme.baseChange b).obj T) χ tQ
  let : IsOpenImmersion m.left := hopen
  let : Mono m := Over.mono_of_mono_left _
  let A := (Dynamic.unipotent χ).carrier pt
  let A₀ := A.comap e.symm.toMonoidHom
  let e₀ : A₀ ≃ A := e.symm.toEquiv.subtypeEquiv (fun _ => Iff.rfl)
  let posEquiv : A₀ ≃ (pt ⟶ U.X) :=
    e₀.trans ((Dynamic.Affine.isRepresentedBy_unipotentHom χ).pointsEquiv pt).symm.toEquiv
  let E := galoisTransportRationalEquiv F Q G σ (Dynamic.unipotent χ)
  let negEquiv : A₀ ≃ (pt ⟶ V.X) :=
    e₀.trans (E.toEquiv.trans ((Equiv.subtypeEquivRight (fun x =>
      show x ∈ (SubgroupFunctor.galoisTransport F Q G σ (Dynamic.unipotent χ)).carrier pt ↔
        x ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).carrier pt from by rw [hU])).trans
      ((Dynamic.Affine.isRepresentedBy_unipotentHom _).pointsEquiv pt).symm.toEquiv))
  have hpos (x : A₀) : e (posEquiv x ≫ i.hom.hom) = x := by
    have h := (Dynamic.Affine.isRepresentedBy_unipotentHom χ).pointsEquiv_symm_comp (e₀ x)
    change e (posEquiv x ≫ i.hom.hom) = x.val
    exact (congrArg e h).trans (e.apply_symm_apply x.val)
  have hneg (x : A₀) : e (negEquiv x ≫ j.hom.hom) = GaloisPoint.conjugate F Q G σ x := by
    have hh : negEquiv x ≫ j.hom.hom = rationalConjugate F Q G σ (e.symm x.val) := by
      exact (Dynamic.Affine.isRepresentedBy_unipotentHom (Dynamic.oppositeCocharacter χ)).pointsEquiv_symm_comp _
    rw [hh]
    change baseChangeCoeffEquiv F Q G (rationalConjugate F Q G σ ((baseChangeCoeffEquiv F Q G).symm x.val)) = _
    rw [baseChangeCoeffEquiv_rationalConjugate, MulEquiv.apply_symm_apply]
  let fill (a : A₀ × (cover F Q ⟶ T.X) × A₀) : pt ⟶ U.X ⊗ ((TQ).X ⊗ V.X) :=
    lift (posEquiv a.1) (lift (eT.symm a.2.1) (negEquiv a.2.2))
  let product (a : A₀ × (cover F Q ⟶ T.X) × A₀) : cover F Q ⟶ G.X :=
    a.1.val * (a.2.1 ≫ t.hom.hom) * GaloisPoint.conjugate F Q G σ a.2.2
  have hfill (a : A₀ × (cover F Q ⟶ T.X) × A₀) : e (fill a ≫ m) = product a := by
    dsimp only [fill, m, product]
    rw [Dynamic.lift_comp_torusOppositeCell, map_mul, map_mul, hpos, hneg]
    have ht' : e (eT.symm a.2.1 ≫ (tQ).hom.hom) = a.2.1 ≫ t.hom.hom :=
      (baseChangeBasePointsEquiv_comp b t (eT.symm a.2.1)).trans
        (congrArg (fun r : cover F Q ⟶ T.X => r ≫ t.hom.hom) (eT.apply_symm_apply _))
    rw [ht']
  have hinj : Function.Injective product := by
    intro a c h
    have hc : fill a = fill c := (cancel_mono m).mp (e.injective
      ((hfill a).trans (h.trans (hfill c).symm)))
    have h₁ := congrArg (fun x => x ≫ fst _ _) hc
    have h₂ := congrArg (fun x => x ≫ snd _ _) hc
    dsimp only [fill] at h₁ h₂
    rw [lift_fst, lift_fst] at h₁
    rw [lift_snd, lift_snd] at h₂
    exact Prod.ext (posEquiv.injective h₁) (Prod.ext
      (eT.symm.injective (by simpa only [lift_fst] using congrArg (fun x => x ≫ fst _ _) h₂))
      (negEquiv.injective (by simpa only [lift_snd] using congrArg (fun x => x ≫ snd _ _) h₂)))
  let a := (posEquiv.symm x, eT middle, negEquiv.symm y)
  have ha : fill a = lift x (lift middle y) := by
    simp only [fill, a, Equiv.apply_symm_apply, eT.symm_apply_apply]
  have hv : value (ξ.twist f) σ = product a :=
    (e.apply_symm_apply _).symm.trans ((congrArg e hq).symm.trans ((congrArg (fun x => e (x ≫ m))
      ha).symm.trans (hfill a)))
  obtain ⟨δ, hδ, hcoh⟩ := exists_torusCocycle_of_oppositeCell hdeg σ hσ t A₀ hinj ξ f a.1 a.2.2
    a.2.1 hv
  exact ⟨δ, hcoh, hδ⟩

end Langlands.GroupScheme.GaloisCocycle

