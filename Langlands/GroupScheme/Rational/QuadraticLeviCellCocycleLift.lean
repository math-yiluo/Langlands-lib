import Langlands.GroupScheme.Rational.QuadraticTorusCellCocycleLift

/-! # Quadratic cocycles in an opposite cell with an arbitrary middle subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace Dynamic

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left]
  {C : GroupScheme (Spec (CommRingCat.of k))}
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (c : C ⟶ G)

/-- The product `U(χ) × C × U(-χ) → G` as an actual morphism of schemes, for an arbitrary
subgroup `c : C ⟶ G` in the middle. -/
abbrev leviOppositeCell :
    (Affine.unipotentScheme χ).X ⊗ (C.X ⊗ (Affine.unipotentScheme (oppositeCocharacter χ)).X) ⟶
      G.X :=
  tripleCellMultiplication (Affine.unipotentHom χ) c (Affine.unipotentHom (oppositeCocharacter χ))

omit [IsAffineHom G.X.hom] in
/-- The cell map multiplies its three coordinates. -/
theorem lift_comp_leviOppositeCell {Z : Over (Spec (CommRingCat.of k))}
    (x : Z ⟶ (Affine.unipotentScheme χ).X) (y : Z ⟶ C.X)
    (z : Z ⟶ (Affine.unipotentScheme (oppositeCocharacter χ)).X) :
    lift x (lift y z) ≫ leviOppositeCell χ c =
      (x ≫ (Affine.unipotentHom χ).hom.hom) * (y ≫ c.hom.hom) *
        (z ≫ (Affine.unipotentHom (oppositeCocharacter χ)).hom.hom) := by
  rw [mul_assoc, lift_tripleCellMultiplication]

/-- The three-factor multiplication is an open immersion when the middle subgroup represents
the full dynamic centralizer. -/
theorem isOpenImmersion_leviOppositeCell [Smooth G.X.hom]
    (hc : (centralizer χ).IsRepresentedBy c) :
    IsOpenImmersion (leviOppositeCell χ c).left := by
  let χ' := oppositeCocharacter χ
  have hU : (unipotent (oppositeCocharacter χ')).IsRepresentedBy (Affine.unipotentHom χ) := by
    simpa only [χ', oppositeCocharacter_oppositeCocharacter] using
      Affine.isRepresentedBy_unipotentHom χ
  have hc' : (centralizer χ').IsRepresentedBy c := by
    rw [show centralizer χ' = centralizer χ from centralizer_oppositeCocharacter χ]
    exact hc
  exact isOpenImmersion_tripleCellMultiplication χ' hU hc' (Affine.isRepresentedBy_unipotentHom χ')

end Dynamic

namespace GaloisCocycle

open GaloisPointComparison

variable {F Q : Type u} [Field F] [Field Q] [Algebra F Q]
  {G C : GroupScheme (Spec (CommRingCat.of F))} {t : C ⟶ G}

local notation "b" => algebraBaseMap F Q
local notation "BC" => GroupScheme.baseChange b
local notation "GQ" => Functor.obj BC G
local notation "CQ" => Functor.obj BC C
local notation "tQ" => CategoryTheory.Functor.map BC t
local notation "pt" => Over.mk (𝟙 (Spec (CommRingCat.of Q)))

variable [IsAffine ((GroupScheme.baseChange (algebraBaseMap F Q)).obj G).X.left]
  (χ : (Gm (Spec (CommRingCat.of Q))).toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap F Q)).obj G)

/-- Coordinates in the actual cell `U(χ) × C_Q × U(-χ)` when Galois conjugation exchanges the
two unipotent factors: the positive and negative unipotent coordinates are both parametrized by
the coefficient points of `U(χ)`, the negative one through Galois conjugation, the resulting
three-coordinate product is injective, and it computes the cell map on rational points. -/
theorem exists_leviOppositeCell_coordinates (σ : Q ≃ₐ[F] Q)
    (hU : SubgroupFunctor.galoisTransport F Q G σ (Dynamic.unipotent χ) =
      Dynamic.unipotent (Dynamic.oppositeCocharacter χ))
    [Mono (Dynamic.leviOppositeCell χ tQ)] :
    ∃ (A₀ : Subgroup (cover F Q ⟶ G.X))
      (posEquiv : A₀ ≃ (pt ⟶ (Dynamic.Affine.unipotentScheme χ).X))
      (negEquiv : A₀ ≃
        (pt ⟶ (Dynamic.Affine.unipotentScheme (Dynamic.oppositeCocharacter χ)).X)),
      Function.Injective (fun z : A₀ × (cover F Q ⟶ C.X) × A₀ =>
        (z.1 : cover F Q ⟶ G.X) * (z.2.1 ≫ t.hom.hom) *
          GaloisPoint.conjugate F Q G σ z.2.2) ∧
      ∀ (x : pt ⟶ (Dynamic.Affine.unipotentScheme χ).X) (middle : pt ⟶ (CQ).X)
        (y : pt ⟶ (Dynamic.Affine.unipotentScheme (Dynamic.oppositeCocharacter χ)).X),
        baseChangeCoeffEquiv F Q G (lift x (lift middle y) ≫ Dynamic.leviOppositeCell χ tQ) =
          ((posEquiv.symm x : A₀) : cover F Q ⟶ G.X) *
            (baseChangeCoeffEquiv F Q C middle ≫ t.hom.hom) *
            GaloisPoint.conjugate F Q G σ (negEquiv.symm y : A₀) := by
  let e : (pt ⟶ (GQ).X) ≃* (cover F Q ⟶ G.X) := baseChangeCoeffEquiv F Q G
  let eC : (pt ⟶ (CQ).X) ≃* (cover F Q ⟶ C.X) := baseChangeCoeffEquiv F Q C
  let U := Dynamic.Affine.unipotentScheme χ
  let V := Dynamic.Affine.unipotentScheme (Dynamic.oppositeCocharacter χ)
  let i := Dynamic.Affine.unipotentHom χ
  let j := Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter χ)
  let m := Dynamic.leviOppositeCell χ tQ
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
      exact (Dynamic.Affine.isRepresentedBy_unipotentHom
        (Dynamic.oppositeCocharacter χ)).pointsEquiv_symm_comp _
    rw [hh]
    change baseChangeCoeffEquiv F Q G (rationalConjugate F Q G σ
      ((baseChangeCoeffEquiv F Q G).symm x.val)) = _
    rw [baseChangeCoeffEquiv_rationalConjugate, MulEquiv.apply_symm_apply]
  let fill (a : A₀ × (cover F Q ⟶ C.X) × A₀) : pt ⟶ U.X ⊗ ((CQ).X ⊗ V.X) :=
    lift (posEquiv a.1) (lift (eC.symm a.2.1) (negEquiv a.2.2))
  let product (a : A₀ × (cover F Q ⟶ C.X) × A₀) : cover F Q ⟶ G.X :=
    a.1.val * (a.2.1 ≫ t.hom.hom) * GaloisPoint.conjugate F Q G σ a.2.2
  have hmid (c : pt ⟶ (CQ).X) : e (c ≫ (tQ).hom.hom) = eC c ≫ t.hom.hom :=
    baseChangeBasePointsEquiv_comp b t c
  have hfill (a : A₀ × (cover F Q ⟶ C.X) × A₀) : e (fill a ≫ m) = product a := by
    dsimp only [fill, m, product]
    rw [Dynamic.lift_comp_leviOppositeCell, map_mul, map_mul, hpos, hneg, hmid,
      eC.apply_symm_apply]
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
      (eC.symm.injective (by simpa only [lift_fst] using congrArg (fun x => x ≫ fst _ _) h₂))
      (negEquiv.injective (by simpa only [lift_snd] using congrArg (fun x => x ≫ snd _ _) h₂)))
  refine ⟨A₀, posEquiv, negEquiv, hinj, fun x middle y => ?_⟩
  have ha : fill (posEquiv.symm x, eC middle, negEquiv.symm y) = lift x (lift middle y) := by
    simp only [fill, Equiv.apply_symm_apply, eC.symm_apply_apply]
  rw [← ha]
  exact hfill _

/-- A twist in the actual three-factor cell `U(χ) × C_Q × U(-χ)` lifts to a cocycle of the
middle subgroup whose coefficient value is exactly the middle coordinate of the cell point. -/
theorem exists_leviCocycle_of_leviOppositeCell
    [FiniteDimensional F Q] [IsGalois F Q]
    (hdeg : Module.finrank F Q = 2) (σ : Q ≃ₐ[F] Q) (hσ : σ ≠ 1)
    [Mono t.hom.hom]
    (hU : SubgroupFunctor.galoisTransport F Q G σ (Dynamic.unipotent χ) =
      Dynamic.unipotent (Dynamic.oppositeCocharacter χ))
    (hopen : IsOpenImmersion (Dynamic.leviOppositeCell χ tQ).left)
    (ξ : Cocycle G (cover F Q)) (f : cover F Q ⟶ G.X)
    (x : pt ⟶ (Dynamic.Affine.unipotentScheme χ).X) (middle : pt ⟶ (CQ).X)
    (y : pt ⟶ (Dynamic.Affine.unipotentScheme (Dynamic.oppositeCocharacter χ)).X)
    (hq : lift x (lift middle y) ≫ Dynamic.leviOppositeCell χ tQ =
      (baseChangeCoeffEquiv F Q G).symm (value (ξ.twist f) σ)) :
    ∃ δ : Cocycle C (cover F Q), (δ.map t).Cohomologous ξ ∧
      value δ σ = baseChangeCoeffEquiv F Q C middle := by
  let : IsOpenImmersion (Dynamic.leviOppositeCell χ tQ).left := hopen
  let : Mono (Dynamic.leviOppositeCell χ tQ) := Over.mono_of_mono_left _
  obtain ⟨A₀, posEquiv, negEquiv, hinj, hcell⟩ :=
    exists_leviOppositeCell_coordinates (t := t) χ σ hU
  have hv : value (ξ.twist f) σ = ((posEquiv.symm x : A₀) : cover F Q ⟶ G.X) *
      (baseChangeCoeffEquiv F Q C middle ≫ t.hom.hom) *
      GaloisPoint.conjugate F Q G σ (negEquiv.symm y : A₀) := by
    rw [← hcell, hq, MulEquiv.apply_symm_apply]
  obtain ⟨δ, hδ, hcoh⟩ := exists_torusCocycle_of_oppositeCell hdeg σ hσ t A₀ hinj ξ f
    (posEquiv.symm x) (negEquiv.symm y) (baseChangeCoeffEquiv F Q C middle) hv
  exact ⟨δ, hcoh, hδ⟩

end GaloisCocycle

end Langlands.GroupScheme
