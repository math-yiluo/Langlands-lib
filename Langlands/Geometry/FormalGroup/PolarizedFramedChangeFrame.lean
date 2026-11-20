import Langlands.Geometry.FormalGroup.PolarizedFramedAffineFunctor
import Langlands.Geometry.FormalGroup.PolarizedRationalSectionIso

/-! # Changing the residue frame of the actual affine polarized class functor -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.RationalSection

open CategoryTheory TopologicalSpace _root_.AlgebraicGeometry

variable {O : Type u} [CommRing O]
variable {R S B : Type v} [CommRing R] [CommRing S] [CommRing B]
variable [Algebra O R] [Algebra O S] [Algebra O B]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}

private theorem baseChange_top_comp (φ : R →ₐ[O] S) (ψ : S →ₐ[O] B)
    {χ : R →ₐ[O] B} (h : ψ.comp φ = χ)
    (a : Iso ((M.map φ).map ψ) (M.map χ)) (b : Iso ((N.map φ).map ψ) (N.map χ))
    (ha : a.hom.toHom.toCoordinateMap = CoordinateMap.id)
    (hb : b.hom.toHom.toCoordinateMap = CoordinateMap.id) (z : RationalSection F M N ⊤) :
    transportIso a b ⊤ (baseChange ψ ⊤ (baseChange φ ⊤ z)) = baseChange χ ⊤ z := by
  subst χ
  have ea : a = mapCompIso M φ ψ := Iso.ext_hom (Hom.ext (CommLaw.Hom.ext ha))
  have eb : b = mapCompIso N φ ψ := Iso.ext_hom (Hom.ext (CommLaw.Hom.ext hb))
  subst a
  subst b
  have hz := baseChange_composite_transport φ ψ ⊤ z
  have e : eqToHom (coefficientOpenMap_comp_obj φ ψ ⊤) = 𝟙 (⊤ : Opens (PrimeSpectrum B)) :=
    Subsingleton.elim _ _
  rw [e] at hz
  exact hz.trans (restrict_id ⊤ _)

end Langlands.FormalGroup.ModuleLaw.RationalSection

namespace Langlands.FormalGroup.PolarizedFramedAffinePoint

open CategoryTheory ModuleLaw Langlands.Shimura

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

variable {prime : ℕ} [Fact prime.Prime]
variable {W : Type} [CommRing W] [Algebra ℤ_[prime] W] {π : W}
variable {A : Type w} [Ring A] [Algebra ℤ_[prime] A] {star : AlgebraInvolution ℤ_[prime] A}
variable {frame frame' frame'' : PolarizedOrderModule A star (ResidueRing W π) (prime : ℤ_[prime])}
variable {T U : Nilp.{0, 0} W π}
variable (X : PolarizedFramedAffinePoint prime π frame T)

/-- Replace the residue frame by precomposing the framing section with the
actual inverse of the specified rational similitude. -/
def changeFrame (e : PolarizedOrderModule.RationalSimilitudeIso frame frame' ⊤) :
    PolarizedFramedAffinePoint prime π frame' T where
  target := X.target
  rho := RationalSection.comp X.rho (e.sectionIso.baseChange (frameCoefficientMap prime π T)).inv
  commutes := (show RationalSection.IsOrderLinear _ _ X.rho from X.commutes).comp
    ((e.orderLinear.inverse e.sectionIso).baseChange (frameCoefficientMap prime π T))
  similitude := by
    obtain ⟨c, hc⟩ := X.similitude
    obtain ⟨d, _, hd⟩ := e.similitude
    exact ⟨d⁻¹ * c, hc.comp (hd.baseChange (frameCoefficientMap prime π T))⟩

/-- An integral isometry square remains a square after changing the common frame. -/
def Iso.changeFrame {X Y : PolarizedFramedAffinePoint prime π frame T}
    (f : Iso X Y) (e : PolarizedOrderModule.RationalSimilitudeIso frame frame' ⊤) :
    Iso (X.changeFrame e) (Y.changeFrame e) where
  targetIso := f.targetIso
  square := by
    let g := (e.sectionIso.baseChange (frameCoefficientMap prime π T)).inv
    exact (RationalSection.comp_assoc (X.reducedIsometrySection f.targetIso) X.rho g).symm.trans
      (congrArg (fun z => RationalSection.comp z g) f.square)

private theorem eq_of_target_rho {X Y : PolarizedFramedAffinePoint prime π frame T}
    (h : X.target = Y.target) (hr : HEq X.rho Y.rho) : X = Y := by
  cases X
  cases Y
  cases h
  cases hr
  rfl

/-- Changing the frame by its identity fixes the actual triple. -/
@[simp]
theorem changeFrame_refl :
    X.changeFrame (PolarizedOrderModule.RationalSimilitudeIso.refl frame ⊤) = X := by
  refine eq_of_target_rho ?_ ?_
  · rfl
  apply heq_of_eq
  let φ := frameCoefficientMap prime π T
  exact (congrArg (RationalSection.comp X.rho)
    (RationalSection.baseChange_id (F := ℚ_[prime]) (M := frame.law) φ ⊤)).trans
      (RationalSection.comp_id X.rho)

/-- Successive changes of frame precompose by the inverse of the composite. -/
theorem changeFrame_trans
    (e : PolarizedOrderModule.RationalSimilitudeIso frame frame' ⊤)
    (f : PolarizedOrderModule.RationalSimilitudeIso frame' frame'' ⊤) :
    (X.changeFrame e).changeFrame f = X.changeFrame (e.trans f) := by
  refine eq_of_target_rho ?_ ?_
  · rfl
  apply heq_of_eq
  let φ := frameCoefficientMap prime π T
  let g := (e.sectionIso.baseChange φ).inv
  let h := (f.sectionIso.baseChange φ).inv
  exact (RationalSection.comp_assoc X.rho g h).trans
    (congrArg (RationalSection.comp X.rho)
      (RationalSection.baseChange_comp φ e.sectionIso.inv f.sectionIso.inv).symm)

private theorem source_has_identity_series (j : T ⟶ U) :
    (sourceComparison (frame := frame) j).orderIso.toModuleIso.hom.toHom.toCoordinateMap =
      CoordinateMap.id := by
  change CoordinateMap.id.comp CoordinateMap.id = _
  exact CoordinateMap.id_comp _

/-- Change of frame commutes with actual coefficient extension on representatives. -/
theorem changeFrame_baseChange (e : PolarizedOrderModule.RationalSimilitudeIso frame frame' ⊤)
    (j : T ⟶ U) : (X.changeFrame e).baseChange j = (X.baseChange j).changeFrame e := by
  refine eq_of_target_rho ?_ ?_
  · rfl
  apply heq_of_eq
  let φ := frameCoefficientMap prime π T
  let ψ := Nilp.reducedScalarMap ℤ_[prime] j
  let a := (sourceComparison (frame := frame) j).orderIso.toModuleIso
  let a' := (sourceComparison (frame := frame') j).orderIso.toModuleIso
  let b := (X.targetComparison j).orderIso.toModuleIso
  let f := e.sectionIso.inv
  let z := RationalSection.baseChange φ ⊤ f
  have hPullback := RationalSection.baseChange_comp ψ X.rho z
  have hTransport := RationalSection.transportIso_comp a' a b
    (RationalSection.baseChange ψ ⊤ X.rho) (RationalSection.baseChange ψ ⊤ z)
  have hCompare := RationalSection.baseChange_top_comp φ ψ (frameCoefficientMap_natural j)
    a' a (source_has_identity_series j) (source_has_identity_series j) f
  exact (congrArg (RationalSection.transportIso a' b ⊤) hPullback).trans
    (hTransport.trans (congrArg
      (RationalSection.comp (RationalSection.transportIso a b ⊤
        (RationalSection.baseChange ψ ⊤ X.rho))) hCompare))

/-- Actual frame change on polarized framed isomorphism classes. -/
def IsomorphismClass.changeFrame (q : IsomorphismClass (frame := frame) (T := T))
    (e : PolarizedOrderModule.RationalSimilitudeIso frame frame' ⊤) :
    IsomorphismClass (frame := frame') (T := T) := by
  refine Quotient.map (fun X : PolarizedFramedAffinePoint prime π frame T => X.changeFrame e) ?_ q
  intro X Y h
  change Nonempty (Iso X Y) at h
  exact h.map (fun f => f.changeFrame e)

@[simp]
theorem IsomorphismClass.changeFrame_refl (q : IsomorphismClass (frame := frame) (T := T)) :
    q.changeFrame (PolarizedOrderModule.RationalSimilitudeIso.refl frame ⊤) = q := by
  induction q using Quotient.inductionOn with
  | h X => exact congrArg (Quotient.mk _) X.changeFrame_refl

theorem IsomorphismClass.changeFrame_trans (q : IsomorphismClass (frame := frame) (T := T))
    (e : PolarizedOrderModule.RationalSimilitudeIso frame frame' ⊤)
    (f : PolarizedOrderModule.RationalSimilitudeIso frame' frame'' ⊤) :
    (q.changeFrame e).changeFrame f = q.changeFrame (e.trans f) := by
  induction q using Quotient.inductionOn with
  | h X => exact congrArg (Quotient.mk _) (X.changeFrame_trans e f)

theorem IsomorphismClass.changeFrame_baseChange (q : IsomorphismClass (frame := frame) (T := T))
    (e : PolarizedOrderModule.RationalSimilitudeIso frame frame' ⊤) (j : T ⟶ U) :
    (q.changeFrame e).baseChange j = (q.baseChange j).changeFrame e := by
  induction q using Quotient.inductionOn with
  | h X => exact congrArg (Quotient.mk _) (X.changeFrame_baseChange e j)

/-- A rational similitude of fixed residue frames gives an actual natural
isomorphism of the polarized framed class functors. -/
def changeFrameNatIso (e : PolarizedOrderModule.RationalSimilitudeIso frame frame' ⊤) :
    classFunctor frame ≅ classFunctor frame' where
  hom := {
    app _ := ↾(fun q => q.changeFrame e)
    naturality _ _ j := by
      ext q
      exact (q.changeFrame_baseChange e j).symm }
  inv := {
    app _ := ↾(fun q => q.changeFrame e.symm)
    naturality _ _ j := by
      ext q
      exact (q.changeFrame_baseChange e.symm j).symm }
  hom_inv_id := by
    ext T q
    change (q.changeFrame e).changeFrame e.symm = q
    have h : e.trans e.symm = PolarizedOrderModule.RationalSimilitudeIso.refl frame ⊤ :=
      PolarizedOrderModule.RationalSimilitudeIso.ext e.sectionIso.inv_hom
    rw [q.changeFrame_trans, h, q.changeFrame_refl]
  inv_hom_id := by
    ext T q
    change (q.changeFrame e.symm).changeFrame e = q
    have h : e.symm.trans e = PolarizedOrderModule.RationalSimilitudeIso.refl frame' ⊤ :=
      PolarizedOrderModule.RationalSimilitudeIso.ext e.sectionIso.hom_inv
    rw [q.changeFrame_trans, h, q.changeFrame_refl]

end Langlands.FormalGroup.PolarizedFramedAffinePoint
