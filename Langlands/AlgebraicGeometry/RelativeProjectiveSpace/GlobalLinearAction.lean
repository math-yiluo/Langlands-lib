import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.LinearActionRestriction

/-! # Projective coordinate changes with global-function coefficients -/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry.RelativeProjectiveSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S T U : Scheme.{u}} (n : ℕ)

/-- Pull back every coefficient of an invertible coordinate map along a scheme morphism. -/
def coordinatePullback (f : T ⟶ S) :
    ((Fin (n + 1) → Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) → Γ(S, ⊤))) →*
      ((Fin (n + 1) → Γ(T, ⊤)) ≃ₗ[Γ(T, ⊤)] (Fin (n + 1) → Γ(T, ⊤))) :=
  ProjectiveSpace.coordinateBaseChange n f.appTop.hom

@[simp]
lemma coordinatePullback_coeff (f : T ⟶ S)
    (e : (Fin (n + 1) → Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) → Γ(S, ⊤)))
    (i j : Fin (n + 1)) :
    coordinatePullback n f e (Pi.single j 1) i = f.appTop (e (Pi.single j 1) i) :=
  ProjectiveSpace.coordinateBaseChange_coeff n f.appTop.hom e i j

@[simp]
lemma coordinatePullback_id
    (e : (Fin (n + 1) → Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) → Γ(S, ⊤))) :
    coordinatePullback n (𝟙 S) e = e := by
  simp [coordinatePullback]

lemma coordinatePullback_comp (f : U ⟶ T) (g : T ⟶ S)
    (e : (Fin (n + 1) → Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) → Γ(S, ⊤))) :
    coordinatePullback n (f ≫ g) e =
      coordinatePullback n f (coordinatePullback n g e) := by
  simp [coordinatePullback, ProjectiveSpace.coordinateBaseChange_comp]

/-- An invertible matrix of global functions acts on the actual relative projective scheme. -/
def globalLinearAction
    (e : (Fin (n + 1) → Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) → Γ(S, ⊤))) :
    RelativeProjectiveSpace S n ⟶ RelativeProjectiveSpace S n :=
  linearAction S.toSpecΓ e

@[reassoc (attr := simp)]
lemma globalLinearAction_toBase
    (e : (Fin (n + 1) → Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) → Γ(S, ⊤))) :
    globalLinearAction n e ≫ toBase S n = toBase S n :=
  linearAction_toBase S.toSpecΓ e

@[simp]
lemma globalLinearAction_refl :
    globalLinearAction n (LinearEquiv.refl Γ(S, ⊤) _) = 𝟙 _ :=
  linearAction_refl S.toSpecΓ

lemma globalLinearAction_comp
    (e f : (Fin (n + 1) → Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) → Γ(S, ⊤))) :
    globalLinearAction n e ≫ globalLinearAction n f = globalLinearAction n (e.trans f) :=
  linearAction_comp S.toSpecΓ e f

/-- The actual scheme isomorphism defined by an invertible global coordinate matrix. -/
def globalLinearActionIso
    (e : (Fin (n + 1) → Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) → Γ(S, ⊤))) :
    RelativeProjectiveSpace S n ≅ RelativeProjectiveSpace S n :=
  linearActionIso S.toSpecΓ e

@[simp]
lemma globalLinearActionIso_hom
    (e : (Fin (n + 1) → Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) → Γ(S, ⊤))) :
    (globalLinearActionIso n e).hom = globalLinearAction n e := rfl

@[simp]
lemma globalLinearActionIso_inv
    (e : (Fin (n + 1) → Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) → Γ(S, ⊤))) :
    (globalLinearActionIso n e).inv = globalLinearAction n e.symm := rfl

/-- Naturality includes the pullback of all matrix coefficients. -/
@[reassoc]
lemma map_globalLinearAction (f : T ⟶ S)
    (e : (Fin (n + 1) → Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) → Γ(S, ⊤))) :
    map n f ≫ globalLinearAction n e =
      globalLinearAction n (coordinatePullback n f e) ≫ map n f := by
  exact map_linearAction_baseChange S.toSpecΓ T.toSpecΓ f f.appTop.hom
    (Scheme.toSpecΓ_naturality f).symm e

@[simp]
lemma globalLinearAction_smulOfUnit (c : Γ(S, ⊤)ˣ) :
    globalLinearAction n (LinearEquiv.smulOfUnit c) = 𝟙 _ :=
  linearAction_smulOfUnit S.toSpecΓ c

end Langlands.AlgebraicGeometry.RelativeProjectiveSpace
