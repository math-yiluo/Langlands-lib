/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrderedCechModuleCoordinates
public import Mathlib.GroupTheory.Perm.Sign
import WeilConjectures.AlgebraicGeometry.OrderedCechDegreewiseProjectionDifferential

/-! # Signed projection of module Čech cochains

Source: Stacks Project, Tags 01FK and 01FM.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- All-tuple coordinate, with the actual extension transport.
Source: Stacks 01FK. (blueprint: lem-pc-ordered-cech-module-projection-lift). -/
noncomputable def orderedCechFullCoordinate {X' T' : Scheme.{u}} (f' : X' ⟶ T')
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).X p)
    (p : ℕ) (B : T'.Opens) (y : Fin (p + 1) → ULift.{u} (Fin r))
    (s : Γ(((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat).X (p : ℤ), B)) :
    Γ(M, (∏ᶜ fun l ↦ W₀ (y l)) ⨯ f' ⁻¹ᵁ B) :=
  (((e p).hom ≫ Pi.π (fun z : Fin (p + 1) → ULift.{u} (Fin r) ↦
    ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat).obj
        (op (∏ᶜ fun l ↦ W₀ (z l)))) y).app (op (f' ⁻¹ᵁ B)))
    (((((Modules.pushforward f').mapHomologicalComplex _).obj D).extendXIso
      ComplexShape.embeddingUpNat (i := p) rfl).hom.app B s)

/-- Restrict an ordered coordinate back to an arbitrary permuted full tuple.
Source: Stacks 01FK. (blueprint: lem-pc-ordered-cech-module-projection-lift). -/
noncomputable def orderedCechProjectionOpenMap {X : Scheme.{u}} {r p : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (B : X.Opens)
    (y : Fin (p + 1) → ULift.{u} (Fin r)) (σ : Equiv.Perm (Fin (p + 1)))
    (h : StrictMono (fun l ↦ (y (σ l)).down)) :
    (∏ᶜ fun l ↦ W (y l)) ⨯ B ⟶
      alternatingCechIntersection (fun i ↦ W ⟨i⟩) (OrderEmbedding.ofStrictMono _ h) ⊓ B :=
  homOfLE (le_inf (le_iInf fun l ↦
    (prod.fst ≫ Pi.π (fun k ↦ W (y k)) (σ l)).le) prod.snd.le)

/-- The finite signed extension formula characterizes the projection completely.
Source: Stacks 01FK and 01FM.
(blueprint: lem-pc-ordered-cech-module-projection-lift). -/
def IsOrderedCechModuleProjection {X' T' : Scheme.{u}} (f' : X' ⟶ T')
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).X p)
    (P : ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat) ⟶
      ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat)) : Prop :=
  ∀ (p : ℕ) (B : T'.Opens) (s : Γ(((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat).X (p : ℤ), B))
    (y : Fin (p + 1) → ULift.{u} (Fin r)),
    orderedCechFullCoordinate f' M W₀ D e p B y ((P.f (p : ℤ)).app B s) =
      ∑ σ : Equiv.Perm (Fin (p + 1)),
        if h : StrictMono (fun l ↦ (y (σ l)).down) then
          (Equiv.Perm.sign σ : ℤ) •
            M.presheaf.map (orderedCechProjectionOpenMap W₀ (f' ⁻¹ᵁ B) y σ h).op
              (orderedCechModuleCoordinate f' M W₀ D e p B
                (OrderEmbedding.ofStrictMono _ h) s)
        else 0

/-- Signed extension lifts to a cochain endomorphism of module sheaves.
Source: Stacks 01FK, signed extension; 01FM, the map cπ.
(blueprint: lem-pc-ordered-cech-module-projection-lift).

Proof: Obtain the degreewise module maps and their coordinate formula from
orderedCech_degreewise_projection_exists, whose construction uses the actual finite
signed sum and hlinear. Apply orderedCech_degreewise_projection_comm with hd and
assemble a morphism of D using CochainComplex.ofHom. Push it forward and extend by
zero with HomologicalComplex.extendMap. In a natural degree, extendMap_f expresses
its component using extendXIso, the pushed-forward degreewise map, and the inverse
of extendXIso. Composing with the coordinate's extendXIso cancels that inverse.
The degreewise formula on the inverse-image open is definitionally the required
signed formula. The extension functor supplies all negative components and boundary
equations. Empty families and degrees exceeding r have zero projection by the
strict-increase filter. -/
theorem orderedCech_module_projection_exists {X' T' : Scheme.{u}} (f' : X' ⟶ T')
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).X p)
    (hd : ∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor W₀).obj
            ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).d p (p + 1))
    (hlinear : ∀ (p : ℕ) (y : Fin (p + 1) → ULift.{u} (Fin r)) (B : X'.Opens),
        let c : Γ(D.X p, B) → Γ(M, (∏ᶜ fun l ↦ W₀ (y l)) ⨯ B) :=
          fun s ↦ ((e p).hom ≫ Pi.π (fun y : Fin (p + 1) → ULift.{u} (Fin r) ↦
            ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj
                M.presheafModuleCat).obj
                (op (∏ᶜ fun l ↦ W₀ (y l)))) y).app (op B) s
        ∀ (a : Γ(X', B)) (s : Γ(D.X p, B)),
          c (a • s) = X'.presheaf.map (prod.snd :
            (∏ᶜ fun l ↦ W₀ (y l)) ⨯ B ⟶ B).op a • c s)
    : ∃ P : ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat) ⟶
      ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat),
      IsOrderedCechModuleProjection f' M W₀ D e P := by
  obtain ⟨Q, hQ⟩ := orderedCech_degreewise_projection_exists M W₀ D e hlinear
  let q : D ⟶ D := CochainComplex.ofHom Q
    (orderedCech_degreewise_projection_comm M W₀ D e hd Q hQ)
  let v := ((Modules.pushforward f').mapHomologicalComplex (ComplexShape.up ℕ)).map q
  refine ⟨HomologicalComplex.extendMap v ComplexShape.embeddingUpNat, ?_⟩
  intro p B s y
  let E := (((Modules.pushforward f').mapHomologicalComplex _).obj D).extendXIso
    ComplexShape.embeddingUpNat (i := p) rfl
  have hv : E.hom.app B
      (((HomologicalComplex.extendMap v ComplexShape.embeddingUpNat).f (p : ℤ)).app B s) =
      (Q p).app (f' ⁻¹ᵁ B) (E.hom.app B s) := by
    rw [HomologicalComplex.extendMap_f v ComplexShape.embeddingUpNat
      (i := p) (i' := (p : ℤ)) rfl]
    change E.hom.app B (E.inv.app B ((Q p).app (f' ⁻¹ᵁ B) (E.hom.app B s))) = _
    have hi := congrArg (fun k ↦ (k.app B) ((Q p).app (f' ⁻¹ᵁ B)
      (E.hom.app B s))) E.inv_hom_id
    simpa only [Hom.comp_app, ConcreteCategory.comp_apply, Hom.id_app,
      CategoryTheory.id_apply] using hi
  change orderedCechNaturalCoordinate M W₀ D e p (f' ⁻¹ᵁ B) y
      (E.hom.app B _) = _
  rw [hv]
  exact hQ p (f' ⁻¹ᵁ B) (E.hom.app B s) y

end AlgebraicGeometry.Scheme.Modules
