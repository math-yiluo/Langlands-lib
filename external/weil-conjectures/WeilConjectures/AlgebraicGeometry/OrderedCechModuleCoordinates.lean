/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-! # Ordered coordinates of a usual module Čech presentation

Source: Stacks Project, Tags 01FJ and 01FK.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical map from an ordered intersection to the chosen categorical product.
Source: Stacks 01FJ, identification of products of opens with intersections.
(blueprint: def-pc-ordered-cech-module-coordinates). -/
noncomputable def orderedCechTupleOpenMap {X : Scheme.{u}} {r p : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (B : X.Opens)
    (t : Fin (p + 1) ↪o Fin r) :
    alternatingCechIntersection (fun i ↦ W ⟨i⟩) t ⊓ B ⟶
      (∏ᶜ fun l ↦ W ⟨t l⟩) ⨯ B :=
  prod.lift (Pi.lift fun l ↦ homOfLE (inf_le_left.trans
    (iInf_le (fun k ↦ W ⟨t k⟩) l))) (homOfLE inf_le_right)

/-- The coordinate transport is an isomorphism, including for empty intersections.
Source: Stacks 01FJ, products in the poset of opens are intersections.
(blueprint: def-pc-ordered-cech-module-coordinates).
Proof: The projections of the product give the reverse containment. -/
theorem orderedCechTupleOpenMap_isIso {X : Scheme.{u}} {r p : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (B : X.Opens)
    (t : Fin (p + 1) ↪o Fin r) : IsIso (orderedCechTupleOpenMap W B t) := by
  apply (PartialOrder.isIso_iff_eq _).mpr
  apply le_antisymm (orderedCechTupleOpenMap W B t).le
  apply le_inf
  · exact le_iInf fun k ↦ (prod.fst ≫ Pi.π (fun l ↦ W ⟨t l⟩) k).le
  · exact (prod.snd : (∏ᶜ fun l ↦ W ⟨t l⟩) ⨯ B ⟶ B).le


/-- Evaluate a usual Čech presentation on an increasing tuple after pushforward.
All transports are actual maps, including the extension isomorphism in degree p.
Source: Stacks 01FJ and 01FK, restriction to ordered tuples.
(blueprint: def-pc-ordered-cech-module-coordinates). -/
noncomputable def orderedCechModuleCoordinate {X T : Scheme.{u}} (f : X ⟶ T)
    (M : X.Modules) {r : ℕ} (W : ULift.{u} (Fin r) → X.Opens)
    (D : CochainComplex X.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤)
      isTerminalTop.op).obj (D.X p).val ≅
      ((cechComplexFunctor W).obj
        ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
          (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat)).X p)
    (p : ℕ) (B : T.Opens) (t : Fin (p + 1) ↪o Fin r)
    (s : Γ(((((Modules.pushforward f).mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat).X (p : ℤ), B)) :
    Γ(M, alternatingCechIntersection (fun i ↦ W ⟨i⟩) t ⊓ f ⁻¹ᵁ B) :=
  M.presheaf.map (orderedCechTupleOpenMap W (f ⁻¹ᵁ B) t).op
    (((e p).hom ≫ Pi.π (fun y : Fin (p + 1) → ULift.{u} (Fin r) ↦
      ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat).obj
          (op (∏ᶜ fun l ↦ W (y l)))) (fun l ↦ ⟨t l⟩)).app (op (f ⁻¹ᵁ B))
      (((((Modules.pushforward f).mapHomologicalComplex _).obj D).extendXIso
        ComplexShape.embeddingUpNat (i := p) rfl).hom.app B s))

section CoordinateProperties

variable {X T : Scheme.{u}} (f : X ⟶ T)
    (M : X.Modules) {r : ℕ} (W : ULift.{u} (Fin r) → X.Opens)
    (D : CochainComplex X.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤)
      isTerminalTop.op).obj (D.X p).val ≅
      ((cechComplexFunctor W).obj
        ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
          (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat)).X p)


/-- Ordered coordinates are additive.
Source: Stacks 01FK, restriction to ordered tuples.
(blueprint: def-pc-ordered-cech-module-coordinates).
Proof: Every factor in the defining composite is additive. -/
theorem orderedCechModuleCoordinate_add (p : ℕ) (B : T.Opens)
    (t : Fin (p + 1) ↪o Fin r)
    (s s' : Γ(((((Modules.pushforward f).mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat).X (p : ℤ), B)) :
    orderedCechModuleCoordinate f M W D e p B t (s + s') =
      orderedCechModuleCoordinate f M W D e p B t s +
        orderedCechModuleCoordinate f M W D e p B t s' := by
  simp only [orderedCechModuleCoordinate, map_add]

/-- Ordered coordinates send zero to zero.
Source: Stacks 01FK, restriction to ordered tuples.
(blueprint: def-pc-ordered-cech-module-coordinates).
Proof: Every factor in the defining composite preserves zero. -/
theorem orderedCechModuleCoordinate_zero (p : ℕ) (B : T.Opens)
    (t : Fin (p + 1) ↪o Fin r) :
    orderedCechModuleCoordinate f M W D e p B t 0 = 0 := by
  simp only [orderedCechModuleCoordinate, map_zero]

/-- Ordered coordinates preserve the local module action pulled back along f.
Source: Stacks 01FK, restriction of local scalars.
(blueprint: def-pc-ordered-cech-module-coordinates).
Proof: The extension isomorphism is locally linear, hlinear applies to its image,
and semilinearity of coefficient restriction gives the pulled-back scalar. -/
theorem orderedCechModuleCoordinate_smul
    (hlinear : ∀ (p : ℕ) (y : Fin (p + 1) → ULift.{u} (Fin r)) (B : X.Opens),
        let c : Γ(D.X p, B) → Γ(M, (∏ᶜ fun l ↦ W (y l)) ⨯ B) :=
          fun s ↦ ((e p).hom ≫ Pi.π (fun y : Fin (p + 1) → ULift.{u} (Fin r) ↦
            ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj
                M.presheafModuleCat).obj
                (op (∏ᶜ fun l ↦ W (y l)))) y).app (op B) s
        ∀ (a : Γ(X, B)) (s : Γ(D.X p, B)),
          c (a • s) = X.presheaf.map (prod.snd :
            (∏ᶜ fun l ↦ W (y l)) ⨯ B ⟶ B).op a • c s)
    (p : ℕ) (B : T.Opens) (t : Fin (p + 1) ↪o Fin r) (b : Γ(T, B))
    (s : Γ(((((Modules.pushforward f).mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat).X (p : ℤ), B)) :
    orderedCechModuleCoordinate f M W D e p B t (b • s) =
      X.presheaf.map (homOfLE (show
        alternatingCechIntersection (fun i ↦ W ⟨i⟩) t ⊓ f ⁻¹ᵁ B ≤ f ⁻¹ᵁ B
          from inf_le_right)).op (f.app B b) •
            orderedCechModuleCoordinate f M W D e p B t s := by
  simp only [orderedCechModuleCoordinate, Hom.app_smul]
  let v : Γ(D.X p, f ⁻¹ᵁ B) :=
    (((((Modules.pushforward f).mapHomologicalComplex _).obj D).extendXIso
    ComplexShape.embeddingUpNat (i := p) rfl).hom.app B s)
  let c : Γ(D.X p, f ⁻¹ᵁ B) → Γ(M, (∏ᶜ fun l ↦ W ⟨t l⟩) ⨯ f ⁻¹ᵁ B) :=
    fun x ↦ ((e p).hom ≫ Pi.π (fun y : Fin (p + 1) → ULift.{u} (Fin r) ↦
      ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat).obj
          (op (∏ᶜ fun l ↦ W (y l)))) (fun l ↦ ⟨t l⟩)).app (op (f ⁻¹ᵁ B)) x
  change M.presheaf.map (orderedCechTupleOpenMap W (f ⁻¹ᵁ B) t).op
      (c (f.app B b • v)) =
    X.presheaf.map (homOfLE inf_le_right).op (f.app B b) •
      M.presheaf.map (orderedCechTupleOpenMap W (f ⁻¹ᵁ B) t).op (c v)
  rw [show c (f.app B b • v) =
    X.presheaf.map prod.snd.op (f.app B b) • c v from
      hlinear p (fun l ↦ ⟨t l⟩) (f ⁻¹ᵁ B) (f.app B b) v, map_smul]
  congr 1
  change (X.presheaf.map prod.snd.op ≫
    X.presheaf.map (orderedCechTupleOpenMap W (f ⁻¹ᵁ B) t).op) (f.app B b) = _
  rw [← X.presheaf.map_comp]
  congr 2

/-- Ordered coordinates commute with restriction of the base open.
Source: Stacks 01FK, naturality of ordered restriction.
(blueprint: def-pc-ordered-cech-module-coordinates).
Proof: Apply naturality of the extension isomorphism and of e followed by its
product projection; the two coefficient restriction arrows agree in the poset. -/
theorem orderedCechModuleCoordinate_naturality (p : ℕ) {B C : T.Opens} (i : B ⟶ C)
    (s : Γ(((((Modules.pushforward f).mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat).X (p : ℤ), C))
    (t : Fin (p + 1) ↪o Fin r) :
    orderedCechModuleCoordinate f M W D e p B t
      ((((((Modules.pushforward f).mapHomologicalComplex _).obj D).extend
        ComplexShape.embeddingUpNat).X (p : ℤ)).presheaf.map i.op s) =
      M.presheaf.map (homOfLE (inf_le_inf le_rfl
        ((TopologicalSpace.Opens.map f.base).map i).le)).op
          (orderedCechModuleCoordinate f M W D e p C t s) := by
  let E := (((Modules.pushforward f).mapHomologicalComplex _).obj D).extendXIso
    ComplexShape.embeddingUpNat (i := p) rfl
  have hi : E.hom.app B
      ((((((Modules.pushforward f).mapHomologicalComplex _).obj D).extend
        ComplexShape.embeddingUpNat).X (p : ℤ)).presheaf.map i.op s) =
      (D.X p).presheaf.map ((TopologicalSpace.Opens.map f.base).map i).op
        (E.hom.app C s) := by
    change E.hom.app B _ = ((pushforward f).obj (D.X p)).presheaf.map i.op
      (E.hom.app C s)
    exact congrArg (fun k ↦ k s) (E.hom.mapPresheaf.naturality i.op)
  simp only [orderedCechModuleCoordinate]
  rw [hi]
  let j := (TopologicalSpace.Opens.map f.base).map i
  let c := (e p).hom ≫ Pi.π (fun y : Fin (p + 1) → ULift.{u} (Fin r) ↦
    ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat).obj
        (op (∏ᶜ fun l ↦ W (y l)))) (fun l ↦ ⟨t l⟩)
  have hc : c.app (op (f ⁻¹ᵁ B))
      ((D.X p).presheaf.map j.op (E.hom.app C s)) =
      M.presheaf.map (prod.map (𝟙 _) j).op
        (c.app (op (f ⁻¹ᵁ C)) (E.hom.app C s)) := by
    exact congrArg (fun k ↦ k (E.hom.app C s)) (c.naturality j.op)
  rw [hc]
  change (M.presheaf.map (prod.map (𝟙 _) j).op ≫
    M.presheaf.map (orderedCechTupleOpenMap W (f ⁻¹ᵁ B) t).op) _ =
    (M.presheaf.map (orderedCechTupleOpenMap W (f ⁻¹ᵁ C) t).op ≫
      M.presheaf.map (homOfLE (inf_le_inf le_rfl j.le)).op) _
  rw [← M.presheaf.map_comp, ← M.presheaf.map_comp]
  congr 2

end CoordinateProperties

end AlgebraicGeometry.Scheme.Modules
