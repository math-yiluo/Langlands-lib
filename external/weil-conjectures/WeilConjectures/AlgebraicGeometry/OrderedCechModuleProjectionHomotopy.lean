/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrderedCechModuleProjectionLift
public import Mathlib.Algebra.Homology.Homotopy
import WeilConjectures.AlgebraicGeometry.OrderedCechModuleFirstSortingBoundary
import WeilConjectures.AlgebraicGeometry.OrderedCechModuleSecondSortingBoundary
import WeilConjectures.AlgebraicGeometry.OrderedCechModuleCoordinates

/-! # Sorting homotopy for the module Čech projection

Source: Stacks Project, Tags 01FK and 01FM.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

private theorem fullCoordinate_ext {X' T' : Scheme.{u}} (f' : X' ⟶ T')
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).X p)
    (p : ℕ) (B : T'.Opens)
    (s s' : Γ(((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat).X (p : ℤ), B))
    (hs : ∀ y, orderedCechFullCoordinate f' M W₀ D e p B y s =
      orderedCechFullCoordinate f' M W₀ D e p B y s') : s = s' := by
  let E := (((Modules.pushforward f').mapHomologicalComplex _).obj D).extendXIso
    ComplexShape.embeddingUpNat (i := p) rfl
  let K := (prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
    (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat
  let F := fun y : Fin (p + 1) → ULift.{u} (Fin r) ↦
    K.obj (op (∏ᶜ fun l ↦ W₀ (y l)))
  have he : (e p).hom.app (op (f' ⁻¹ᵁ B)) (E.hom.app B s) =
      (e p).hom.app (op (f' ⁻¹ᵁ B)) (E.hom.app B s') := by
    apply Concrete.isLimit_ext _
      (isLimitOfPreserves ((evaluation _ _).obj (op (f' ⁻¹ᵁ B)))
        (limit.isLimit (Discrete.functor F)))
    intro ⟨y⟩
    change ((Pi.π F y).app (op (f' ⁻¹ᵁ B)))
        ((e p).hom.app (op (f' ⁻¹ᵁ B)) (E.hom.app B s)) =
      ((Pi.π F y).app (op (f' ⁻¹ᵁ B))) ((e p).hom.app (op (f' ⁻¹ᵁ B)) (E.hom.app B s'))
    dsimp only [F, K, E]
    convert hs y using 1
    all_goals rfl
  have he' := congrArg (fun x ↦ (e p).inv.app (op (f' ⁻¹ᵁ B)) x) he
  have hv : E.hom.app B s = E.hom.app B s' := by
    simpa using he'
  have hv' := congrArg (fun x ↦ E.inv.app B x) hv
  simpa only [← ConcreteCategory.comp_apply, ← Hom.comp_app, E.hom_inv_id,
    Hom.id_app, ConcreteCategory.id_apply, map_zero] using hv'

/-- The signed projection is homotopic to identity before any kernel hypothesis.
Source: Stacks 01FM, equations 20.23.6.1 and 20.23.6.2.
(blueprint: lem-pc-ordered-cech-module-projection-homotopy).

Proof: Transport the first sorting family H and the second family J along e on every
open. Their identities give dH+Hd=id-kappa and dJ+Jd=kappa-P. Naturality follows
termwise from restriction functoriality; local linearity follows from hlinear since
all terms restrict the same scalar to the same intersection. Their sum is therefore
an actual family of module-sheaf maps with boundary id-P. Push forward these maps
and extend by zero in negative degrees. The degree-zero incoming component is zero,
as in the natural-degree families. These give the asserted homotopy. The formulas
also apply to empty families and to degrees with no increasing tuples. -/
theorem orderedCech_module_projection_homotopy {X' T' : Scheme.{u}} (f' : X' ⟶ T')
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
    (P : ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat) ⟶
      ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat))
    (hP : IsOrderedCechModuleProjection f' M W₀ D e P) :
    Nonempty (Homotopy (𝟙 _) P) := by
  classical
  obtain ⟨H, hH⟩ := orderedCech_module_firstSorting_boundary f' M W₀ D e hd hlinear
  obtain ⟨J, hJ⟩ := orderedCech_module_secondSorting_boundary f' M W₀ D e hd hlinear P hP
  have hb : Homotopy.nullHomotopicMap' H + Homotopy.nullHomotopicMap' J = 𝟙 _ - P := by
    apply HomologicalComplex.Hom.ext
    funext i
    by_cases hi : 0 ≤ i
    · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hi
      apply Modules.hom_ext _ _
      intro B
      ext s
      apply fullCoordinate_ext f' M W₀ D e p B
      intro y
      change orderedCechFullCoordinate f' M W₀ D e p B y
          ((((Homotopy.nullHomotopicMap' H).f (p : ℤ)).app B s) +
            (((Homotopy.nullHomotopicMap' J).f (p : ℤ)).app B s)) =
        orderedCechFullCoordinate f' M W₀ D e p B y (s - ((P.f (p : ℤ)).app B s))
      have ha : ∀ a b, orderedCechFullCoordinate f' M W₀ D e p B y (a + b) =
          orderedCechFullCoordinate f' M W₀ D e p B y a +
            orderedCechFullCoordinate f' M W₀ D e p B y b := by
        intros
        simp only [orderedCechFullCoordinate, map_add]
      have hs : ∀ a b, orderedCechFullCoordinate f' M W₀ D e p B y (a - b) =
          orderedCechFullCoordinate f' M W₀ D e p B y a -
            orderedCechFullCoordinate f' M W₀ D e p B y b := by
        intros
        simp only [orderedCechFullCoordinate, map_sub]
      rw [ha, hs, hH p B y s, hJ p B y s, sub_add_sub_cancel]
    · exact (((Modules.pushforward f').mapHomologicalComplex _).obj D).isZero_extend_X
        ComplexShape.embeddingUpNat i (by intro p hp; simp at hp; omega) |>.eq_of_src _ _
  apply Nonempty.intro
  refine Homotopy.equivSubZero.symm ?_
  rw [← hb]
  simpa only [add_zero] using (Homotopy.nullHomotopy' H).add (Homotopy.nullHomotopy' J)

end AlgebraicGeometry.Scheme.Modules
