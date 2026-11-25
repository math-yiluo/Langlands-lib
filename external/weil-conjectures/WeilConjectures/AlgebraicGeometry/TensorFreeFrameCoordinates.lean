/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.AlgebraicGeometry.EtaleTensorHomEvaluationNaturality
import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections

/-!
# Coordinates for a finite tensor-pullback frame

Source: Stacks Project, Tag 0GKU, proof of lemma-frobenius-linear-on-vb.
(blueprint: lem-fd-tensor-free-frame-coordinates).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules
attribute [local irreducible] tensorPullback tensorPullbackObj
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf

private theorem tensor_comparison_unit {A B : Scheme.{u}} (a : A ⟶ B) (G : B.Modules)
    (s : Γ(G, ⊤)) :
    ((tensorSectionsPullbackComparison a).hom.app G).app ⊤ (tensorSectionsUnit a G s) =
      pullbackSection a s := by
  have hi : (homOfLE a.preimage_top.ge).op =
      𝟙 (Opposite.op (⊤ : TopologicalSpace.Opens A)) := rfl
  unfold tensorSectionsUnit
  erw [hi, ((tensorPullback a).obj G).presheaf.map_id, Category.comp_id]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Classical.choose (exists_tensorPullbackAdjunction a)) (pullbackPushforwardAdjunction a) G
  have hs := congrArg (fun φ ↦ φ.app ⊤ s) hu
  simp only [Hom.comp_app, pushforward_map_app, ConcreteCategory.comp_apply] at hs
  exact hs
end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme
open Modules SheafOfModules
attribute [local irreducible] Modules.tensorPullback Modules.tensorPullbackObj
attribute [local instance 2000]
  Modules.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
private noncomputable def moduleFrameEquiv
    {X : Scheme.{u}} (M : X.Modules) (n : ℕ)
    (α : M ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))) :
    Γ(M, ⊤) ≃ₗ[Γ(X, ⊤)] (Fin n → Γ(X, ⊤)) :=
  let d : Γ(M, ⊤) ≃ₗ[Γ(X, ⊤)] (ULift.{u} (Fin n) → Γ(X, ⊤)) :=
    SheafOfModules.sectionsLinearEquivOfIsoFree α (op ⊤)
  d.trans (LinearEquiv.piCongrLeft' Γ(X, ⊤)
    (fun _ : ULift.{u} (Fin n) ↦ Γ(X, ⊤)) Equiv.ulift)

private theorem moduleFrameEquiv_apply
    {X : Scheme.{u}} (M : X.Modules) (n : ℕ)
    (α : M ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n)))
    (m : Γ(M, ⊤)) (i : Fin n) :
    moduleFrameEquiv M n α m i =
      Modules.Hom.app (Modules.freeπ (X := X) (ULift.up i)) ⊤ (α.hom.app ⊤ m) := rfl

private theorem moduleIso_cancel {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (m : Γ(M, ⊤)) : e.inv.app ⊤ (e.hom.app ⊤ m) = m := by
  change (e.hom ≫ e.inv).app ⊤ m = m
  rw [Iso.hom_inv_id]
  rfl

private theorem tensorRestriction_formula
    {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
    (V W : S.Etale) (h : W ⟶ V) :
    (Modules.etaleTensorSectionsSheaf E).obj.map h.op =
      Modules.tensorSectionsUnit h.left ((Modules.tensorPullback V.hom).obj E) ≫
        ((Modules.tensorSectionsComp h.left V.hom).hom.app E).app ⊤ ≫
          (eqToHom (congrArg (fun f ↦ (Modules.tensorPullback f).obj E) h.w)).app ⊤ := rfl

private theorem pullbackFrameCoordinates
    {A B : Scheme.{u}} (a : A ⟶ B) (G : B.Modules) (n : ℕ)
    (α : G ≅ SheafOfModules.free (R := B.ringCatSheaf) (ULift.{u} (Fin n)))
    (m : Γ(G, ⊤)) (i : Fin n) :
    ((Modules.pullback a).map α.hom ≫
      (Modules.pullbackFreeIso a (ULift.{u} (Fin n))).hom ≫
        Modules.freeπ (ULift.up i)).app ⊤ (Modules.pullbackSection a m) =
      a.appTop ((α.hom ≫ Modules.freeπ (ULift.up i)).app ⊤ m) := by
  rw [Modules.pullbackFreeIso_hom_freeπ, ← Functor.map_comp_assoc]
  change (Modules.pullbackObjUnitIso a).hom.app ⊤
    (((Modules.pullback a).map (α.hom ≫ Modules.freeπ (ULift.up i))).app ⊤
      (Modules.pullbackSection a m)) = _
  let ψ : G ⟶ Modules.unit B := α.hom ≫ Modules.freeπ (ULift.up i)
  have hn : ((Modules.pullback a).map ψ).app ⊤ (Modules.pullbackSection a m) =
      Modules.pullbackSection a (ψ.app ⊤ m) :=
    Modules.pullback_map_app_pullbackSection a ψ m
  have hu : (Modules.pullbackObjUnitIso a).hom.app ⊤
      (Modules.pullbackSection a (ψ.app ⊤ m)) = a.appTop (ψ.app ⊤ m) :=
    Modules.pullbackObjUnitIso_hom_app_pullbackSection a (ψ.app ⊤ m)
  exact (congrArg ((Modules.pullbackObjUnitIso a).hom.app ⊤) hn).trans hu

private theorem exists_pulled_frame_coordinates
    {A B : Scheme.{u}} (f : A ⟶ B) (G : B.Modules) (H : A.Modules) (n : ℕ)
    (α : G ≅ SheafOfModules.free (R := B.ringCatSheaf) (ULift.{u} (Fin n)))
    (t : (Modules.tensorPullback f).obj G ≅ H) (r : Γ(G, ⊤) ⟶ Γ(H, ⊤))
    (hr : ∀ m, t.inv.app ⊤ (r m) = Modules.tensorSectionsUnit f G m) :
    ∃ e : Γ(H, ⊤) ≃ₗ[Γ(A, ⊤)] (Fin n → Γ(A, ⊤)),
      ∀ (m : Γ(G, ⊤)) (i : Fin n),
        e (r m) i = f.appTop ((α.hom ≫ Modules.freeπ (ULift.up i)).app ⊤ m) := by
  let β : H ≅ SheafOfModules.free (R := A.ringCatSheaf) (ULift.{u} (Fin n)) :=
    t.symm ≪≫ (Modules.tensorSectionsPullbackComparison f).app G ≪≫
      (Modules.pullback f).mapIso α ≪≫ Modules.pullbackFreeIso f _
  refine ⟨moduleFrameEquiv H n β, ?_⟩
  intro m i
  rw [moduleFrameEquiv_apply]
  change Modules.Hom.app (Modules.freeπ (X := A) (ULift.up i)) ⊤
    ((Modules.pullbackFreeIso f (ULift.{u} (Fin n))).hom.app ⊤
      (((Modules.pullback f).map α.hom).app ⊤
        (((Modules.tensorSectionsPullbackComparison f).hom.app G).app ⊤
          (t.inv.app ⊤ (r m))))) = _
  rw [hr, Modules.tensor_comparison_unit]
  change ((Modules.pullback f).map α.hom ≫
    (Modules.pullbackFreeIso f (ULift.{u} (Fin n))).hom ≫
      Modules.freeπ (ULift.up i)).app ⊤ (Modules.pullbackSection f m) = _
  exact pullbackFrameCoordinates f G n α m i

private theorem exists_composed_frame_coordinates
    {A B : Scheme.{u}} (f : A ⟶ B) (G : B.Modules) (M H : A.Modules) (n : ℕ)
    (α : G ≅ SheafOfModules.free (R := B.ringCatSheaf) (ULift.{u} (Fin n)))
    (c : (Modules.tensorPullback f).obj G ≅ M) (d : M ≅ H) :
    ∃ e : Γ(H, ⊤) ≃ₗ[Γ(A, ⊤)] (Fin n → Γ(A, ⊤)),
      ∀ (m : Γ(G, ⊤)) (i : Fin n),
        e ((Modules.tensorSectionsUnit f G ≫ c.hom.app ⊤ ≫ d.hom.app ⊤) m) i =
          f.appTop ((α.hom ≫ Modules.freeπ (ULift.up i)).app ⊤ m) := by
  apply exists_pulled_frame_coordinates f G H n α (c ≪≫ d)
    (Modules.tensorSectionsUnit f G ≫ c.hom.app ⊤ ≫ d.hom.app ⊤)
  intro m
  change c.inv.app ⊤ (d.inv.app ⊤
    (d.hom.app ⊤ (c.hom.app ⊤ (Modules.tensorSectionsUnit f G m)))) = _
  rw [moduleIso_cancel, moduleIso_cancel]

private theorem exists_frame_coordinates_of_map_eq
    {A B : Scheme.{u}} (f : A ⟶ B) (G : B.Modules) (M H : A.Modules) (n : ℕ)
    (α : G ≅ SheafOfModules.free (R := B.ringCatSheaf) (ULift.{u} (Fin n)))
    (c : (Modules.tensorPullback f).obj G ≅ M) (d : M ≅ H)
    (r : Γ(G, ⊤) ⟶ Γ(H, ⊤))
    (hr : r = Modules.tensorSectionsUnit f G ≫ c.hom.app ⊤ ≫ d.hom.app ⊤) :
    ∃ e : Γ(H, ⊤) ≃ₗ[Γ(A, ⊤)] (Fin n → Γ(A, ⊤)),
      ∀ (m : Γ(G, ⊤)) (i : Fin n),
        e (r m) i = f.appTop ((α.hom ≫ Modules.freeπ (ULift.up i)).app ⊤ m) := by
  rw [hr]
  exact exists_composed_frame_coordinates f G M H n α c d

private theorem exists_restriction_frame_coordinates
    (S : Scheme.{u}) (E : S.Modules) [E.IsQuasicoherent]
    (V : S.Etale) (n : ℕ)
    (α : (Modules.tensorPullback V.hom).obj E ≅
      SheafOfModules.free (R := V.left.ringCatSheaf) (ULift.{u} (Fin n)))
    (W : S.Etale) (h : W ⟶ V) :
    ∃ e : Γ((Modules.tensorPullback W.hom).obj E, ⊤) ≃ₗ[Γ(W.left, ⊤)]
        (Fin n → Γ(W.left, ⊤)),
      ∀ (m : Γ((Modules.tensorPullback V.hom).obj E, ⊤)) (i : Fin n),
        e ((Modules.etaleTensorSectionsSheaf E).obj.map h.op m) i =
          h.left.appTop ((α.hom ≫ Modules.freeπ (ULift.up i)).app ⊤ m) := by
  exact exists_frame_coordinates_of_map_eq (A := W.left) (B := V.left) h.left
    ((Modules.tensorPullback V.hom).obj E)
    ((Modules.tensorPullback (h.left ≫ V.hom)).obj E)
    ((Modules.tensorPullback W.hom).obj E) n α
    ((Modules.tensorSectionsComp h.left V.hom).app E)
    (eqToIso (congrArg (fun f ↦ (Modules.tensorPullback f).obj E) h.w))
    ((Modules.etaleTensorSectionsSheaf E).obj.map h.op)
    (tensorRestriction_formula E V W h)

set_option maxRecDepth 2048 in
/-- Coordinates from a finite free frame commute with tensor-section restriction.

Source: Stacks Project, Tag 0GKU, proof of lemma-frobenius-linear-on-vb,
first paragraph (trivialize the vector bundle and use its frame coordinates).
(blueprint: lem-fd-tensor-free-frame-coordinates).

Proof: for h:W -> V, use the inverse of precisely the normalized composition map
that occurs in the definition of tensor-section restriction. Follow it by the
unit-normalized comparison with ordinary pullback, the pullback of the supplied
frame, and the free-pullback isomorphism. Global sections and reindexing give e_(W,h).
On a restricted section, the composition map cancels its inverse. The adjunction
unit equation identifies the remaining tensor unit with ordinary section pullback.
Pullback of each coordinate projection commutes with section pullback, and the
structure-sheaf comparison acts by h.appTop. Thus these coordinates of a restricted
section equal the pullback of the original frame coordinates. Apply this formula to
h=id and use the presheaf identity law to identify e_(V,id) with those original
coordinates. Substitution proves the asserted formula. Rank zero has no coordinate
to check, and all comparisons and identity laws apply to empty test schemes.
-/
theorem exists_natural_tensor_free_frame_coordinates
    (S : Scheme.{u}) (E : S.Modules) [E.IsQuasicoherent]
    (V : S.Etale) (n : ℕ)
    (α : (Modules.tensorPullback V.hom).obj E ≅
      SheafOfModules.free (R := V.left.ringCatSheaf) (ULift.{u} (Fin n))) :
    ∃ (e : ∀ (W : S.Etale), (W ⟶ V) →
        Γ((Modules.tensorPullback W.hom).obj E, ⊤) ≃ₗ[Γ(W.left, ⊤)]
          (Fin n → Γ(W.left, ⊤))),
      ∀ (W : S.Etale) (h : W ⟶ V)
        (m : Γ((Modules.tensorPullback V.hom).obj E, ⊤)) (i : Fin n),
        e W h ((Modules.etaleTensorSectionsSheaf E).obj.map h.op m) i =
          h.left.appTop (e V (𝟙 V) m i) := by
  classical
  have heach := exists_restriction_frame_coordinates S E V n α
  choose e he using heach
  refine ⟨e, ?_⟩
  intro W h m i
  have hi : e V (𝟙 V) m i = (α.hom ≫ Modules.freeπ (ULift.up i)).app ⊤ m := by
    have hi := he V (𝟙 V) m i
    have hid : (𝟙 V : V ⟶ V).left = 𝟙 V.left := rfl
    rw [hid, Scheme.Hom.id_appTop] at hi
    rw [show (𝟙 V).op = 𝟙 (op V) from rfl,
      (Modules.etaleTensorSectionsSheaf E).obj.map_id] at hi
    exact hi
  rw [he, hi]
end AlgebraicGeometry.Scheme
