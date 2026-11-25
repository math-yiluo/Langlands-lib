/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.AlgebraicGeometry.SectionModuleAlgebraicInverseImage
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat

/-! # Flat module objects under pro-étale inverse image

Source: Stacks Project, Tag 05VD, inverse image of flat module sheaves.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false in
/-- Inverse image followed by transport along an isomorphism of coefficient
rings preserves flat module objects.

Source: Stacks Project, Tag 05VD, lemma-pullback-flat.
(auxiliary; not a blueprint node)

Proof. The explicit balanced tensor comparison transports internal flatness to
site-flatness of section modules. Construct the set-valued inverse image as left
Kan extension followed by sheafification, with its usual right adjoint. Filtered
colimits of types commute with finite limits, so this inverse image is left exact.
The algebraic-operations comparison identifies its module inverse image with the
internal inverse image, including restriction along the coefficient isomorphism.
Apply the existing universe-polymorphic algebraic inverse-image flatness theorem.
Transfer the result through the source equivalence unit and the comparison
isomorphism: the local equational criterion is invariant under isomorphism by
mapping a finite relation forward and its local factorization sections backward.
Finally use the reverse tensor comparison to recover internal flatness. All finite
limits and finite sums include their empty cases. No Noetherian hypothesis is used. -/
theorem inverseImageModule_preservesFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (f)^*[Ab.{u + 1}].obj R) [IsMonHom ρ] [IsIso ρ] :
    (Mod.mapModComap ρ).PreservesFlat := by
  have flat_of_iso (R' : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
      {M N : SheafOfModules.{u + 1}
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R')}
      (e : M ≅ N) (hN : SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology X) (R := R') N) :
      SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology X) (R := R') M := by
    apply (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{u + 1, u, u + 1, u + 1}
      R' M).mpr
    intro U n a s h
    let s' (i : Fin n) := e.hom.val.app (Opposite.op U) (s i)
    have hs : (∑ i, a i • s' i) = 0 := by
      change (∑ i, a i • (e.hom.val.app (Opposite.op U)) (s i)) = 0
      simpa only [map_sum, map_smul, map_zero] using
        congrArg (fun z ↦ e.hom.val.app (Opposite.op U) z) h
    obtain ⟨S, hS, hlocal⟩ :=
      (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{u + 1, u, u + 1, u + 1}
        R' N).mp hN U n a s' hs
    refine ⟨S, hS, ?_⟩
    intro V f hf
    obtain ⟨l, b, t, ht, hb⟩ := hlocal V f hf
    refine ⟨l, b, fun j ↦ e.inv.val.app (Opposite.op V) (t j), ?_, hb⟩
    intro i
    have hi := congrArg (fun z ↦ e.inv.val.app (Opposite.op V) z) (ht i)
    simp only [map_sum, map_smul] at hi
    have hinv : e.inv.val.app (Opposite.op V)
        (e.hom.val.app (Opposite.op V) (M.val.map f.op (s i))) =
        M.val.map f.op (s i) := by
      have h := congrArg (fun z ↦ z.val.app (Opposite.op V) (M.val.map f.op (s i))) e.hom_inv_id
      exact h
    rw [← PresheafOfModules.naturality_apply] at hi
    exact hinv.symm.trans hi
  let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  let L := Functor.sheafPullbackConstruction.sheafPullback U (Type (u + 1))
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  let V := U.sheafPushforwardContinuous (Type (u + 1))
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  let adj : L ⊣ V := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    U (Type (u + 1)) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  have : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
    ⟨fun J _ _ ↦ ⟨inferInstance⟩⟩
  have : PreservesFiniteLimits (U.op.lan :
      (Y.ProEtᵒᵖ ⥤ Type (u + 1)) ⥤ X.ProEtᵒᵖ ⥤ Type (u + 1)) :=
    CategoryTheory.preservesFiniteLimits_op_lan_of_flat U
  have : PreservesFiniteLimits L := by dsimp only [L]; infer_instance
  obtain ⟨I, ⟨ei⟩⟩ := exists_sectionModuleAlgebraicInverseImage f R S ρ
  let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology Y) R
  let eX := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) S
  refine ⟨fun {M} hM ↦ ?_⟩
  have hsec := (InternalAbelianSheafModule.flat_iff_sectionModule
    (Scheme.ProEt.topology Y) R M).mp hM
  have hi := SheafOfModules.isFlat_algebraicInverseImageOfUniverses.{u + 1, u, u + 1, u,
    u + 1, u + 1}
    L V adj I (eY.functor.obj M) hsec
  let e : eX.functor.obj ((Mod.mapModComap ρ).obj M) ≅
      I.modules.obj (eY.functor.obj M) :=
    (Mod.mapModComap ρ ⋙ eX.functor).mapIso (eY.unitIso.app M) ≪≫
      ei.app (eY.functor.obj M)
  have ht := flat_of_iso
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) S) e hi
  exact (InternalAbelianSheafModule.flat_iff_sectionModule
    (Scheme.ProEt.topology X) S _).mpr ht

end AlgebraicGeometry.ProEtale
