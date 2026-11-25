/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars

import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison

/-! # Scalar extension preserves local finite presentation

The heart-level part of exact scalar extension, independent of bounded derived categories.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
variable {X : Scheme.{u}}
  (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]

lemma fp_iff_of_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (e : M ≅ N) : Mod.IsFinitelyPresented R M ↔ Mod.IsFinitelyPresented R N := by
  constructor
  · intro h
    rcases h with ⟨n, m, f, ⟨i⟩⟩
    exact ⟨n, m, f, ⟨e.symm ≪≫ i⟩⟩
  · intro h
    rcases h with ⟨n, m, f, ⟨i⟩⟩
    exact ⟨n, m, f, ⟨e ≪≫ i⟩⟩

lemma fp_map {X Y : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [MonObj S]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) S)
    [F.Additive] [PreservesFiniteColimits F]
    (e : F.obj (Mod.regular R) ≅ Mod.regular S)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) : Mod.IsFinitelyPresented S (F.obj M) := by
  rcases h with ⟨n, m, f, ⟨i⟩⟩
  let en (n : ℕ) : F.obj (Mod.finiteFree R n) ≅ Mod.finiteFree S n :=
    F.mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫ biproduct.mapIso (fun _ ↦ e)
  let f' : Mod.finiteFree S m ⟶ Mod.finiteFree S n := (en m).inv ≫ F.map f ≫ (en n).hom
  exact ⟨n, m, f', ⟨F.mapIso i ≪≫ PreservesCokernel.iso F f ≪≫
    cokernel.mapIso (F.map f) f' (en m) (en n) (by simp [f'])⟩⟩

private noncomputable def extendScalarsRegularIso :
    (Mod.extendScalars φ).obj (Mod.regular R) ≅ Mod.regular S := by
  let e₀ := Mod.toBimodRegularIso (R := R)
  let B := Bimod.ofMonHom φ
  let e₁ : B.tensorBimod ((Mod.toBimod R).obj (Mod.regular R)) ≅
      B.tensorBimod (Bimod.regular (Mon.mk R)) :=
    { hom := Bimod.whiskerLeft B e₀.hom
      inv := Bimod.whiskerLeft B e₀.inv
      hom_inv_id := by rw [← Bimod.whiskerLeft_comp_bimod, Iso.hom_inv_id];
                       exact Bimod.whiskerLeft_id_bimod
      inv_hom_id := by rw [← Bimod.whiskerLeft_comp_bimod, Iso.inv_hom_id];
                       exact Bimod.whiskerLeft_id_bimod }
  let e := e₁ ≪≫ Bimod.rightUnitorBimod B
  exact Mod.isoMk
    { hom := e.hom.hom
      inv := e.inv.hom
      hom_inv_id := congrArg Bimod.Hom.hom e.hom_inv_id
      inv_hom_id := congrArg Bimod.Hom.hom e.inv_hom_id }
    e.hom.left_act_hom

omit [IsCommMonObj S] in
lemma fp_extend
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) :
    Mod.IsFinitelyPresented S ((Mod.extendScalars φ).obj M) :=
  fp_map R S (Mod.extendScalars φ) (extendScalarsRegularIso R S φ) h

omit [IsCommMonObj S] in
/-- Extension of scalars preserves locally finitely presented internal modules.
Source: the finite-presentation argument in the proof of scalar-extension preservation
in Bhatt--Scholze, Sections 6.5 and 6.8, and the existing bounded scalar-extension proof
(auxiliary; not a blueprint node).

Proof: extension of scalars preserves finite colimits and sends the regular module to
the regular module, so it sends a finite free cokernel presentation to one over the
new ring. Pullback commutes with scalar extension by uniqueness of left adjoints.
Applying these facts on the original pro-étale presentation cover proves the claim.
The argument includes rank-zero presentations and the empty scheme. -/
lemma lfp_extend
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : IsLocallyFinitelyPresented R M) :
    IsLocallyFinitelyPresented S ((Mod.extendScalars φ).obj M) := by
  rcases h with ⟨U, hU⟩
  refine ⟨U, fun i ↦ ?_⟩
  let F := upperStar Ab.{u + 1} (U.f i)
  exact (fp_iff_of_iso ((pullbackExtendScalarsComparison (U.f i) R S φ).app M).symm).mp
    (fp_extend (F.obj R) (F.obj S) (F.map φ) (hU i))

end AlgebraicGeometry.ProEtale
