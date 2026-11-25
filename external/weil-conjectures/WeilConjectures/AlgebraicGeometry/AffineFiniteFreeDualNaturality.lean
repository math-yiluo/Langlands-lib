/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
import WeilConjectures.AlgebraicGeometry.FreeSheafDualTranspose
public import WeilConjectures.AlgebraicGeometry.AffineBasisDualMatrix

/-! # Finite basis dual comparison on an affine open

Source: Stacks Project, schemes.tex, Tag 01HV; duality.tex, Tag 0BQZ.
(blueprint: lem-sc-affine-finite-free-dual-naturality).
-/

@[expose] public section

universe u v w
open CategoryTheory Opposite Module
namespace AlgebraicGeometry

/-- The associated sheaf of a based module, transported to the affine open,
is the free sheaf on the same basis. All maps are constructed from the basis.
Source: Stacks Project, schemes.tex, Tag 01HV.
(blueprint: lem-sc-affine-finite-free-dual-naturality). -/
noncomputable abbrev affineBasisSheafIso {Y : Scheme.{u}} (U : Y.affineOpens)
    (M : ModuleCat.{u} Γ(Y, U.1)) {I : Type u} (b : Basis I Γ(Y, U.1) M) :
    ((tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj M) ≅
      SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) I :=
  affineBasisCoordinatesIso U M b

/-- Transport a contravariant duality through specified coordinate comparisons.
Source: Stacks Project, Tag 0BQZ, transport of the finite free dual comparison.
(blueprint: lem-sc-affine-finite-free-dual-naturality). -/
noncomputable def affineDualTransportIso {C : Type w} [Category.{v} C]
    (D : Cᵒᵖ ⥤ C) {M F P : C} (e : M ≅ F) (d : P ≅ F)
    (h : D.obj (op F) ≅ F) : D.obj (op M) ≅ P :=
  let c := D.mapIso e.symm.op ≪≫ h ≪≫ d.symm
  { hom := D.map e.inv.op ≫ h.hom ≫ d.inv
    inv := d.hom ≫ h.inv ≫ D.map e.hom.op
    hom_inv_id := by
      simpa only [c, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
        Functor.mapIso_inv, Iso.op_hom, Iso.op_inv, Iso.symm_hom, Iso.symm_inv,
        Category.assoc] using c.hom_inv_id
    inv_hom_id := by
      simpa only [c, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
        Functor.mapIso_inv, Iso.op_hom, Iso.op_inv, Iso.symm_hom, Iso.symm_inv,
        Category.assoc] using c.inv_hom_id }

private theorem affineDualTransportIso_hom {C : Type w} [Category.{v} C]
    (D : Cᵒᵖ ⥤ C) {M F P : C} (e : M ≅ F) (d : P ≅ F)
    (h : D.obj (op F) ≅ F) :
    (affineDualTransportIso D e d h).hom = D.map e.inv.op ≫ h.hom ≫ d.inv := rfl

/-- Explicit comparison of the internal dual and the sheafified module dual.
Use the basis and its dual basis, with the canonical dual of a finite free sheaf.
No data are selected from an unproved existence theorem.
Source: Stacks Project, duality.tex, Tag 0BQZ; schemes.tex, Tag 01HV.
(blueprint: lem-sc-affine-finite-free-dual-naturality). -/
@[irreducible]
noncomputable def affineBasisDualIso {Y : Scheme.{u}} (U : Y.affineOpens)
    (M : ModuleCat.{u} Γ(Y, U.1)) {I : Type u} [Fintype I]
    (b : Basis I Γ(Y, U.1) M) :
    SheafOfModules.homObj (R := U.1.toScheme.toRingedSpace.sheaf)
      ((tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj M)
      (SheafOfModules.unit U.1.toScheme.ringCatSheaf) ≅
    (tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj
      (ModuleCat.of Γ(Y, U.1) (M ⟶ ModuleCat.of Γ(Y, U.1) Γ(Y, U.1))) := by
  classical
  exact affineDualTransportIso
    ((SheafOfModules.homFunctor U.1.toScheme.toRingedSpace.sheaf).flip.obj
      (SheafOfModules.unit U.1.toScheme.ringCatSheaf))
    (affineBasisCoordinatesIso U M b) (affineDualBasisCoordinatesIso U M b)
    (SheafOfModules.homObjFreeUnitIso.{u} (R := U.1.toScheme.toRingedSpace.sheaf) I)

set_option backward.isDefEq.respectTransparency false in
private theorem affineBasisDualIso_hom {Y : Scheme.{u}} (U : Y.affineOpens)
    (M : ModuleCat.{u} Γ(Y, U.1)) {I : Type u} [Fintype I]
    (b : Basis I Γ(Y, U.1) M) :
    (affineBasisDualIso U M b).hom =
      ((SheafOfModules.homFunctor U.1.toScheme.toRingedSpace.sheaf).flip.obj
        (SheafOfModules.unit U.1.toScheme.ringCatSheaf)).map
        (affineBasisCoordinatesIso U M b).inv.op ≫
      (SheafOfModules.homObjFreeUnitIso.{u}
        (R := U.1.toScheme.toRingedSpace.sheaf) I).hom ≫
      (affineDualBasisCoordinatesIso U M b).inv := by
  unfold affineBasisDualIso
  exact affineDualTransportIso_hom
    ((SheafOfModules.homFunctor U.1.toScheme.toRingedSpace.sheaf).flip.obj
      (SheafOfModules.unit U.1.toScheme.ringCatSheaf))
    (affineBasisCoordinatesIso U M b) (affineDualBasisCoordinatesIso U M b)
    (SheafOfModules.homObjFreeUnitIso.{u} (R := U.1.toScheme.toRingedSpace.sheaf) I)

private theorem affineDualFunctor_map {X : Scheme.{u}} {M N : X.Modules}
    (f : N ⟶ M) :
    ((SheafOfModules.homFunctor X.toRingedSpace.sheaf).flip.obj
      (SheafOfModules.unit X.ringCatSheaf)).map f.op =
    SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf) f
      (𝟙 (SheafOfModules.unit X.ringCatSheaf)) := rfl

private lemma free_target_ext {X : Scheme.{u}} {J : Type u} [Finite J]
    [DecidableEq J] {P : X.Modules}
    {a b : P ⟶ SheafOfModules.free (R := X.ringCatSheaf) J}
    (h : ∀ j, a ≫ Scheme.Modules.freeπ j = b ≫ Scheme.Modules.freeπ j) : a = b := by
  let := Fintype.ofFinite J
  have ha : a = a ≫ ∑ j : J, Scheme.Modules.freeπ j ≫ SheafOfModules.ιFree j :=
    ((congrArg (fun k ↦ a ≫ k) (Scheme.Modules.sum_freeπ_ιFree (X := X))).trans
      (Category.comp_id a)).symm
  have hb : b ≫ ∑ j : J, Scheme.Modules.freeπ j ≫ SheafOfModules.ιFree j = b :=
    (congrArg (fun k ↦ b ≫ k) (Scheme.Modules.sum_freeπ_ιFree (X := X))).trans
      (Category.comp_id b)
  calc
    a = a ≫ ∑ j : J, Scheme.Modules.freeπ j ≫ SheafOfModules.ιFree j := ha
    _ = ∑ j : J, a ≫ (Scheme.Modules.freeπ j ≫ SheafOfModules.ιFree j) :=
      Preadditive.comp_sum _ _ _
    _ = ∑ j : J, b ≫ (Scheme.Modules.freeπ j ≫ SheafOfModules.ιFree j) :=
      Finset.sum_congr rfl fun j _ ↦
        (Category.assoc _ _ _).symm.trans
          ((congrArg (fun k ↦ k ≫ SheafOfModules.ιFree j) (h j)).trans
            (Category.assoc _ _ _))
    _ = b ≫ ∑ j : J, Scheme.Modules.freeπ j ≫ SheafOfModules.ιFree j :=
      (Preadditive.comp_sum _ _ _).symm
    _ = b := hb

private lemma dual_conjugation {C : Type w} [Category.{v} C]
    (D : Cᵒᵖ ⥤ C) {M N F G P Q : C} (eM : M ≅ F) (eN : N ≅ G)
    (dM : P ≅ F) (dN : Q ≅ G) (hM : D.obj (op F) ≅ F) (hN : D.obj (op G) ≅ G)
    (f : N ⟶ M) (g : P ⟶ Q)
    (h : hM.inv ≫ D.map (eN.inv ≫ f ≫ eM.hom).op ≫ hN.hom =
      dM.inv ≫ g ≫ dN.hom) :
    D.map f.op ≫ (D.map eN.inv.op ≫ hN.hom ≫ dN.inv) =
      (D.map eM.inv.op ≫ hM.hom ≫ dM.inv) ≫ g := by
  have key := congrArg (fun k ↦ hM.hom ≫ k ≫ dN.inv) h
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] at key
  have hf : D.map f.op ≫ D.map eN.inv.op =
      D.map eM.inv.op ≫ D.map (eN.inv ≫ f ≫ eM.hom).op := by
    rw [← D.map_comp, ← D.map_comp]
    congr 1
    simp only [← op_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change D.map f.op ≫ (D.map eN.inv.op ≫ hN.hom ≫ dN.inv) =
    (D.map eM.inv.op ≫ hM.hom ≫ dM.inv) ≫ g
  calc
    _ = (D.map f.op ≫ D.map eN.inv.op) ≫ hN.hom ≫ dN.inv := by
      simp only [Category.assoc]
    _ = (D.map eM.inv.op ≫ D.map (eN.inv ≫ f ≫ eM.hom).op) ≫
        hN.hom ≫ dN.inv := by rw [hf]
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun k ↦ D.map eM.inv.op ≫ k) key

private lemma dual_conjugation_of_comparisons {C : Type w} [Category.{v} C]
    (D : Cᵒᵖ ⥤ C) {M N F G P Q : C} (eM : M ≅ F) (eN : N ≅ G)
    (dM : P ≅ F) (dN : Q ≅ G) (hM : D.obj (op F) ≅ F) (hN : D.obj (op G) ≅ G)
    (f : N ⟶ M) (g : P ⟶ Q) (df : D.obj (op M) ⟶ D.obj (op N))
    (aM : D.obj (op M) ⟶ P) (aN : D.obj (op N) ⟶ Q)
    (hf : df = D.map f.op)
    (haM : aM = D.map eM.inv.op ≫ hM.hom ≫ dM.inv)
    (haN : aN = D.map eN.inv.op ≫ hN.hom ≫ dN.inv)
    (h : hM.inv ≫ D.map (eN.inv ≫ f ≫ eM.hom).op ≫ hN.hom =
      dM.inv ≫ g ≫ dN.hom) : df ≫ aN = aM ≫ g := by
  rw [hf, haM, haN]
  exact dual_conjugation D eM eN dM dN hM hN f g h

private lemma free_dual_matrix_ext {X : Scheme.{u}} {I J : Type u}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (phi : SheafOfModules.free (R := X.ringCatSheaf) J ⟶ SheafOfModules.free I)
    {P Q : X.Modules} (a : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ P)
    (g : P ⟶ Q) (b : Q ⟶ SheafOfModules.free (R := X.ringCatSheaf) J)
    (h : ∀ i j, SheafOfModules.ιFree i ≫ a ≫ g ≫ b ≫ Scheme.Modules.freeπ j =
      SheafOfModules.ιFree j ≫ phi ≫ Scheme.Modules.freeπ i) :
    (SheafOfModules.homObjFreeUnitIso (R := X.toRingedSpace.sheaf) I).inv ≫
      SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf) phi
        (𝟙 (SheafOfModules.unit X.ringCatSheaf)) ≫
      (SheafOfModules.homObjFreeUnitIso (R := X.toRingedSpace.sheaf) J).hom = a ≫ g ≫ b := by
  apply Scheme.Modules.free_hom_ext
  intro i
  apply free_target_ext
  intro j
  simpa only [Category.assoc] using
    (freeSheafDualTranspose_component phi i j).trans (h i j).symm

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The finite basis dual comparisons commute with precomposition, for any
choices of bases on the two modules.
Source: Stacks Project, schemes.tex, Tag 01HV; duality.tex, Tag 0BQZ.
(blueprint: lem-sc-affine-finite-free-dual-naturality).

Proof: On a principal open D(g), the basis sheaf is the free module on the
localized basis. The free internal dual is identified with its coordinates by
evaluation on those generators. The dual-basis representation of a functional
has exactly these coordinates, by Basis.dualBasis_repr. Thus the displayed
comparison sends an internal functional to the vector of its evaluations,
regarded as the localized module dual. If f has matrix (a_ij) in the two bases,
precomposition on either side sends an evaluation vector (v_i) to
(sum_i a_ij v_i)_j. Localization preserves these finite sums and products, so
the two composites agree on D(g). They agree on all opens by the sheaf property,
since the principal opens form a basis. Transport by U.isoSpec preserves the
identity. This also proves independence of the basis. No nontriviality of the
ring is required: for rank zero or a zero ring all the same formulas hold and
the maps between zero modules are unique. -/
theorem affineBasisDualIso_naturality {Y : Scheme.{u}} (U : Y.affineOpens)
    (M N : ModuleCat.{u} Γ(Y, U.1)) {I J : Type u} [Fintype I] [Fintype J]
    (bM : Basis I Γ(Y, U.1) M) (bN : Basis J Γ(Y, U.1) N) (f : N ⟶ M) :
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    SheafOfModules.homObjMap (R := U.1.toScheme.toRingedSpace.sheaf)
        (T.map f) (𝟙 (SheafOfModules.unit U.1.toScheme.ringCatSheaf)) ≫
      (affineBasisDualIso U N bN).hom =
    (affineBasisDualIso U M bM).hom ≫
      T.map (ModuleCat.ofHom (Linear.leftComp Γ(Y, U.1)
        (ModuleCat.of Γ(Y, U.1) Γ(Y, U.1)) f)) := by
  classical
  let S := Scheme.Modules.restrictFunctor U.2.isoSpec.hom
  let T := tilde.functor Γ(Y, U.1) ⋙ S
  let eM := affineBasisCoordinatesIso U M bM
  let eN := affineBasisCoordinatesIso U N bN
  let dM := affineDualBasisCoordinatesIso U M bM
  let dN := affineDualBasisCoordinatesIso U N bN
  let dualf : ModuleCat.of Γ(Y, U.1) (M ⟶ ModuleCat.of Γ(Y, U.1) Γ(Y, U.1)) ⟶
      ModuleCat.of Γ(Y, U.1) (N ⟶ ModuleCat.of Γ(Y, U.1) Γ(Y, U.1)) :=
    ModuleCat.ofHom (Linear.leftComp Γ(Y, U.1)
    (ModuleCat.of Γ(Y, U.1) Γ(Y, U.1)) f)
  let phi : SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) J ⟶
      SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) I := eN.inv ≫ T.map f ≫ eM.hom
  have entries := free_dual_matrix_ext (X := U.1.toScheme) phi dM.inv
    (T.map dualf) dN.hom (fun i j ↦ affineBasisDualMatrix_component U M N bM bN f i j)
  let D := (SheafOfModules.homFunctor U.1.toScheme.toRingedSpace.sheaf).flip.obj
    (SheafOfModules.unit U.1.toScheme.ringCatSheaf)
  exact dual_conjugation_of_comparisons D eM eN dM dN
    (SheafOfModules.homObjFreeUnitIso.{u} (R := U.1.toScheme.toRingedSpace.sheaf) I)
    (SheafOfModules.homObjFreeUnitIso.{u} (R := U.1.toScheme.toRingedSpace.sheaf) J)
    (T.map f) (T.map dualf)
    (SheafOfModules.homObjMap (R := U.1.toScheme.toRingedSpace.sheaf)
      (T.map f) (𝟙 (SheafOfModules.unit U.1.toScheme.ringCatSheaf)))
    (affineBasisDualIso U M bM).hom (affineBasisDualIso U N bN).hom
    (affineDualFunctor_map (X := U.1.toScheme) (T.map f)).symm
    (affineBasisDualIso_hom U M bM) (affineBasisDualIso_hom U N bN) entries

end AlgebraicGeometry
