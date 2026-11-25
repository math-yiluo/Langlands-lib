/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde

import WeilConjectures.AlgebraicGeometry.FormalModuleQuotientAffineProjection
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.ModulePullbackIdealPowerProductImage
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine

/-! # Sheafification of a positive affine module quotient

Source: Stacks Project, Tags 01I7, 01I8, 01IC and 087W.
(blueprint: lem-weil-pbc-affine-formal-quotient-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem product_qc {X : Scheme.{u}} {P : X.Modules}
    (ι : P ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules)
    [P.IsQuasicoherent] [F.IsQuasicoherent] :
    (Scheme.idealModuleProduct ι F).IsQuasicoherent := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  have := (Scheme.Modules.quasiCoherent_tensor_product_affine_sections P F).1
  let a := MonoidalCategoryStruct.whiskerRight ι F ≫
    (MonoidalCategoryStruct.leftUnitor F).hom
  have := Scheme.Modules.isQuasicoherent_cokernel a
  have := Scheme.Modules.isQuasicoherent_kernel (cokernel.π a)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Abelian.imageIsoImage a) inferInstance

-- Quotient projection transport elaborates several affine adjunction layers.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem spec_quotient_comparison
    (A : Type u) [CommRing A] (I : Ideal A)
    (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    (M : ModuleCat.{u} A) (n : ℕ) (hn : 0 < n) :
    ∃ e : formalModuleQuotient J n ((tilde.functor (CommRingCat.of A)).obj M) ≅
        (tilde.functor (CommRingCat.of A)).obj
          (ModuleCat.of A (M ⧸ (I ^ n • (⊤ : Submodule A M)))),
      formalModuleQuotientπ J n ((tilde.functor (CommRingCat.of A)).obj M) ≫ e.hom =
        (tilde.functor (CommRingCat.of A)).map
          (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).mkQ) := by
  let T := tilde.functor (CommRingCat.of A)
  let G := moduleSpecΓFunctor (R := CommRingCat.of A)
  let Q := formalModuleQuotient J n (T.obj M)
  let π := formalModuleQuotientπ J n (T.obj M)
  let η := (tilde.toTildeΓNatIso (R := CommRingCat.of A)).hom
  let ε := Scheme.Modules.fromTildeΓNatTrans (R := CommRingCat.of A)
  let p := η.app M ≫ G.map π
  obtain ⟨hp, hk⟩ := formalModuleQuotient_affine_projection A I J hJ M n hn
  let e : ModuleCat.of A (M ⧸ (I ^ n • (⊤ : Submodule A M))) ≅ G.obj Q :=
    ((Submodule.quotEquivOfEq _ _ hk.symm) ≪≫ₗ
      p.hom.quotKerEquivOfSurjective hp).toModuleIso
  have he : ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).mkQ ≫ e.hom = p := by
    ext x
    rfl
  have : (T.obj M).IsQuasicoherent := by
    change (tilde (R := CommRingCat.of A) M).IsQuasicoherent
    infer_instance
  have : (Scheme.idealSheafPower J.toModulesι n).1.IsQuasicoherent :=
    (Scheme.Modules.ideal_times_quasiCoherent_affine_sections J (T.obj M)).2.2.1 n hn
  have : (Scheme.idealModuleProduct
      (Scheme.idealSheafPower J.toModulesι n).2 (T.obj M)).IsQuasicoherent :=
    product_qc _ _
  have : Q.IsQuasicoherent := Scheme.Modules.isQuasicoherent_cokernel _
  have : IsIso (ε.app Q) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent Q
  let a : Q ≅ T.obj (ModuleCat.of A (M ⧸ (I ^ n • (⊤ : Submodule A M)))) :=
    (asIso (ε.app Q)).symm ≪≫ T.mapIso e.symm
  refine ⟨a, ?_⟩
  apply (cancel_mono (T.map e.hom)).1
  change (π ≫ inv (ε.app Q) ≫ T.map e.inv) ≫ T.map e.hom =
    T.map (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).mkQ) ≫ T.map e.hom
  rw [Category.assoc, Category.assoc, ← T.map_comp, e.inv_hom_id]
  erw [T.map_id (G.obj Q), Category.comp_id, ← T.map_comp, he]
  apply (cancel_mono (ε.app Q)).1
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  change π = T.map (η.app M ≫ G.map π) ≫ ε.app Q
  have hε : T.map (G.map π) ≫ ε.app Q = ε.app (T.obj M) ≫ π :=
    ε.naturality π
  rw [T.map_comp, Category.assoc, hε, ← Category.assoc]
  have htri := (tilde.adjunction (R := CommRingCat.of A)).left_triangle_components M
  change T.map (η.app M) ≫ ε.app (T.obj M) = 𝟙 _ at htri
  rw [htri, Category.id_comp]

private noncomputable def quotientFunctor {X : Scheme.{u}} (J : X.IdealSheafData)
    (n : ℕ) : X.Modules ⥤ X.Modules where
  obj := formalModuleQuotient J n
  map f := formalModuleQuotientMap J f (Nat.le_refl n)
  map_id M := formalModuleQuotientMap_id J M n
  map_comp f g := formalModuleQuotientMap_comp J f g (Nat.le_refl n) (Nat.le_refl n)

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_quotient_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Y.IdealSheafData) (G : Y.Modules) (hG : G.IsQuasicoherent) (n : ℕ) :
    ∃ e : formalModuleQuotient (J.comap f) n ((Scheme.Modules.tensorPullback f).obj G) ≅
        (Scheme.Modules.tensorPullback f).obj (formalModuleQuotient J n G),
      formalModuleQuotientπ (J.comap f) n ((Scheme.Modules.tensorPullback f).obj G) ≫
        e.hom = (Scheme.Modules.tensorPullback f).map (formalModuleQuotientπ J n G) := by
  classical
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction f
  let := adj.isLeftAdjoint
  let T := Scheme.Modules.tensorPullback f
  let i := Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2 G
  let k := Scheme.idealModuleProductι
    (Scheme.idealSheafPower (J.comap f).toModulesι n).2 (T.obj G)
  have : Mono k := by
    dsimp [k, Scheme.idealModuleProductι]
    infer_instance
  have he : Subobject.mk k = Subobject.mk (image.ι (T.map i)) := by
    rw [← imageSubobject_mono k]
    exact (modulePullbackIdealPowerProductImage f J G hG n).symm
  let a := Subobject.isoOfMkEqMk k (image.ι (T.map i)) he
  let e : cokernel k ≅ T.obj (cokernel i) :=
    cokernel.mapIso k (image.ι (T.map i)) a (Iso.refl _) (by simp [a]) ≪≫
      cokernelImageι (T.map i) ≪≫ (PreservesCokernel.iso T i).symm
  refine ⟨e, ?_⟩
  change cokernel.π k ≫ e.hom = T.map (cokernel.π i)
  dsimp only [e, Iso.trans_hom, Iso.symm_hom]
  rw [PreservesCokernel.iso_inv]
  simp [cokernel.mapIso, cokernelImageι]

-- Transport along the affine isomorphism unfolds ideal and module equivalences.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The affine module quotient realizes the explicit sheaf quotient, with its projection.
No finiteness, completeness or Noetherian hypothesis on the module is required.

Source: Stacks Project, Tags 01I7 and 01IC (exact affine module correspondence),
01I8 (tensor products), and 087W (the positive-power quotient system).
(blueprint: lem-weil-pbc-affine-formal-quotient-comparison).

Proof:
1. On Spec A, the ideal sheaf associated with I has power inclusion with range I^n.
The affine tensor-sections formula identifies the image of multiplication on tilde M
with I^n M. Exact affine sections identify the cokernel projection with the surjection
M to M/I^n M: its kernel is I^n M. Thus the quotient's sections are canonically
isomorphic to M/I^n M, with the given projection.
2. Both the cokernel and tilde of the module quotient are quasi-coherent. The affine
counit therefore sheafifies that section isomorphism to an isomorphism of sheaves.
Its composite with the quotient projection is tilde of the module quotient map,
as seen on global sections and hence on every localized basic open.
3. Use X's canonical affine isomorphism with Spec A. The affine ideal dictionary sends
J to the ideal I of top sections. Pullback along the isomorphism is an equivalence,
so preserves cokernels and images. The ideal-power product image comparison identifies
the transported multiplication image with the one used in formalModuleQuotient J.
The uniqueness of maps from a cokernel transports the projection equation as well.
For I=0 the projection is an isomorphism; for I=A the quotient is zero. Empty affine
schemes and zero modules satisfy the same cokernel argument. -/
theorem affine_formalQuotient_comparison
    {X : Scheme.{u}} [IsAffine X] (J : X.IdealSheafData)
    (M : ModuleCat.{u} Γ(X, ⊤)) (n : ℕ) (hn : 0 < n) :
    let A := Γ(X, ⊤)
    let I := J.ideal ⟨⊤, isAffineOpen_top X⟩
    let L := tilde.functor A ⋙ Scheme.Modules.pullback X.isoSpec.hom
    ∃ e : formalModuleQuotient J n (L.obj M) ≅
        L.obj (ModuleCat.of A (M ⧸ (I ^ n • (⊤ : Submodule A M)))),
      formalModuleQuotientπ J n (L.obj M) ≫ e.hom =
        L.map (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).mkQ) := by
  classical
  dsimp only
  let A := Γ(X, ⊤)
  let f := X.isoSpec.hom
  let JY := J.comap X.isoSpec.inv
  have hf : X.isoSpec.inv.appTop = (Scheme.ΓSpecIso A).inv := by
    apply (cancel_mono X.isoSpec.hom.appTop).1
    rw [← Scheme.Hom.comp_appTop, X.isoSpec.hom_inv_id, Scheme.Hom.id_appTop]
    change 𝟙 _ = (Scheme.ΓSpecIso A).inv ≫ X.toSpecΓ.appTop
    rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id]
  have hJY : JY = Scheme.IdealSheafData.ofIdealTop
      ((J.ideal ⟨⊤, isAffineOpen_top X⟩).map (Scheme.ΓSpecIso A).inv.hom) := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    rw [Scheme.IdealSheafData.ideal_top_ofIdealTop,
      Scheme.IdealSheafData.ideal_top_comap_of_isAffine, hf]
  have hJ : JY.comap f = J := by
    dsimp [JY, f]
    rw [← Scheme.IdealSheafData.comap_comp, X.isoSpec.hom_inv_id,
      Scheme.IdealSheafData.comap_id]
  let T := tilde.functor A
  let P := Scheme.Modules.pullback f
  let B := Scheme.Modules.tensorPullback f
  let θ : B ≅ P :=
    (Scheme.Modules.nonempty_tensorPullbackAdjunction f).some.leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction f)
  have hM : (T.obj M).IsQuasicoherent := by
    change (tilde (R := A) M).IsQuasicoherent
    infer_instance
  obtain ⟨a, ha⟩ := spec_quotient_comparison A _ JY hJY M n hn
  have hb' := tensor_quotient_comparison f JY (T.obj M) hM n
  rw [hJ] at hb'
  obtain ⟨b, hb⟩ := hb'
  let Q := quotientFunctor J n
  let e := (Q.mapIso (θ.app (T.obj M))).symm ≪≫ b ≪≫ B.mapIso a ≪≫
    θ.app (T.obj (ModuleCat.of A
      (M ⧸ (J.ideal ⟨⊤, isAffineOpen_top X⟩ ^ n • (⊤ : Submodule A M)))))
  refine ⟨e, ?_⟩
  dsimp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv]
  have hπ : formalModuleQuotientπ J n (P.obj (T.obj M)) ≫
      Q.map (θ.inv.app (T.obj M)) = θ.inv.app (T.obj M) ≫
        formalModuleQuotientπ J n (B.obj (T.obj M)) := by
    exact cokernel.π_desc _ _ _
  change formalModuleQuotientπ J n (P.obj (T.obj M)) ≫
    Q.map (θ.inv.app (T.obj M)) ≫ b.hom ≫ B.map a.hom ≫
      θ.hom.app (T.obj (ModuleCat.of A
        (M ⧸ (J.ideal ⟨⊤, isAffineOpen_top X⟩ ^ n • (⊤ : Submodule A M))))) = _
  let m : M ⟶ ModuleCat.of A
      (M ⧸ (J.ideal ⟨⊤, isAffineOpen_top X⟩ ^ n • (⊤ : Submodule A M))) :=
    ModuleCat.ofHom (J.ideal ⟨⊤, isAffineOpen_top X⟩ ^ n • (⊤ : Submodule A M)).mkQ
  have hθ : B.map (T.map m) ≫ θ.hom.app _ = θ.hom.app (T.obj M) ≫ P.map (T.map m) :=
    θ.hom.naturality (T.map m)
  have hba : formalModuleQuotientπ J n (B.obj (T.obj M)) ≫
      b.hom ≫ B.map a.hom = B.map (T.map m) := by
    calc
      _ = B.map (formalModuleQuotientπ JY n (T.obj M)) ≫ B.map a.hom := by
        rw [← Category.assoc]
        exact congrArg (· ≫ B.map a.hom) hb
      _ = B.map (formalModuleQuotientπ JY n (T.obj M) ≫ a.hom) :=
        (B.map_comp _ _).symm
      _ = B.map (T.map m) := congrArg B.map ha
  calc
    _ = (formalModuleQuotientπ J n (P.obj (T.obj M)) ≫
        Q.map (θ.inv.app (T.obj M))) ≫ b.hom ≫ B.map a.hom ≫ θ.hom.app _ := by
      simp only [Category.assoc]
      rfl
    _ = (θ.inv.app (T.obj M) ≫ formalModuleQuotientπ J n (B.obj (T.obj M))) ≫
        b.hom ≫ B.map a.hom ≫ θ.hom.app _ :=
      congrArg (· ≫ b.hom ≫ B.map a.hom ≫ θ.hom.app _) hπ
    _ = θ.inv.app (T.obj M) ≫ B.map (T.map m) ≫ θ.hom.app _ := by
      simpa only [Category.assoc] using
        congrArg (θ.inv.app (T.obj M) ≫ · ≫ θ.hom.app _) hba
    _ = θ.inv.app (T.obj M) ≫ θ.hom.app (T.obj M) ≫ P.map (T.map m) :=
      congrArg (θ.inv.app (T.obj M) ≫ ·) hθ
    _ = P.map (T.map m) := by
      rw [← Category.assoc, θ.inv_hom_id_app, Category.id_comp]

end AlgebraicGeometry
