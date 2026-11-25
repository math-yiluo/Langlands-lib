/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.AlgebraicGeometry.EtaleTensorOpenSectionsNaturality

/-! # Direct image of tensor-sections sheaves

Source: Stacks Project, Tags 03DW, 03P2 and 0733.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

attribute [local irreducible] tensorPullback tensorPullbackObj

private theorem tensorOpenSectionIso_coeff_natural
    (X : Scheme.{u}) (F G : X.Modules) (φ : F ⟶ G) (U : X.Opens) :
    ((tensorPullback U.ι).map φ).app ⊤ ≫ (tensorOpenSectionIso X G U).hom =
      (tensorOpenSectionIso X F U).hom ≫ φ.app U := by
  let k := (Classical.choose (exists_tensorPullbackAdjunction U.ι)).leftAdjointUniq
    (restrictAdjunction U.ι)
  have hn := congrArg (fun f ↦ f.app ⊤) (k.hom.naturality φ)
  change ((tensorPullback U.ι).map φ).app ⊤ ≫ (k.hom.app G).app ⊤ =
    (k.hom.app F).app ⊤ ≫ φ.app (U.ι ''ᵁ ⊤) at hn
  change ((tensorPullback U.ι).map φ).app ⊤ ≫
      (k.hom.app G).app ⊤ ≫ G.presheaf.map (eqToHom U.ι_image_top.symm).op =
    ((k.hom.app F).app ⊤ ≫ F.presheaf.map (eqToHom U.ι_image_top.symm).op) ≫ φ.app U
  have hr := ((toPresheaf X).map φ).naturality (eqToHom U.ι_image_top.symm).op
  change F.presheaf.map (eqToHom U.ι_image_top.symm).op ≫ φ.app U =
    φ.app (U.ι ''ᵁ ⊤) ≫ G.presheaf.map (eqToHom U.ι_image_top.symm).op at hr
  calc
    _ = ((tensorPullback U.ι).map φ).app ⊤ ≫ (k.hom.app G).app ⊤ ≫
        G.presheaf.map (eqToHom U.ι_image_top.symm).op := rfl
    _ = ((k.hom.app F).app ⊤ ≫ φ.app (U.ι ''ᵁ ⊤)) ≫
        G.presheaf.map (eqToHom U.ι_image_top.symm).op :=
      (Category.assoc _ _ _).symm.trans (congrArg
        (fun f ↦ f ≫ G.presheaf.map (eqToHom U.ι_image_top.symm).op) hn)
    _ = _ := (Category.assoc _ _ _).trans
      ((congrArg (fun f ↦ (k.hom.app F).app ⊤ ≫ f) hr.symm).trans
        (Category.assoc _ _ _).symm)

private theorem tensorSections_transport_natural
    {X : Scheme.{u}} (F G : X.Modules) (φ : F ⟶ G) {A B : Over X} (h : A = B) :
    ((tensorPullback A.hom).map φ).app ⊤ ≫
        (eqToIso (congrArg (fun T : Over X ↦ Γ((tensorPullback T.hom).obj G, ⊤)) h)).hom =
      (eqToIso (congrArg (fun T : Over X ↦ Γ((tensorPullback T.hom).obj F, ⊤)) h)).hom ≫
        ((tensorPullback B.hom).map φ).app ⊤ := by
  cases h
  exact (Category.comp_id _).trans (Category.id_comp _).symm

private theorem etaleTensorOpenSectionIso_coeff_natural
    (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (F G : X.Modules) (φ : F ⟶ G) (U : X.Opensᵒᵖ) :
    ((tensorPullback (i.obj U.unop).hom).map φ).app ⊤ ≫
        (etaleTensorOpenSectionIso X i hi G U).hom =
      (etaleTensorOpenSectionIso X i hi F U).hom ≫ φ.app U.unop := by
  let h := congrArg (fun k : X.Opens ⥤ Over X ↦ k.obj U.unop) hi
  let t (F : X.Modules) :=
    (eqToIso (congrArg (fun T : Over X ↦ Γ((tensorPullback T.hom).obj F, ⊤)) h)).hom
  change ((tensorPullback (i.obj U.unop).hom).map φ).app ⊤ ≫
      t G ≫ (tensorOpenSectionIso X G U.unop).hom =
    (t F ≫ (tensorOpenSectionIso X F U.unop).hom) ≫ φ.app U.unop
  have ht := tensorSections_transport_natural F G φ h
  change ((tensorPullback (i.obj U.unop).hom).map φ).app ⊤ ≫ t G =
    t F ≫ ((tensorPullback U.unop.ι).map φ).app ⊤ at ht
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f ↦ f ≫ (tensorOpenSectionIso X G U.unop).hom) ht).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f ↦ t F ≫ f)
          (tensorOpenSectionIso_coeff_natural X F G φ U.unop)).trans
            (Category.assoc _ _ _).symm)))

/-- The underlying abelian sheaf is the direct image of the tensor-sections sheaf,
naturally in the specified tensor-pullback maps.
Source: Stacks Project, Descent, Tag 03DW(2), and Etale Cohomology, Tag 03P2.
(blueprint: lem-sc-etale-tensor-direct-image-identification)

Proof: on an open W, compare restriction along W into X with tensor pullback
using uniqueness of left adjoints to module pushforward. Normalize this comparison
by the restriction and tensor adjunction units. Evaluation at the top open of W
identifies F(W) with the tensor-pullback sections. The composition unit equation
makes these identifications commute with restriction to smaller opens, so they
assemble into a sheaf isomorphism. Naturality of the left-adjoint comparison in F,
and the component formula hm, give the displayed naturality square. This also
works for the empty open and does not require X to be affine or separated. -/
theorem etaleTensorDirectImageIdentification
    (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    [i.IsContinuous (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology]
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (m : ∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent],
      (F ⟶ G) → (etaleTensorSectionsSheaf F ⟶ etaleTensorSectionsSheaf G))
    (hm : ∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
      (φ : F ⟶ G) (U : X.Etale),
      (m F G φ).hom.app (op U) = ((tensorPullback U.hom).map φ).app ⊤) :
    let T := i.sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology
    ∃ a : ∀ (F : X.Modules) [F.IsQuasicoherent],
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F) ≅
          T.obj (etaleTensorSectionsSheaf F),
      ∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G),
        (SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).map φ ≫ (a G).hom =
          (a F).hom ≫ T.map (m F G φ) := by
  classical
  let T := i.sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology
  let a (F : X.Modules) [F.IsQuasicoherent] :
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F) ≅
        T.obj (etaleTensorSectionsSheaf F) :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (NatIso.ofComponents (etaleTensorOpenSectionIso X i hi F)
        (fun f ↦ etaleTensorOpenSectionIso_naturality X i hi F f)).symm
  refine ⟨a, ?_⟩
  intro F G _ _ φ
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply (cancel_mono ((etaleTensorOpenSectionIso X i hi G U).hom)).mp
  change φ.app U.unop ≫ (etaleTensorOpenSectionIso X i hi G U).inv ≫
      (etaleTensorOpenSectionIso X i hi G U).hom =
    ((etaleTensorOpenSectionIso X i hi F U).inv ≫ (m F G φ).hom.app (op (i.obj U.unop))) ≫
      (etaleTensorOpenSectionIso X i hi G U).hom
  rw [hm F G φ]
  have hn := etaleTensorOpenSectionIso_coeff_natural X i hi F G φ U
  have hh := congrArg (fun f ↦ (etaleTensorOpenSectionIso X i hi F U).inv ≫ f) hn
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using hh.symm

end AlgebraicGeometry.Scheme.Modules
