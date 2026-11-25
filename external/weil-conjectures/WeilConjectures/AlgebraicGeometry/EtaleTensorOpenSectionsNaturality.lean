/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique

/-! # Canonical open-section comparisons and restriction compatibility

Source: Stacks Project, Tags 03DR, 0095 and 0096.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- The canonical tensor-to-restriction comparison on the whole open subscheme.
Source: Stacks, Tags 0095 and 0096; uniqueness of left adjoints and
Mathlib `restrictAppIso` (blueprint: new-etale-tensor-open-section-iso). -/
def tensorOpenSectionIso (X : Scheme.{u}) (F : X.Modules) (U : X.Opens) :
    Γ((tensorPullback U.ι).obj F, ⊤) ≅ Γ(F, U) :=
  ((CategoryTheory.evaluation _ AddCommGrpCat).obj (op ⊤)).mapIso
      ((toPresheaf U.toScheme).mapIso
        (((Classical.choose (exists_tensorPullbackAdjunction U.ι)).leftAdjointUniq
          (restrictAdjunction U.ι)).app F)) ≪≫
    F.restrictAppIso U.ι ⊤ ≪≫
    F.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

/-- Transport the canonical open-section comparison along the equality of
underlying over-scheme objects. No section is chosen from an existence assertion.
Source: Stacks, Tag 03DR (blueprint: new-etale-tensor-open-section-iso). -/
def etaleTensorOpenSectionIso (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor) (F : X.Modules)
    (U : X.Opensᵒᵖ) :
    (i.op ⋙ etaleTensorSectionsPresheaf F).obj U ≅
      (F.presheafModuleCat ⋙ forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).obj U :=
  eqToIso (congrArg (fun T : Over X ↦ Γ((tensorPullback T.hom).obj F, ⊤))
      (congrArg (fun k : X.Opens ⥤ Over X ↦ k.obj U.unop) hi)) ≪≫
    tensorOpenSectionIso X F U.unop

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem restrictionComp_unit {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    [IsOpenImmersion a] [IsOpenImmersion b] (F : C.Modules) :
    ((restrictAdjunction b).comp (restrictAdjunction a)).unit.app F ≫
        (pushforwardComp a b).hom.app _ =
      (restrictAdjunction (a ≫ b)).unit.app F ≫
        (pushforward (a ≫ b)).map ((restrictFunctorComp a b).hom.app F) := by
  apply hom_ext
  intro W
  simp only [Adjunction.comp_unit_app, Hom.comp_app, pushforward_map_app,
    restrictAdjunction_unit_app_app, pushforwardComp_hom_app_app,
    restrictFunctorComp_hom_app_app]
  change F.presheaf.map _ ≫ F.presheaf.map _ = F.presheaf.map _ ≫ F.presheaf.map _
  rw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
  congr 1

private theorem restrictionComp_conjugate {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) [IsOpenImmersion a] [IsOpenImmersion b] :
    conjugateEquiv ((restrictAdjunction b).comp (restrictAdjunction a))
        (restrictAdjunction (a ≫ b)) (restrictFunctorComp a b).hom =
      (pushforwardComp a b).hom := by
  apply (conjugateEquiv ((restrictAdjunction b).comp (restrictAdjunction a))
    (restrictAdjunction (a ≫ b))).symm.injective
  rw [Equiv.symm_apply_apply]
  apply NatTrans.ext
  funext F
  apply ((restrictAdjunction (a ≫ b)).homEquiv F _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact (restrictionComp_unit a b F).symm.trans
    (unit_conjugateEquiv_symm ((restrictAdjunction b).comp (restrictAdjunction a))
      (restrictAdjunction (a ≫ b)) (pushforwardComp a b).hom F)

private def openComparison {A B : Scheme.{u}} (f : A ⟶ B) [IsOpenImmersion f] :
    tensorPullback f ≅ restrictFunctor f :=
  (Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
    (restrictAdjunction f)

private theorem openComparison_comp_inv {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    [IsOpenImmersion a] [IsOpenImmersion b] :
    (openComparison (a ≫ b)).inv ≫ (tensorSectionsComp a b).inv =
      (restrictFunctorComp a b).hom ≫
        Functor.whiskerLeft (restrictFunctor b) (openComparison a).inv ≫
        Functor.whiskerRight (openComparison b).inv (tensorPullback a) := by
  apply (conjugateEquiv
    ((Classical.choose (exists_tensorPullbackAdjunction b)).comp
      (Classical.choose (exists_tensorPullbackAdjunction a)))
    (restrictAdjunction (a ≫ b))).injective
  rw [← conjugateEquiv_comp _ (Classical.choose (exists_tensorPullbackAdjunction (a ≫ b))),
    ← conjugateEquiv_comp _ ((restrictAdjunction b).comp (restrictAdjunction a)),
    ← conjugateEquiv_comp _
      ((restrictAdjunction b).comp (Classical.choose (exists_tensorPullbackAdjunction a)))]
  simp only [openComparison, conjugateEquiv_leftAdjointUniq_inv,
    conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight, Category.comp_id,
    restrictionComp_conjugate]
  change (conjugateEquiv
    ((Classical.choose (exists_tensorPullbackAdjunction b)).comp
      (Classical.choose (exists_tensorPullbackAdjunction a)))
    (Classical.choose (exists_tensorPullbackAdjunction (a ≫ b))))
      ((conjugateEquiv
        ((Classical.choose (exists_tensorPullbackAdjunction b)).comp
          (Classical.choose (exists_tensorPullbackAdjunction a)))
        (Classical.choose (exists_tensorPullbackAdjunction (a ≫ b)))).symm
        (pushforwardComp a b).hom) = _
  rw [Equiv.apply_symm_apply]
  erw [Functor.whiskerLeft_id, Functor.whiskerRight_id, Category.id_comp]

private theorem openComparison_comp {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    [IsOpenImmersion a] [IsOpenImmersion b] :
    (tensorSectionsComp a b).hom ≫ (openComparison (a ≫ b)).hom =
      Functor.whiskerRight (openComparison b).hom (tensorPullback a) ≫
        Functor.whiskerLeft (restrictFunctor b) (openComparison a).hom ≫
        (restrictFunctorComp a b).inv := by
  have h : tensorSectionsComp a b ≪≫ openComparison (a ≫ b) =
      Functor.isoWhiskerRight (openComparison b) (tensorPullback a) ≪≫
        Functor.isoWhiskerLeft (restrictFunctor b) (openComparison a) ≪≫
        (restrictFunctorComp a b).symm := by
    apply Iso.ext_inv
    exact openComparison_comp_inv a b
  exact congrArg Iso.hom h

private theorem openComparison_unit {A B : Scheme.{u}} (a : A ⟶ B)
    [IsOpenImmersion a] (G : B.Modules) (s : Γ(G, ⊤)) :
    ((openComparison a).hom.app G).app ⊤ (tensorSectionsUnit a G s) =
      ((restrictAdjunction a).unit.app G).app ⊤ s := by
  have hi : (homOfLE a.preimage_top.ge).op =
      𝟙 (op (⊤ : TopologicalSpace.Opens A)) := rfl
  unfold tensorSectionsUnit
  erw [hi, ((tensorPullback a).obj G).presheaf.map_id, Category.comp_id]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Classical.choose (exists_tensorPullbackAdjunction a)) (restrictAdjunction a) G
  have hs := congrArg (fun φ ↦ φ.app ⊤ s) hu
  simp only [Hom.comp_app, pushforward_map_app, ConcreteCategory.comp_apply] at hs
  exact hs

private theorem openComparison_section {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    [IsOpenImmersion a] [IsOpenImmersion b]
    (F : C.Modules) (s : Γ((tensorPullback b).obj F, ⊤)) :
    ((openComparison (a ≫ b)).hom.app F).app ⊤
        (((tensorSectionsComp a b).hom.app F).app ⊤
          (tensorSectionsUnit a ((tensorPullback b).obj F) s)) =
      ((restrictFunctorComp a b).inv.app F).app ⊤
        (((restrictAdjunction a).unit.app ((restrictFunctor b).obj F)).app ⊤
          (((openComparison b).hom.app F).app ⊤ s)) := by
  have hc := congrArg (fun φ ↦ (φ.app F).app ⊤
      (tensorSectionsUnit a ((tensorPullback b).obj F) s)) (openComparison_comp a b)
  simp only [NatTrans.comp_app, Hom.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, ConcreteCategory.comp_apply] at hc
  rw [hc]
  have hn := congrArg (fun φ ↦ φ.app ⊤ s)
    ((Classical.choose (exists_tensorPullbackAdjunction a)).unit.naturality
      ((openComparison b).hom.app F))
  have hi : (homOfLE a.preimage_top.ge).op =
      𝟙 (op (⊤ : TopologicalSpace.Opens A)) := rfl
  have hn' : ((tensorPullback a).map ((openComparison b).hom.app F)).app ⊤
        (tensorSectionsUnit a ((tensorPullback b).obj F) s) =
      tensorSectionsUnit a ((restrictFunctor b).obj F)
        (((openComparison b).hom.app F).app ⊤ s) := by
    unfold tensorSectionsUnit
    erw [hi, ((tensorPullback a).obj ((tensorPullback b).obj F)).presheaf.map_id,
      ((tensorPullback a).obj ((restrictFunctor b).obj F)).presheaf.map_id,
      Category.comp_id, Category.comp_id]
    simp only [Functor.id_map, Functor.comp_map, Hom.comp_app,
      pushforward_map_app, ConcreteCategory.comp_apply] at hn
    exact hn.symm
  exact congrArg (((restrictFunctorComp a b).inv.app F).app ⊤)
    ((congrArg (((openComparison a).hom.app ((restrictFunctor b).obj F)).app ⊤)
      hn').trans (openComparison_unit a ((restrictFunctor b).obj F)
        (((openComparison b).hom.app F).app ⊤ s)))

private theorem ordinaryRestriction_section {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) [IsOpenImmersion a] [IsOpenImmersion b]
    (F : C.Modules) (t : Γ(F, b ''ᵁ ⊤)) :
    F.presheaf.map (eqToHom (show (a ≫ b) ''ᵁ ⊤ =
        b ''ᵁ (a ''ᵁ a ⁻¹ᵁ ⊤) by simp)).op
      (F.presheaf.map (b.opensFunctor.map (homOfLE (a.image_preimage_le ⊤))).op t) =
    F.presheaf.map (homOfLE (show (a ≫ b) ''ᵁ ⊤ ≤ b ''ᵁ ⊤ by
      simpa only [Scheme.Hom.comp_image] using
        b.image_mono (show a ''ᵁ ⊤ ≤ ⊤ from le_top))).op t := by
  rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
  congr 2

-- Keep the tensor construction folded while comparing section maps.
attribute [local irreducible] tensorPullback tensorPullbackObj
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem openComparison_restriction {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (c : A ⟶ C) [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c]
    (h : a ≫ b = c) (F : C.Modules) :
    (tensorSectionsUnit a ((tensorPullback b).obj F) ≫
      ((tensorSectionsComp a b).hom.app F).app ⊤ ≫
      (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj F) h)).app ⊤) ≫
        ((openComparison c).hom.app F).app ⊤ =
      ((openComparison b).hom.app F).app ⊤ ≫
        F.presheaf.map (homOfLE (show c ''ᵁ ⊤ ≤ b ''ᵁ ⊤ by
          subst c
          simpa only [Scheme.Hom.comp_image] using
            b.image_mono (show a ''ᵁ ⊤ ≤ ⊤ from le_top))).op := by
  subst c
  simp only [eqToHom_refl, Hom.id_app, Category.comp_id]
  apply ConcreteCategory.hom_ext
  intro s
  simp only [ConcreteCategory.comp_apply]
  refine (openComparison_section a b F s).trans ?_
  simp only [restrictFunctorComp_inv_app_app, restrictAdjunction_unit_app_app, restrict_map]
  exact ordinaryRestriction_section a b F
    (((openComparison b).hom.app F).app ⊤ s)


private theorem tensorOpenSectionIso_hom (X : Scheme.{u}) (F : X.Modules)
    (U : X.Opens) :
    (tensorOpenSectionIso X F U).hom = ((openComparison U.ι).hom.app F).app ⊤ ≫
      F.presheaf.map (eqToHom U.ι_image_top.symm).op := by
  rfl

private theorem openSections_naturality (X : Scheme.{u}) (F : X.Modules)
    (U V : X.Opens) (h : V ≤ U) :
    (tensorSectionsUnit (X.homOfLE h) ((tensorPullback U.ι).obj F) ≫
      ((tensorSectionsComp (X.homOfLE h) U.ι).hom.app F).app ⊤ ≫
      (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj F)
        (X.homOfLE_ι h))).app ⊤) ≫ (tensorOpenSectionIso X F V).hom =
      (tensorOpenSectionIso X F U).hom ≫ F.presheaf.map (homOfLE h).op := by
  conv_lhs =>
    rhs
    rw [tensorOpenSectionIso_hom X F V]
  conv_rhs =>
    lhs
    rw [tensorOpenSectionIso_hom X F U]
  have hr := openComparison_restriction (X.homOfLE h) U.ι V.ι (X.homOfLE_ι h) F
  have hs := congrArg (fun φ ↦ φ ≫ F.presheaf.map (eqToHom V.ι_image_top.symm).op) hr
  have hm :
      F.presheaf.map (homOfLE (show V.ι ''ᵁ ⊤ ≤ U.ι ''ᵁ ⊤ by
        simpa only [V.ι_image_top, U.ι_image_top] using h)).op ≫
        F.presheaf.map (eqToHom V.ι_image_top.symm).op =
      F.presheaf.map (eqToHom U.ι_image_top.symm).op ≫ F.presheaf.map (homOfLE h).op := by
    rw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
    congr 1
  conv_rhs at hs => erw [Category.assoc, hm]
  exact (Category.assoc _ _ _).symm.trans (hs.trans (Category.assoc _ _ _).symm)

private theorem overSections_naturality (X : Scheme.{u}) (F : X.Modules)
    (U V : X.Opens) (f : V ⟶ U) (A B : Over X) (g : B ⟶ A)
    (hA : A = X.restrictFunctor.obj U) (hB : B = X.restrictFunctor.obj V) :
    (tensorSectionsUnit g.left ((tensorPullback A.hom).obj F) ≫
      ((tensorSectionsComp g.left A.hom).hom.app F).app ⊤ ≫
      (eqToHom (congrArg (fun a ↦ (tensorPullback a).obj F) g.w)).app ⊤) ≫
        eqToHom (congrArg (fun T : Over X ↦ Γ((tensorPullback T.hom).obj F, ⊤)) hB) ≫
        (tensorOpenSectionIso X F V).hom =
      eqToHom (congrArg (fun T : Over X ↦ Γ((tensorPullback T.hom).obj F, ⊤)) hA) ≫
        (tensorOpenSectionIso X F U).hom ≫ F.presheaf.map f.op := by
  cases hA
  cases hB
  have hg : g = X.restrictFunctor.map f := by
    ext1
    change g.left = X.homOfLE f.le
    apply (cancel_mono U.ι).mp
    exact g.w.trans (X.homOfLE_ι f.le).symm
  subst g
  simp only [eqToHom_refl, Category.id_comp]
  exact openSections_naturality X F U V f.le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The constructed comparisons commute with the unit-normalized tensor restrictions.
Source: Stacks, Tag 03DR, equation (35.8.0.1), and Tags 0095 and 0096.
(blueprint: new-etale-tensor-open-section-naturality).

Proof: First use hi on objects and arrows to replace the underlying objects i(U)
by the inclusions U.ι and each underlying arrow by the inclusion between opens.
Write a for the inclusion V into U and b for U.ι. Let e_b be the unique comparison
from tensor pullback to restriction defined by leftAdjointUniq. Its unit equation
is η_b followed by b_* e_b = the restriction-adjunction unit. The composition
comparison c_{a,b} is the mate of the inverse pushforward-composition isomorphism.
Its unit equation identifies η_b followed by b_* η_a and the pushforward of
c_{a,b} with η_{a≫b}, after the pushforward composition identification.
Combine these equations: section pullback along a, followed by c_{a,b} and e_{a≫b},
is e_b followed by the restriction unit along a and the restriction-composition
comparison. Equality follows by injectivity of the adjunction Hom equivalence;
both mates are the same composite restriction unit. Evaluate at the whole source
open. Mathlib restrictAdjunction_unit_app_app expresses the restriction unit as
the ordinary presheaf restriction, while restrictAppIso identifies the whole-open
sections with F(U) and F(V). The transports of image-top and a≫b=V.ι commute with
these maps by functoriality of F.presheaf. This gives the displayed square. Empty
opens, identity inclusions, and zero modules obey the same unit equations. -/
/- Core comparison compatibility after expanding the constructed isomorphisms.
Source: Stacks, Tag 03DR, equation (35.8.0.1) (blueprint: new-etale-tensor-open-section-core).
-/
theorem etaleTensorOpenSectionIso_component_core
    (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor) (F : X.Modules)
    {U V : X.Opensᵒᵖ} (f : U ⟶ V) :
    (i.op ⋙ etaleTensorSectionsPresheaf F).map f ≫
        (eqToIso (congrArg (fun T : Over X ↦ Γ((tensorPullback T.hom).obj F, ⊤))
          (congrArg (fun k : X.Opens ⥤ Over X ↦ k.obj V.unop) hi))).hom ≫
        (tensorOpenSectionIso X F V.unop).hom =
      (eqToIso (congrArg (fun T : Over X ↦ Γ((tensorPullback T.hom).obj F, ⊤))
          (congrArg (fun k : X.Opens ⥤ Over X ↦ k.obj U.unop) hi))).hom ≫
        (tensorOpenSectionIso X F U.unop).hom ≫
        (F.presheafModuleCat ⋙ forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).map f := by
  exact overSections_naturality X F U.unop V.unop f.unop
    ((i ⋙ Scheme.Etale.forget X).obj U.unop)
    ((i ⋙ Scheme.Etale.forget X).obj V.unop)
    ((i ⋙ Scheme.Etale.forget X).map f.unop)
    (congrArg (fun k : X.Opens ⥤ Over X ↦ k.obj U.unop) hi)
    (congrArg (fun k : X.Opens ⥤ Over X ↦ k.obj V.unop) hi)

/-- (blueprint: new-etale-tensor-open-section-naturality) -/
theorem etaleTensorOpenSectionIso_naturality
    (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor) (F : X.Modules)
    {U V : X.Opensᵒᵖ} (f : U ⟶ V) :
    (i.op ⋙ etaleTensorSectionsPresheaf F).map f ≫
        (etaleTensorOpenSectionIso X i hi F V).hom =
      (etaleTensorOpenSectionIso X i hi F U).hom ≫
        (F.presheafModuleCat ⋙ forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).map f := by
  simpa [etaleTensorOpenSectionIso] using
    etaleTensorOpenSectionIso_component_core X i hi F f

end
end AlgebraicGeometry.Scheme.Modules
