/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Sites.Adjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian

/-!
# Internal group objects and the abelian direct image

Source: Stacks Project, Section 00YR and Proposition 00YV, proof of (2).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Source: Stacks Project, Section 00YR and Proposition 00YV, proof of (2).
(blueprint: lem-weil-pbc-etale-abelian-direct-image-internal)

Proof: At each site take the sectionwise identification of abelian sheaves with
internal commutative group objects from `sheavesAlgebraicStructuresAbelian`.
The forward functor uses addition, zero and negation as multiplication, unit and
inverse; its inverse recovers the sectionwise abelian groups and homomorphisms.
The strict inverse identities give equivalences eV and eU, and the underlying
functor identities give iV and iU. The set direct image is precomposition along
base change. Its product comparison is the sectionwise pairing map, and its
terminal comparison is the unique map of singleton sheaves. Consequently the
operations on the image under R.mapCommGrp are exactly the operations of the
original abelian sheaf evaluated at the base-changed object. For each F the underlying
map of β is R.map (iU.hom.app F) followed by iV.inv.app (f_* F). The section
formulas for the two identifications show that this map preserves addition and
zero. The inverse uses iV.hom followed by R.map iU.inv and preserves the same
operations; preservation of negation follows from the group laws. These maps
are inverse because iU and iV are isomorphisms. Naturality follows from the
naturality of iU and iV and the sectionwise formula for direct image on morphisms;
faithfulness of CommGrp.forget gives the group-object naturality equation.
Composing the formula for β with iV.hom cancels iV.inv and gives the displayed
equation.
This argument uses no inverse image and no finite-limit assumption on it. -/
theorem etaleAbelianDirectImageInternal (U V : Scheme.{u}) (f : U ⟶ V) :
    let R : Sheaf U.smallEtaleTopology (Type (u + 1)) ⥤
        Sheaf V.smallEtaleTopology (Type (u + 1)) :=
      (MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
      (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
      (U.smallGrothendieckTopology @Etale)
    letI : R.Braided := Functor.Braided.ofChosenFiniteProducts R
    ∃ (eV : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1} ≌
          CommGrp (Sheaf V.smallEtaleTopology (Type (u + 1))))
      (eU : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1} ≌
          CommGrp (Sheaf U.smallEtaleTopology (Type (u + 1))))
      (iV : eV.functor ⋙ CommGrp.forget _ ≅
        sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology)
      (iU : eU.functor ⋙ CommGrp.forget _ ≅
        sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology)
      (β : eU.functor ⋙ R.mapCommGrp ≅
        Etale.lowerStar AddCommGrpCat.{u + 1} f ⋙ eV.functor),
      ∀ F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1},
        (CommGrp.forget _).map (β.hom.app F) ≫
            iV.hom.app ((Etale.lowerStar AddCommGrpCat.{u + 1} f).obj F) =
          R.map (iU.hom.app F) := by
  dsimp only
  let R := (MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
    (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
    (U.smallGrothendieckTopology @Etale)
  let : R.Braided := Functor.Braided.ofChosenFiniteProducts R
  let Ra := Etale.lowerStar AddCommGrpCat.{u + 1} f
  obtain ⟨FV, GV, hFV, _, hFGV, hGFV, hsecV, _⟩ :=
    sheavesAlgebraicStructuresAbelian.{u + 1, u, u + 1} V.smallEtaleTopology
  obtain ⟨FU, GU, hFU, _, hFGU, hGFU, hsecU, _⟩ :=
    sheavesAlgebraicStructuresAbelian.{u + 1, u, u + 1} U.smallEtaleTopology
  let eV := CategoryTheory.Equivalence.mk FV GV (eqToIso hFGV).symm (eqToIso hGFV)
  let eU := CategoryTheory.Equivalence.mk FU GU (eqToIso hFGU).symm (eqToIso hGFU)
  let iV := eqToIso hFV
  let iU := eqToIso hFU
  let c (A : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) :
      (R.mapCommGrp.obj (FU.obj A)).X ≅ (FV.obj (Ra.obj A)).X :=
    R.mapIso (iU.app A) ≪≫ (iV.app (Ra.obj A)).symm
  have hμ (X Y : Sheaf U.smallEtaleTopology (Type (u + 1))) :
      Functor.LaxMonoidal.μ R X Y = 𝟙 (R.obj (MonoidalCategory.tensorObj X Y)) := by
    apply CartesianMonoidalCategory.hom_ext (X := R.obj X) (Y := R.obj Y)
    · exact Functor.Monoidal.μ_fst R X Y
    · exact Functor.Monoidal.μ_snd R X Y
  have hc (A : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) :
      IsMonHom (c A).hom := by
    constructor
    · apply (cancel_mono (iV.hom.app (Ra.obj A))).1
      dsimp only [c, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app]
      simp only [Category.assoc, iV.inv_hom_id_app]
      ext W t
      change (iU.hom.app A).hom.app _
          ((MonObj.one (X := (FU.obj A).X)).hom.app _
            ((Functor.LaxMonoidal.ε R).hom.app W t)) =
        (iV.hom.app (Ra.obj A)).hom.app W
          ((MonObj.one (X := (FV.obj (Ra.obj A)).X)).hom.app W t)
      exact (hsecU A _).2.1 _ |>.trans ((hsecV (Ra.obj A) W).2.1 t).symm
    · apply (cancel_mono (iV.hom.app (Ra.obj A))).1
      dsimp only [c, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app]
      simp only [Category.assoc, iV.inv_hom_id_app]
      change (Functor.LaxMonoidal.μ R _ _ ≫ R.map (MonObj.mul (X := (FU.obj A).X))) ≫
          R.map (iU.hom.app A) ≫ 𝟙 _ = _
      erw [hμ, Category.id_comp, Category.comp_id]
      ext W ab
      change (iU.hom.app A).hom.app _
          ((MonObj.mul (X := (FU.obj A).X)).hom.app _ ab) =
        (iV.hom.app (Ra.obj A)).hom.app W
          ((MonObj.mul (X := (FV.obj (Ra.obj A)).X)).hom.app W
            (((c A).hom.hom.app W ab.1), ((c A).hom.hom.app W ab.2)))
      erw [← (Prod.mk.eta (p := ab))]
      erw [(hsecU A _).1 ab.1 ab.2,
        (hsecV (Ra.obj A) W).1 ((c A).hom.hom.app W ab.1) ((c A).hom.hom.app W ab.2)]
      have he (a : (R.obj (FU.obj A).X).obj.obj W) :
          (iV.hom.app (Ra.obj A)).hom.app W ((c A).hom.hom.app W a) =
            (iU.hom.app A).hom.app _ a := by
        have hh : (c A).hom ≫ iV.hom.app (Ra.obj A) = R.map (iU.hom.app A) := by
          dsimp only [c, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app]
          erw [Category.assoc, iV.inv_hom_id_app, Category.comp_id]
        exact congrArg (fun k ↦ k.hom.app W a) hh
      erw [he ab.1, he ab.2]
  let β : FU ⋙ R.mapCommGrp ≅ Ra ⋙ FV := NatIso.ofComponents
    (fun A ↦ @CommGrp.mkIso' _ _ _ _ _ _ (c A) _ _ _ _ (hc A)) (by
      intro A B g
      apply (CommGrp.forget _).map_injective
      change R.map ((CommGrp.forget _).map (FU.map g)) ≫ (c B).hom =
        (c A).hom ≫ (CommGrp.forget _).map (FV.map (Ra.map g))
      dsimp [c]
      simp only [Category.assoc]
      have hn := iU.hom.naturality g
      change (CommGrp.forget _).map (FU.map g) ≫ iU.hom.app B =
        iU.hom.app A ≫ (sheafForget U.smallEtaleTopology).map g at hn
      erw [← Category.assoc, ← R.map_comp, hn, R.map_comp]
      erw [Category.assoc]
      congr 1
      exact iV.inv.naturality (Ra.map g))
  refine ⟨eV, eU, iV, iU, β, ?_⟩
  intro A
  change (c A).hom ≫ iV.hom.app (Ra.obj A) = R.map (iU.hom.app A)
  dsimp only [c, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app]
  erw [Category.assoc, iV.inv_hom_id_app, Category.comp_id]

end AlgebraicGeometry
