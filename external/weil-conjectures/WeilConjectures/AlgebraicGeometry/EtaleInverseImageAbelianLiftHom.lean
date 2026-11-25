/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.EtaleAbelianDirectImageInternal
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Unique

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Source: Stacks Project, Sites and Sheaves, Proposition 00YV.
(blueprint: lem-weil-pbc-etale-inverse-image-abelian-lift-hom)

Proof: Use `sheaves_algebraicStructures_objects` to identify abelian sheaves
with internal commutative group objects on both sites, with their sectionwise
operations. Finite-limit preservation of L implies finite-product preservation.
Apply `Adjunction.liftsGroupRingObjects` to the set adjunction a. Transport the
resulting group-object adjunction through those identifications. Its right adjoint
is the abelian direct image: on each base-changed object it has the original
sections, operations and restrictions, so its underlying comparison with the set
direct image is the identity. The lift's hom-set equation therefore compares the
forgotten abelian adjunct with the set adjunct of its underlying comparison.

The transported left adjoint and `Etale.upperStar` are both left adjoint to this
same abelian direct image. Choose their comparison by `Adjunction.leftAdjointUniq`,
which intertwines the two adjunction bijections. Forget that comparison and compose
it with the lift's underlying isomorphism to obtain ea. Substitution in the lifted
hom-set equation gives exactly the displayed equation for every G, F and h. -/
theorem etaleInverseImageAbelianLift_hom (U V : Scheme.{u}) (f : U ⟶ V)
    (hL : PreservesFiniteLimits (Scheme.etaleSetPullback f)) :
    let b := MorphismProperty.Over.pullback @Etale ⊤ f
    let L := Scheme.etaleSetPullback f
    let La := Etale.upperStar AddCommGrpCat.{u + 1} f
    let FaU := sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology
    let FaV := sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology
    let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
      (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
      (U.smallGrothendieckTopology @Etale)
    ∃ (ea : La ⋙ FaU ≅ FaV ⋙ L),
        (∀ (G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
            (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (h : La.obj G ⟶ F),
          FaV.map ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
            G F h) =
              a.homEquiv (FaV.obj G) (FaU.obj F) (ea.inv.app G ≫ FaU.map h)) := by
  classical
  dsimp only
  let b := MorphismProperty.Over.pullback @Etale ⊤ f
  let L := Scheme.etaleSetPullback f
  let R : Sheaf U.smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf V.smallEtaleTopology (Type (u + 1)) := b.sheafPushforwardContinuous (Type (u + 1))
    (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
  let FaV := sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology
  let FaU := sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology
  let Ra := Etale.lowerStar AddCommGrpCat.{u + 1} f
  let a : L ⊣ R := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
    (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
    (U.smallGrothendieckTopology @Etale)
  let : PreservesFiniteLimits L := hL
  let : L.Braided := Functor.Braided.ofChosenFiniteProducts L
  let : R.Braided := Functor.Braided.ofChosenFiniteProducts R
  obtain ⟨eV, eU, iV, iU, β, hβ⟩ := etaleAbelianDirectImageInternal U V f
  let Lt := (eV.functor ⋙ L.mapCommGrp) ⋙ eU.inverse
  let q : eV.functor ⋙ L.mapCommGrp ≅ Lt ⋙ eU.functor :=
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft (eV.functor ⋙ L.mapCommGrp) eU.counitIso.symm ≪≫
      (Functor.associator _ _ _).symm
  let aLift : Lt ⊣ Ra := a.mapCommGrp.restrictFullyFaithful
    eV.fullyFaithfulFunctor eU.fullyFaithfulFunctor q β
  let γ : Lt ⋙ FaU ≅ FaV ⋙ L :=
    Functor.isoWhiskerLeft Lt iU.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight q.symm (CommGrp.forget _) ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft eV.functor (eqToIso (by rfl)) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight iV L
  let aa := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  let e := aa.leftAdjointUniq aLift
  refine ⟨Functor.isoWhiskerRight e FaU ≪≫ γ, ?_⟩
  intro G F h
  have ht : FaV.map (aLift.homEquiv G F (e.inv.app G ≫ h)) =
      a.homEquiv (FaV.obj G) (FaU.obj F)
        (γ.inv.app G ≫ FaU.map (e.inv.app G ≫ h)) := by
    let t := e.inv.app G ≫ h
    have hm : eV.functor.map (aLift.homEquiv G F t) =
        (a.mapCommGrp.homEquiv (eV.functor.obj G) (eU.functor.obj F))
          (q.hom.app G ≫ eU.functor.map t) ≫ β.hom.app F := by
      dsimp only [aLift]
      rw [Adjunction.restrictFullyFaithful_homEquiv_apply]
      simp only [Functor.FullyFaithful.map_preimage, Adjunction.homEquiv_unit,
        Functor.map_comp, Category.assoc]
    have hf : (CommGrp.forget _).map
        ((a.mapCommGrp.homEquiv (eV.functor.obj G) (eU.functor.obj F))
          (q.hom.app G ≫ eU.functor.map t)) =
        a.homEquiv (eV.functor.obj G).X (eU.functor.obj F).X
          ((CommGrp.forget _).map (q.hom.app G ≫ eU.functor.map t)) := by
      rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
      change (𝟙 _ ≫ a.unit.app _ ≫ 𝟙 _) ≫ R.map _ = _
      simp only [Category.id_comp, Category.comp_id]
      rfl
    have hi := iV.hom.naturality (aLift.homEquiv G F t)
    dsimp only [Functor.comp_map] at hi
    have hb : (CommGrp.forget (Sheaf V.smallEtaleTopology (Type (u + 1)))).map
        (β.hom.app F) ≫ iV.hom.app (Ra.obj F) = R.map (iU.hom.app F) := hβ F
    rw [← cancel_epi (iV.hom.app G), ← hi, hm, Functor.map_comp,
      Category.assoc, hb, hf]
    let x : L.obj (eV.functor.obj G).X ⟶ (eU.functor.obj F).X :=
      (CommGrp.forget _).map (q.hom.app G ≫ eU.functor.map t)
    change a.homEquiv _ _ x ≫ R.map (iU.hom.app F) =
      iV.hom.app G ≫ a.homEquiv _ _ (γ.inv.app G ≫ FaU.map t)
    rw [← a.homEquiv_naturality_right x (iU.hom.app F)]
    rw [← a.homEquiv_naturality_left (iV.hom.app G) (γ.inv.app G ≫ FaU.map t)]
    congr 1
    simp only [γ, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Functor.associator_hom_app, Iso.symm_inv,
      eqToIso.inv, eqToHom_refl, Category.id_comp, Category.assoc]
    simp only [NatTrans.id_app, ← Category.assoc, ← L.map_comp,
      iV.hom_inv_id_app, L.map_id, Category.id_comp]
    simp only [x, Functor.map_comp, Category.assoc]
    exact congrArg ((CommGrp.forget _).map (q.hom.app G) ≫ ·)
      (iU.hom.naturality t)
  have he : aLift.homEquiv G F (e.inv.app G ≫ h) = aa.homEquiv G F h := by
    rw [Adjunction.homEquiv_unit, Ra.map_comp, ← Category.assoc]
    change aLift.unit.app G ≫ Ra.map ((aLift.leftAdjointUniq aa).hom.app G) ≫ _ = _
    have hu := Adjunction.unit_leftAdjointUniq_hom_app aLift aa G
    rw [← Category.assoc, hu]
    rfl
  rw [he] at ht
  change FaV.map (aa.homEquiv G F h) =
    a.homEquiv (FaV.obj G) (FaU.obj F)
      ((Functor.isoWhiskerRight e FaU ≪≫ γ).inv.app G ≫ FaU.map h)
  simpa only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, FaU.map_comp, Category.assoc] using ht

end AlgebraicGeometry
