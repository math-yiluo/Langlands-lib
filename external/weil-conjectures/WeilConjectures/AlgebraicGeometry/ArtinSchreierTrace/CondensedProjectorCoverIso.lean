/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.ArtinSchreierTraceComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-! # Transport of character-projector images under an isomorphism of covers -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ArtinSchreierTrace

attribute [local irreducible] ProEtale.CondensedRing.upperStar
  ProEtale.CondensedRing.upperStarLowerStarAdjunction

section Coherence

open MonObj

private lemma regularLift_one_hom {C : Type*} [Category* C] [MonoidalCategory C]
    {R S : C} [MonObj R] [MonObj S] (f : R ⟶ S) [IsMonHom f] :
    (Mod.regularLift ((Mod.comap f).obj (Mod.regular S)) (η[R] ≫ f)).hom = f := by
  let g : Mod.regular R ⟶ (Mod.comap f).obj (Mod.regular S) :=
    Mod.homMk f (by
      change μ[R] ≫ f = R ◁ f ≫ f ▷ S ≫ μ[S]
      rw [IsMonHom.mul_hom, tensorHom_def', Category.assoc])
  have e : Mod.regularLift ((Mod.comap f).obj (Mod.regular S)) (η[R] ≫ f) = g :=
    Mod.regular_hom_ext (Mod.one_comp_regularLift _ _)
  exact congrArg (fun t ↦ t.hom) e

private lemma coefficientLift_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y Z : Scheme.{u}} (h : Y ⟶ Z) :
    (Mod.regularLift
      ((ProEtale.CondensedRing.lowerStar Λ h).obj (condensedUnit Λ Y))
      (η ≫ ProEtale.condensedPushforwardHom Λ h)).hom =
        ProEtale.condensedPushforwardHom Λ h := by
  exact regularLift_one_hom _

private lemma pull_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} {Y Z : Over X} (h : Y ⟶ Z) :
    (condensedPull Λ h).hom =
      (ProEtale.lowerStar Ab.{u + 1} Z.hom).map
        (ProEtale.condensedPushforwardHom Λ h.left) ≫
      (ProEtale.lowerStarComp Ab.{u + 1} h.left Z.hom).hom.app
        (ProEtale.condensedRingObj Λ Y.left) ≫
      (ProEtale.lowerStarCongr Ab.{u + 1} (Over.w h)).hom.app
        (ProEtale.condensedRingObj Λ Y.left) := by
  simp only [condensedPull, Mod.comp_hom',
    ProEtale.CondensedRing.lowerStar_map_hom, coefficientLift_hom,
    ProEtale.CondensedRing.lowerStarComp_hom_app_hom,
    ProEtale.CondensedRing.lowerStarCongr_hom_app_hom]
  rfl

private lemma functionPull_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z P : Scheme.{u}}
    (f : Y ⟶ Z) (g : Z ⟶ P) (pY : Y ⟶ X) (pZ : Z ⟶ X) (pP : P ⟶ X)
    (hf : f ≫ pZ = pY) (hg : g ≫ pP = pZ) :
    (ProEtale.lowerStar Ab.{u + 1} pP).map
        (ProEtale.condensedPushforwardHom Λ (f ≫ g)) ≫
      (ProEtale.lowerStarComp Ab.{u + 1} (f ≫ g) pP).hom.app
        (ProEtale.condensedRingObj Λ Y) ≫
      (ProEtale.lowerStarCongr Ab.{u + 1}
        (show (f ≫ g) ≫ pP = pY by rw [Category.assoc, hg, hf])).hom.app
        (ProEtale.condensedRingObj Λ Y) =
    ((ProEtale.lowerStar Ab.{u + 1} pP).map
        (ProEtale.condensedPushforwardHom Λ g) ≫
      (ProEtale.lowerStarComp Ab.{u + 1} g pP).hom.app
        (ProEtale.condensedRingObj Λ Z) ≫
      (ProEtale.lowerStarCongr Ab.{u + 1} hg).hom.app
        (ProEtale.condensedRingObj Λ Z)) ≫
    (ProEtale.lowerStar Ab.{u + 1} pZ).map
        (ProEtale.condensedPushforwardHom Λ f) ≫
      (ProEtale.lowerStarComp Ab.{u + 1} f pZ).hom.app
        (ProEtale.condensedRingObj Λ Y) ≫
      (ProEtale.lowerStarCongr Ab.{u + 1} hf).hom.app
        (ProEtale.condensedRingObj Λ Y) := by
  subst pY pZ
  simp only [ProEtale.condensedPushforwardHom_comp, Functor.map_comp]
  have hc := congrArg (fun e ↦ e.hom.app (ProEtale.condensedRingObj Λ Y))
    (ProEtale.legacy_lowerStarComp_assoc Ab.{u + 1} f g pP)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.id_comp] at hc
  simp only [ProEtale.lowerStarCongr_rfl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id] at hc ⊢
  simp only [Category.assoc]
  refine (congrArg (fun t ↦
    (ProEtale.lowerStar Ab.{u + 1} pP).map (ProEtale.condensedPushforwardHom Λ g) ≫
      (ProEtale.lowerStar Ab.{u + 1} pP).map
        ((ProEtale.lowerStar Ab.{u + 1} g).map (ProEtale.condensedPushforwardHom Λ f)) ≫ t)
    hc.symm).trans ?_
  exact congrArg (fun t ↦
    (ProEtale.lowerStar Ab.{u + 1} pP).map (ProEtale.condensedPushforwardHom Λ g) ≫ t)
    ((ProEtale.lowerStarComp Ab.{u + 1} g pP).hom.naturality_assoc
      (ProEtale.condensedPushforwardHom Λ f)
      ((ProEtale.lowerStarComp Ab.{u + 1} f (g ≫ pP)).hom.app
        (ProEtale.condensedRingObj Λ Y)))

private lemma pull_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} {Y Z P : Over X}
    (f : Y ⟶ Z) (g : Z ⟶ P) :
    condensedPull Λ (f ≫ g) = condensedPull Λ g ≫ condensedPull Λ f := by
  apply Mod.hom_ext
  simp only [pull_hom, Mod.comp_hom']
  exact functionPull_comp Λ f.left g.left Y.hom Z.hom P.hom (Over.w f) (Over.w g)

private lemma pull_id
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (Y : Over X) :
    condensedPull Λ (𝟙 Y) = 𝟙 _ := by
  apply Mod.hom_ext
  rw [pull_hom]
  change (ProEtale.lowerStar Ab.{u + 1} Y.hom).map
      (ProEtale.condensedPushforwardHom Λ (𝟙 Y.left)) ≫
    (ProEtale.lowerStarComp Ab.{u + 1} (𝟙 Y.left) Y.hom).hom.app _ ≫
    (ProEtale.lowerStarCongr Ab.{u + 1} (Category.id_comp Y.hom)).hom.app _ = 𝟙 _
  rw [ProEtale.condensedPushforwardHom_id, ProEtale.legacy_lowerStarComp_id_left]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Iso.symm_hom,
    Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  change (ProEtale.lowerStar Ab.{u + 1} Y.hom).map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]

private lemma coefficient_section
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y X : Scheme.{u}} (p : Y ⟶ X)
    (c : MonObj.Γ Λ) :
    (MonObj.Γ.mapFunctorMonoidHom (ProEtale.upperStarFromPoint X) c).hom ≫
        ProEtale.condensedPushforwardHom Λ p =
      Functor.LaxMonoidal.ε (ProEtale.lowerStar Ab.{u + 1} p) ≫
        (ProEtale.lowerStar Ab.{u + 1} p).map
          (MonObj.Γ.mapFunctorMonoidHom (ProEtale.upperStarFromPoint Y) c).hom := by
  simpa only [MonObj.Γ.mapFunctorMonoidHom_hom,
    ProEtale.condensedPushforwardHom, Category.assoc] using
    Adjunction.ε_comp_map_comp_unit_app_comp_map
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} p)
      (ProEtale.upperStarFromPoint X) (ProEtale.upperStarFromPoint Y)
      (ProEtale.upperStarFromPointComp p).hom c.hom

private lemma regularEnd_hom {C : Type*} [Category* C] [MonoidalCategory C]
    [BraidedCategory C] [Preadditive C] [MonoidalPreadditive C]
    {R : C} [MonObj R] [IsCommMonObj R] (c : MonObj.Γ R) :
    (Mod.regularEndRingHom c).asHom.hom = Mod.globalSmul c.hom (Mod.regular R) := by
  exact Mod.rightUnitor_inv_whiskerLeft_mul_eq c.hom

private lemma pushed_scalar
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y X : Scheme.{u}} (p : Y ⟶ X)
    (c : MonObj.Γ Λ) :
    (ProEtale.CondensedRing.lowerStar Λ p).map
        (Mod.regularEndRingHom
          (MonObj.Γ.mapFunctorMonoidHom (ProEtale.upperStarFromPoint Y) c)).asHom =
      (Mod.smulNatTrans
        (MonObj.Γ.mapFunctorMonoidHom (ProEtale.upperStarFromPoint X) c).hom).app
        ((ProEtale.CondensedRing.lowerStar Λ p).obj (condensedUnit Λ Y)) := by
  apply Mod.hom_ext
  rw [ProEtale.CondensedRing.lowerStar_map_hom, regularEnd_hom,
    Mod.smulNatTrans_app_hom_eq_globalSmul]
  change (ProEtale.lowerStar Ab.{u + 1} p).map
      (Mod.globalSmul
        (MonObj.Γ.mapFunctorMonoidHom (ProEtale.upperStarFromPoint Y) c).hom
        (Mod.regular (ProEtale.condensedRingObj Λ Y))) =
    Mod.globalSmul
      (MonObj.Γ.mapFunctorMonoidHom (ProEtale.upperStarFromPoint X) c).hom
      ((Mod.comap (ProEtale.condensedPushforwardHom Λ p)).obj
        (((ProEtale.lowerStar Ab.{u + 1} p).mapMod
          (ProEtale.condensedRingObj Λ Y)).obj
            (Mod.regular (ProEtale.condensedRingObj Λ Y))))
  rw [Mod.globalSmul_comap, coefficient_section, Mod.globalSmul_mapMod]

private lemma pull_scalar
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} {Y Z : Over X} (h : Y ⟶ Z)
    (c : MonObj.Γ Λ) :
    (ProEtale.CondensedRing.lowerStar Λ Z.hom).map
        (Mod.regularEndRingHom
          (MonObj.Γ.mapFunctorMonoidHom (ProEtale.upperStarFromPoint Z.left) c)).asHom ≫
        condensedPull Λ h =
      condensedPull Λ h ≫ (ProEtale.CondensedRing.lowerStar Λ Y.hom).map
        (Mod.regularEndRingHom
          (MonObj.Γ.mapFunctorMonoidHom (ProEtale.upperStarFromPoint Y.left) c)).asHom := by
  rw [pushed_scalar, pushed_scalar]
  exact (NatTrans.naturality (Mod.smulNatTrans
    (MonObj.Γ.mapFunctorMonoidHom (ProEtale.upperStarFromPoint X) c).hom)
      (condensedPull Λ h)).symm

end Coherence

/-- An equivariant cover isomorphism transports the actual character-projector image,
including every induced pullback-of-functions map and its root evaluation.
Source: latest blueprint, lem-wft-as-unit-trivialization.proof.md, final paragraph;
lem-wft-as-comparison.proof.md, quotient-cover and evaluation comparison.
(blueprint: lem-wft-condensed-projector-cover-iso).

Proof in words. On a cover Y, take the coefficient module pushed forward along Y→X.
The regular-lift formula for condensedPull is the pullback of coefficient functions.
Its identity and composition laws follow from the unit and associativity coherence of
lowerStarComp and from condensedPushforwardHom_id and condensedPushforwardHom_comp;
regular module maps are determined by their value on the coefficient unit. This gives
a contravariant functor of covers. These maps commute with coefficient multiplication,
by the monoidal-adjunction mate equation and naturality of scalar multiplication.
Conjugacy of the translations therefore intertwines the finite sums defining the two
averaging projectors. The isomorphism of the two pushed-forward coefficient modules
induces an isomorphism J of their images, whose composite with the image inclusion
is the old inclusion followed by pullback along u inverse. Compose this identity with
the given inclusion identity for e. The composition law for condensedPull gives the
first asserted equation. Apply upperStar to it and use its functoriality. By the
composition law once more, the defining adjunction-counit formula for
condensedEvaluation gives the second equation, at every root and after every base map.
No root existence, torsor, invertibility of card(G), or field hypothesis is used. -/
theorem condensedProjector_coverIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (G : Type v) [AddGroup G] [Fintype G]
    {X : Scheme.{u}} {Y Z : Over X} (u : Y ≅ Z)
    (σY : G → (Y ⟶ Y)) (σZ : G → (Z ⟶ Z))
    (hσ : ∀ c, σY c ≫ u.hom = u.hom ≫ σZ c)
    (χ : AddChar G (MonObj.Γ Λ)) :
    ∃ J : image (condensedProjector Λ G Y σY χ).asHom ≅
        image (condensedProjector Λ G Z σZ χ).asHom,
      ∀ (P : Over X) (h : Y ⟶ P)
        (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (ProEtale.condensedRingObj Λ X))
        (ι : M ⟶ (ProEtale.CondensedRing.lowerStar Λ P.hom).obj (condensedUnit Λ P.left))
        (e : M ≅ image (condensedProjector Λ G Y σY χ).asHom),
        e.hom ≫ image.ι (condensedProjector Λ G Y σY χ).asHom = ι ≫ condensedPull Λ h →
        (e ≪≫ J).hom ≫ image.ι (condensedProjector Λ G Z σZ χ).asHom =
          ι ≫ condensedPull Λ (u.inv ≫ h) ∧
        ∀ (T : Scheme.{u}) (x : T ⟶ X) (s : Over.mk x ⟶ Z),
          (ProEtale.CondensedRing.upperStar Λ x).map (e ≪≫ J).hom ≫
              condensedEvaluation Λ x s
                (image.ι (condensedProjector Λ G Z σZ χ).asHom) =
            condensedEvaluation Λ x (s ≫ u.inv ≫ h) ι := by
  classical
  let U :
      (ProEtale.CondensedRing.lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left) ≅
      (ProEtale.CondensedRing.lowerStar Λ Z.hom).obj (condensedUnit Λ Z.left) :=
    { hom := condensedPull Λ u.inv
      inv := condensedPull Λ u.hom
      hom_inv_id := by rw [← pull_comp, u.hom_inv_id, pull_id]
      inv_hom_id := by rw [← pull_comp, u.inv_hom_id, pull_id] }
  have hi (c : G) : u.inv ≫ σY c = σZ c ≫ u.inv := by
    simpa [Category.assoc] using congrArg (fun f ↦ u.inv ≫ f ≫ u.inv) (hσ c)
  have ht (c : G) :
      condensedPull Λ (σY c) ≫ U.hom = U.hom ≫ condensedPull Λ (σZ c) := by
    change condensedPull Λ (σY c) ≫ condensedPull Λ u.inv =
      condensedPull Λ u.inv ≫ condensedPull Λ (σZ c)
    rw [← pull_comp, ← pull_comp, hi]
  have hp : (condensedProjector Λ G Y σY χ).asHom ≫ U.hom =
      U.hom ≫ (condensedProjector Λ G Z σZ χ).asHom := by
    unfold condensedProjector
    simp only [End.sum_asHom]
    erw [Preadditive.sum_comp, Preadditive.comp_sum]
    apply Finset.sum_congr rfl
    intro c _
    change (condensedPull Λ (σY c) ≫ _) ≫ condensedPull Λ u.inv = _
    rw [Category.assoc, pull_scalar, ← Category.assoc, ht, Category.assoc]
  let A : Arrow.mk (condensedProjector Λ G Y σY χ).asHom ≅
      Arrow.mk (condensedProjector Λ G Z σZ χ).asHom := Arrow.isoMk U U hp.symm
  let J := CategoryTheory.Limits.im.mapIso A
  have hJ : J.hom ≫ image.ι (condensedProjector Λ G Z σZ χ).asHom =
      image.ι (condensedProjector Λ G Y σY χ).asHom ≫ condensedPull Λ u.inv :=
    image.map_ι A.hom
  refine ⟨J, ?_⟩
  intro P h M ι e he
  have heJ : (e ≪≫ J).hom ≫ image.ι (condensedProjector Λ G Z σZ χ).asHom =
      ι ≫ condensedPull Λ (u.inv ≫ h) := by
    rw [Iso.trans_hom, Category.assoc, hJ, ← Category.assoc, he,
      Category.assoc, ← pull_comp]
  refine ⟨heJ, ?_⟩
  intro T x s
  unfold condensedEvaluation
  erw [← CategoryTheory.Functor.map_comp_assoc]
  rw [← Category.assoc, heJ, Category.assoc, ← pull_comp]

end AlgebraicGeometry.ArtinSchreierTrace
