/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage

import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj

/-!
# The geometric inverse image from the profinite point

Source: RefactorInstruction.tex, Section 4, lem:XS and prop:pX, and Section 5,
eq:triangle and thm:alpha (auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

/-- The set inverse image is left Kan extension followed by sheafification.
Source: RefactorInstruction, prop:pX
(auxiliary; not a blueprint node). -/
noncomputable abbrev profinitePointSetInverseImage :
    Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)) ⥤
      Sheaf (Scheme.ProEt.topology specZ.{u}) (Type (u + 1)) :=
  Functor.sheafPullbackConstruction.sheafPullback profiniteToProEt (Type (u + 1))
    (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)

/-- Geometric inverse image from the profinite point, including the specified monoidal
comparison with the inverse image along every scheme morphism.

Source: RefactorInstruction, lem:XS, prop:pX, eq:triangle, thm:alpha
(auxiliary; not a blueprint node).

Proof: (1) Apply the relative profinite test-object theorem at Spec Z to obtain finite
limits and covering preservation, identifying its maps with spectrum of precomposition.
(2) Apply the left-exact site inverse-image tensor theorem to obtain the sheafified Kan
extension adjunction, exactness and strong symmetric monoidality.
(3) The inverse-image composition comparison is the conjugate of the canonical
fibre-product comparison. Uniqueness of adjunction-compatible comparisons gives the
identity and associativity laws, and the site tensor theorem makes it monoidal.
(4) Whisker the comparison for h and the structure morphism by pointUpperStar and use
comp_toSpecZ. This is exactly upperStarFromPointComp, and is natural and monoidal.
(5) Apply it to ring operations to get the ring-sheaf isomorphism. The subsequent
coherence declarations record the identity, composition, linear, derived and square
clauses explicitly. -/
theorem profinite_point_pullback :
    (∀ S : Profinite.{u}, WeaklyEtale (toSpecZ (profiniteToScheme.obj S))) ∧
    PreservesFiniteLimits profiniteToProEt.{u} ∧
    CoverPreserving (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)
      profiniteToProEt ∧
    (∀ F : Profinite.{u}ᵒᵖ ⥤ Type (u + 1),
      profiniteToProEt.op.HasLeftKanExtension F) ∧
    (∀ F : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1},
      profiniteToProEt.op.HasLeftKanExtension F) ∧
    Nonempty (profinitePointSetInverseImage.{u} ⊣
      profiniteToProEt.sheafPushforwardContinuous (Type (u + 1))
        (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)) ∧
    PreservesFiniteLimits profinitePointSetInverseImage.{u} ∧
    PreservesColimitsOfSize.{u + 1, u + 1} profinitePointSetInverseImage.{u} ∧
    PreservesFiniteLimits pointUpperStar.{u} ∧
    PreservesFiniteColimits pointUpperStar.{u} ∧
    Nonempty pointUpperStar.{u}.Monoidal ∧
    Nonempty pointUpperStar.{u}.Braided ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
      NatTrans.IsMonoidal (upperStarFromPointComp f).hom) := by
  let : AB5OfSize.{u, u + 1} (Type (u + 1)) := AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} _
  let : AB5OfSize.{u, u + 1} Ab.{u + 1} := AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} _
  refine ⟨fun S ↦ inferInstance, inferInstance, coverPreserving_profiniteToProEt,
    fun F ↦ inferInstance, fun F ↦ inferInstance, ⟨?_⟩, ?_, ?_, ?_, ?_,
    ⟨inferInstance⟩, ⟨{ toMonoidal := inferInstance, braided := Functor.LaxBraided.braided }⟩,
    fun X Y f ↦ inferInstance⟩
  · exact Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      profiniteToProEt (Type (u + 1))
      (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)
  · unfold profinitePointSetInverseImage
    infer_instance
  · exact (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      profiniteToProEt (Type (u + 1))
      (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)).leftAdjoint_preservesColimits
  · unfold pointUpperStar
    infer_instance
  · have : PreservesColimitsOfSize.{0, 0} pointUpperStar :=
      pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
    infer_instance

private lemma normalizedPointComparison_comp
    {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (kX : X ⟶ W) (kY : Y ⟶ W) (kZ : Z ⟶ W)
    (hX : f ≫ kY = kX) (hY : g ≫ kZ = kY) (hfg : (f ≫ g) ≫ kZ = kX)
    (M : Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) :
    (upperStarComp Ab.{u + 1} f g).hom.app ((upperStar Ab.{u + 1} kZ).obj M) ≫
      (upperStar Ab.{u + 1} f).map
        ((upperStarComp Ab.{u + 1} g kZ).inv.app M ≫
          (eqToHom (congrArg (upperStar Ab.{u + 1}) hY)).app M) ≫
      ((upperStarComp Ab.{u + 1} f kY).inv.app M ≫
        (eqToHom (congrArg (upperStar Ab.{u + 1}) hX)).app M) =
    (upperStarComp Ab.{u + 1} (f ≫ g) kZ).inv.app M ≫
      (eqToHom (congrArg (upperStar Ab.{u + 1}) hfg)).app M := by
  subst hY
  subst hX
  have h := congrArg (fun e ↦ e.inv.app M) (upperStarComp_assoc Ab.{u + 1} f g kZ)
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Category.id_comp, upperStarCongr,
    eqToIso.inv] at h
  simp only [eqToHom_refl, NatTrans.id_app, Category.comp_id]
  rw [h]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rfl

private lemma pointComparison_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    (eqToHom (congrArg (upperStar Ab.{u + 1}) w)).app ((upperStarFromPoint Y).obj Λ) ≫
        (upperStarFromPointComp g).hom.app Λ = (upperStarFromPointComp f).hom.app Λ := by
  subst w
  simp

/-- The point comparisons satisfy identity and composition on abelian sheaves, hence
also on ring sheaves, since all their components preserve ring operations.
Source: RefactorInstruction, eq:triangle and thm:alpha
(auxiliary; not a blueprint node).

Proof: (3) Transport inverse-image adjunctions to strictly composed right adjoints and
apply associativity of the unique conjugate comparison; identity follows by comparison
with the identity adjunction. (4) Whisker with pointUpperStar and use comp_toSpecZ.
(5) Naturality at addition, negation, zero, multiplication and one proves that these
same equations are equations of ring maps, not merely maps of underlying sheaves. -/
theorem profinite_point_pullback_coefficient_coherence :
    (∀ (X : Scheme.{u}) (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}),
      (upperStarFromPointComp (𝟙 X)).hom.app Λ =
        (upperStarId Ab.{u + 1} X).hom.app ((upperStarFromPoint X).obj Λ)) ∧
    (∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
      (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}),
      (upperStarComp Ab.{u + 1} f g).hom.app ((upperStarFromPoint Z).obj Λ) ≫
          (upperStar Ab.{u + 1} f).map ((upperStarFromPointComp g).hom.app Λ) ≫
          (upperStarFromPointComp f).hom.app Λ =
        (upperStarFromPointComp (f ≫ g)).hom.app Λ) := by
  constructor
  · intro X Λ
    simp [upperStarFromPointComp, upperStarComp_id_left, upperStarCongr,
      upperStarFromPoint]
  · intro X Y Z f g Λ
    change (upperStarComp Ab.{u + 1} f g).hom.app
        ((upperStar Ab.{u + 1} (toSpecZ Z)).obj (pointUpperStar.obj Λ)) ≫
      (upperStar Ab.{u + 1} f).map (condensedPullbackHom Λ g) ≫
        condensedPullbackHom Λ f = condensedPullbackHom Λ (f ≫ g)
    rw [condensedPullbackHom_eq, condensedPullbackHom_eq, condensedPullbackHom_eq]
    exact normalizedPointComparison_comp f g (toSpecZ X) (toSpecZ Y) (toSpecZ Z)
      (comp_toSpecZ f) (comp_toSpecZ g) (comp_toSpecZ (f ≫ g)) (pointUpperStar.obj Λ)

/-- Abelian inverse-image composition is coherent, including both units and every
commutative square. The square map is explicitly the comparison through the common
composite, so it includes noncartesian squares and identity arrows.
Source: RefactorInstruction, Section 5, eq:triangle; Stacks, Tag 03CB
(auxiliary; not a blueprint node).

Proof: (3) Fibre-product maps preserve both projections, so their associativity and unit
diagrams commute by the universal property. Conjugate these diagrams using the
inverse-image adjunctions; uniqueness of the conjugate comparison preserves the equations.
(8) For a square, compose the inverse-image comparison with the inverse comparison for
the other route after transporting along the equality of the two composite morphisms.
Both resulting point-comparison paths equal the comparison for that common morphism. -/
theorem profinite_point_pullback_abelian_coherence :
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
      (M : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}),
      (upperStarComp Ab.{u + 1} (𝟙 X) f).hom.app M ≫
          (upperStarId Ab.{u + 1} X).hom.app ((upperStar Ab.{u + 1} f).obj M) =
        (eqToHom (congrArg (upperStar Ab.{u + 1}) (Category.id_comp f))).app M) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
      (M : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}),
      (upperStarComp Ab.{u + 1} f (𝟙 Y)).hom.app M ≫
          (upperStar Ab.{u + 1} f).map ((upperStarId Ab.{u + 1} Y).hom.app M) =
        (eqToHom (congrArg (upperStar Ab.{u + 1}) (Category.comp_id f))).app M) ∧
    (∀ (X Y Z W : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
      (M : Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}),
      (upperStarComp Ab.{u + 1} (f ≫ g) h).hom.app M ≫
          (upperStarComp Ab.{u + 1} f g).hom.app ((upperStar Ab.{u + 1} h).obj M) =
        (eqToHom (congrArg (upperStar Ab.{u + 1}) (Category.assoc f g h))).app M ≫
          (upperStarComp Ab.{u + 1} f (g ≫ h)).hom.app M ≫
          (upperStar Ab.{u + 1} f).map ((upperStarComp Ab.{u + 1} g h).hom.app M)) ∧
    (∀ (X' X Y' Y : Scheme.{u}) (b : X' ⟶ X) (f : X ⟶ Y)
      (f' : X' ⟶ Y') (g : Y' ⟶ Y) (w : b ≫ f = f' ≫ g)
      (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}),
      (upperStarComp Ab.{u + 1} b f).inv.app ((upperStarFromPoint Y).obj Λ) ≫
          (eqToHom (congrArg (upperStar Ab.{u + 1}) w)).app
            ((upperStarFromPoint Y).obj Λ) ≫
          (upperStarComp Ab.{u + 1} f' g).hom.app ((upperStarFromPoint Y).obj Λ) ≫
          (upperStar Ab.{u + 1} f').map ((upperStarFromPointComp g).hom.app Λ) ≫
          (upperStarFromPointComp f').hom.app Λ =
        (upperStar Ab.{u + 1} b).map ((upperStarFromPointComp f).hom.app Λ) ≫
          (upperStarFromPointComp b).hom.app Λ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y f M
    simp [upperStarComp_id_left, upperStarCongr]
    rfl
  · intro X Y f M
    simp [upperStarComp_id_right, upperStarCongr, ← Functor.map_comp]
    rfl
  · intro X Y Z W f g h M
    exact upperStarComp_hom_app_comp_upperStarComp_hom_app Ab.{u + 1} f g h M
  · intro X' X Y' Y b f f' g w Λ
    rw [profinite_point_pullback_coefficient_coherence.2 X' Y' Y f' g Λ,
      pointComparison_congr w Λ]
    rw [← cancel_epi ((upperStarComp Ab.{u + 1} b f).hom.app
      ((upperStarFromPoint Y).obj Λ))]
    simpa [Category.assoc] using
      (profinite_point_pullback_coefficient_coherence.2 X' X Y b f Λ).symm

open scoped CategoryTheory.Obj

/-- The identity comparison of module direct images is uniquely determined by the
identity comparison on underlying abelian sheaves.
Source: RefactorInstruction, Section 5, coherence of eq:triangle
(auxiliary; not a blueprint node).

Proof: (5) condensedPushforwardHom_id identifies the scalar action with the identity
action through lowerStarId. (6) Hence that abelian identity map and its inverse are
linear. Faithfulness of forgetting the action proves uniqueness. -/
theorem existsUnique_profinitePointModuleDirectImageIdentity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    ∃! r : CondensedRing.lowerStar Λ (𝟙 X) ≅ 𝟭 _,
      ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
        (Mod.forget (condensedRingObj Λ X)).map (r.hom.app M) =
          (lowerStarId Ab.{u + 1} X).hom.app M.X := by
  classical
  have : NatTrans.IsMonoidal (lowerStarId Ab.{u + 1} X).hom :=
    Functor.isMonoidal_sheafPushforwardContinuousId' _ _
  let r : CondensedRing.lowerStar Λ (𝟙 X) ≅ 𝟭 _ :=
    NatIso.ofComponents (fun M ↦ Mod.isoMk ((lowerStarId Ab.{u + 1} X).app M.X) (by
      change (condensedPushforwardHom Λ (𝟙 X) ▷ _ ≫
          Functor.LaxMonoidal.μ (lowerStar Ab.{u + 1} (𝟙 X)) _ _ ≫
          (lowerStar Ab.{u + 1} (𝟙 X)).map (Mod.act M.X)) ≫
          (lowerStarId Ab.{u + 1} X).hom.app M.X = _
      change (condensedPushforwardHom Λ (𝟙 X) ▷ _ ≫
          Functor.LaxMonoidal.μ (lowerStar Ab.{u + 1} (𝟙 X)) _ _ ≫
          (lowerStar Ab.{u + 1} (𝟙 X)).map (Mod.act M.X)) ≫
          (lowerStarId Ab.{u + 1} X).hom.app M.X =
        condensedRingObj Λ X ◁ (lowerStarId Ab.{u + 1} X).hom.app M.X ≫ Mod.act M.X
      rw [condensedPushforwardHom_id]
      simp only [Category.assoc]
      rw [(lowerStarId Ab.{u + 1} X).hom.naturality,
        NatTrans.IsMonoidal.tensor_assoc]
      simp [Functor.LaxMonoidal.id_μ, MonoidalCategory.tensorHom_def,
        ← MonoidalCategory.comp_whiskerRight_assoc])) (fun φ ↦ by
      apply Mod.hom_ext
      exact (lowerStarId Ab.{u + 1} X).hom.naturality φ.hom)
  refine ⟨r, fun M ↦ ?_, ?_⟩
  · rfl
  · intro t ht
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply (Mod.forget (condensedRingObj Λ X)).map_injective
    exact ht M

/-- The canonical identity comparison of module direct images, selected by its unique
underlying map, not by a mere existence of an unrelated isomorphism.
Source: RefactorInstruction, Section 5, eq:triangle
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointModuleDirectImageIdentity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    CondensedRing.lowerStar Λ (𝟙 X) ≅ 𝟭 _ :=
  (existsUnique_profinitePointModuleDirectImageIdentity Λ X).exists.choose

/-- The canonical identity comparison of module inverse images is the conjugate of
that of the direct images under the specified module adjunction.
Source: RefactorInstruction, Section 5, eq:triangle
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointModuleIdentity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    CondensedRing.upperStar Λ (𝟙 X) ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id (CondensedRing.upperStarLowerStarAdjunction Λ (𝟙 X))).symm
    (profinitePointModuleDirectImageIdentity Λ X).symm

/-- The scalar-extension pullback has the original exact abelian inverse image as its
underlying sheaf, via restriction along the inverse coefficient isomorphism.
Source: RefactorInstruction, thm:alpha; Stacks, Tags 03D2 and 03D8
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointModuleForgetPullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.upperStar Λ f ⋙ Mod.forget (condensedRingObj Λ X) ≅
      Mod.forget (condensedRingObj Λ Y) ⋙ upperStar Ab.{u + 1} f :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y))
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)))
    (Mod.forget (condensedRingObj Λ X))

private lemma moduleLowerStarComp_underlying
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((CondensedRing.lowerStarComp Λ f g).hom.app M).hom =
      (lowerStarComp Ab.{u + 1} f g).hom.app M.X := by
  simp only [Functor.comp_obj, CondensedRing.lowerStarComp, Functor.isoWhiskerLeft_trans,
    Functor.isoWhiskerLeft_twice, Functor.mapModCompIso,
    CondensedRing.comapCondensedPushforwardHomComp, Iso.trans_assoc,
    Iso.self_symm_id_assoc, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    NatIso.ofComponents_hom_app, Category.id_comp, Mod.comp_hom', Mod.id_hom',
    Mod.comap_map_hom, Functor.mapModComapIso_hom_app_hom, Mod.comapComp_inv_app_hom,
    Mod.isoMk_hom_hom, asIso_hom, Mod.comapCongr_hom_app_hom]
  erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp,
    Category.comp_id]

private lemma moduleLowerStarId_underlying
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((profinitePointModuleDirectImageIdentity Λ X).hom.app M).hom =
      (lowerStarId Ab.{u + 1} X).hom.app M.X := by
  exact (existsUnique_profinitePointModuleDirectImageIdentity Λ X).exists.choose_spec M

private lemma moduleUnit_forget
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    ((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app M).hom ≫
      (lowerStar Ab.{u + 1} f).map
        ((profinitePointModuleForgetPullbackIso Λ f).hom.app M) =
      (upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app M.X := by
  let φ := condensedPullbackHom Λ f
  let N := ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)).obj M
  have he := congrArg (fun k ↦ k.hom)
    (Adjunction.unit_leftAdjointUniq_hom_app (Mod.extendRestrictAdjunction φ)
      (Mod.comapEquivalenceOfIsIso φ).symm.toAdjunction N)
  simp only [Mod.comp_hom', Mod.comap_map_hom] at he
  have he' : ((Mod.extendRestrictAdjunction φ).unit.app N).hom ≫
      ((Mod.extendScalarsIsoComapInv φ).hom.app N).hom = 𝟙 N.X := by
    change _ = (𝟙 N.X ≫ 𝟙 N.X) ≫ 𝟙 N.X at he
    simpa only [Mod.extendScalarsIsoComapInv, Category.id_comp] using he
  have hc : ((CondensedRing.comapPullbackHomCompIso Λ f).hom.app
      ((CondensedRing.upperStar Λ f).obj M)).hom = 𝟙 _ := by
    simp only [CondensedRing.comapPullbackHomCompIso, Iso.trans_hom,
      Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Mod.comp_hom',
      Mod.id_hom', Mod.comap_map_hom, Functor.mapModComapIso_hom_app_hom,
      Mod.comapComp_inv_app_hom, Mod.comapCongr_hom_app_hom]
    erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp]
    rfl
  unfold CondensedRing.upperStarLowerStarAdjunction
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.comp_unit_app, Mod.comp_hom',
    Adjunction.mapModAdjunction_unit_app_hom]
  rw [hc]
  erw [Category.comp_id]
  change ((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app M.X ≫
      (lowerStar Ab.{u + 1} f).map
        (((Mod.extendRestrictAdjunction φ).unit.app N).hom)) ≫
      (lowerStar Ab.{u + 1} f).map
        (((Mod.extendScalarsIsoComapInv φ).hom.app N).hom) = _
  rw [Category.assoc, ← Functor.map_comp, he']
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private lemma moduleUnit_forget_inv
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app M.X ≫
      (lowerStar Ab.{u + 1} f).map
        ((profinitePointModuleForgetPullbackIso Λ f).inv.app M) =
      ((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app M).hom := by
  rw [← moduleUnit_forget Λ f M, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private lemma moduleIdentity_forget
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((profinitePointModuleIdentity Λ X).hom.app N).hom =
      (profinitePointModuleForgetPullbackIso Λ (𝟙 X)).hom.app N ≫
        (upperStarId Ab.{u + 1} X).hom.app N.X := by
  have hd : ((profinitePointModuleDirectImageIdentity Λ X).inv.app N).hom =
      (lowerStarId Ab.{u + 1} X).inv.app N.X := by
    rw [← cancel_mono ((lowerStarId Ab.{u + 1} X).hom.app N.X), Iso.inv_hom_id_app]
    rw [← moduleLowerStarId_underlying Λ X N]
    change (Mod.forget _).map _ ≫ (Mod.forget _).map _ = _
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
    rfl
  have hc : conjugateEquiv Adjunction.id
      (CondensedRing.upperStarLowerStarAdjunction Λ (𝟙 X))
      (profinitePointModuleIdentity Λ X).hom =
      (profinitePointModuleDirectImageIdentity Λ X).inv := by
    exact congrArg Iso.hom ((conjugateIsoEquiv Adjunction.id
      (CondensedRing.upperStarLowerStarAdjunction Λ (𝟙 X))).apply_symm_apply
      (profinitePointModuleDirectImageIdentity Λ X).symm)
  have hm := unit_conjugateEquiv Adjunction.id
    (CondensedRing.upperStarLowerStarAdjunction Λ (𝟙 X))
    (profinitePointModuleIdentity Λ X).hom N
  rw [hc] at hm
  have hm' := congrArg (fun k ↦ k.hom) hm
  simp only [Adjunction.id_unit, NatTrans.id_app, Category.id_comp, Mod.comp_hom'] at hm'
  have ha := unit_conjugateEquiv Adjunction.id
    (upperStarLowerStarAdjunction Ab.{u + 1} (𝟙 X))
    (upperStarId Ab.{u + 1} X).hom N.X
  rw [show conjugateEquiv Adjunction.id
      (upperStarLowerStarAdjunction Ab.{u + 1} (𝟙 X))
      (upperStarId Ab.{u + 1} X).hom = (lowerStarId Ab.{u + 1} X).inv from
      congrArg Iso.hom (conjugateIsoEquiv_upperStarId Ab.{u + 1} X)] at ha
  simp only [Adjunction.id_unit, NatTrans.id_app, Category.id_comp] at ha
  apply (cancel_epi ((profinitePointModuleForgetPullbackIso Λ (𝟙 X)).inv.app N)).1
  simp only [Iso.inv_hom_id_app_assoc]
  apply ((upperStarLowerStarAdjunction Ab.{u + 1} (𝟙 X)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc]
  erw [moduleUnit_forget_inv Λ (𝟙 X) N]
  exact hm'.symm.trans (hd.trans ha)

private lemma moduleCompositeUnit_forget
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    (((CondensedRing.upperStarLowerStarAdjunction Λ g).comp
        (CondensedRing.upperStarLowerStarAdjunction Λ f)).unit.app M).hom ≫
      (lowerStar Ab.{u + 1} g).map ((lowerStar Ab.{u + 1} f).map
        ((profinitePointModuleForgetPullbackIso Λ f).hom.app
            ((CondensedRing.upperStar Λ g).obj M) ≫
          (upperStar Ab.{u + 1} f).map
            ((profinitePointModuleForgetPullbackIso Λ g).hom.app M))) =
    ((upperStarLowerStarAdjunction Ab.{u + 1} g).comp
      (upperStarLowerStarAdjunction Ab.{u + 1} f)).unit.app M.X := by
  simp only [Adjunction.comp_unit_app, Mod.comp_hom', Functor.map_comp]
  change (((CondensedRing.upperStarLowerStarAdjunction Λ g).unit.app M).hom ≫
      (lowerStar Ab.{u + 1} g).map
        (((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app
          ((CondensedRing.upperStar Λ g).obj M)).hom)) ≫
      ((lowerStar Ab.{u + 1} g).map ((lowerStar Ab.{u + 1} f).map
          ((profinitePointModuleForgetPullbackIso Λ f).hom.app
            ((CondensedRing.upperStar Λ g).obj M))) ≫
        (lowerStar Ab.{u + 1} g).map ((lowerStar Ab.{u + 1} f).map
          ((upperStar Ab.{u + 1} f).map
            ((profinitePointModuleForgetPullbackIso Λ g).hom.app M)))) = _
  have hf := congrArg ((lowerStar Ab.{u + 1} g).map)
    (moduleUnit_forget Λ f ((CondensedRing.upperStar Λ g).obj M))
  simp only [Functor.map_comp] at hf
  simp only [Category.assoc]
  erw [reassoc_of% hf]
  rw [← Functor.map_comp]
  have hn := (upperStarLowerStarAdjunction Ab.{u + 1} f).unit.naturality
    ((profinitePointModuleForgetPullbackIso Λ g).hom.app M)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  erw [← hn]
  rw [Functor.map_comp, ← Category.assoc]
  erw [moduleUnit_forget Λ g M]
  rfl

private lemma comparisonFromUnits
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R S : D ⥤ C} (adj : L ⊣ R) (β : S ⟶ R)
    {M : C} {A B B' : D} (e : A ⟶ L.obj M) (ei : L.obj M ⟶ A)
    (a : A ⟶ B) (q : B ⟶ B') (c : L.obj M ⟶ B')
    (η : M ⟶ R.obj A) (ν : M ⟶ S.obj B) (ν' : M ⟶ S.obj B')
    (he : e ≫ ei = 𝟙 _) (hη : adj.unit.app M ≫ R.map ei = η)
    (ha : η ≫ R.map a = ν ≫ β.app B)
    (hq : ν ≫ S.map q = ν')
    (hc : adj.unit.app M ≫ R.map c = ν' ≫ β.app B') :
    a ≫ q = e ≫ c := by
  have hh : ei ≫ (a ≫ q) = c := by
    apply (adj.homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, Functor.map_comp]
    rw [← Category.assoc, hη, ← Category.assoc, ha, Category.assoc,
      ← β.naturality q, ← Category.assoc, hq, hc]
  calc
    a ≫ q = e ≫ ei ≫ (a ≫ q) := by
      rw [reassoc_of% he]
    _ = e ≫ c := by rw [hh]

private lemma moduleComposition_forget
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    ∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
      (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)),
      (Mod.forget (condensedRingObj Λ X)).map
          ((CondensedRing.upperStarComp Λ f g).hom.app M) ≫
          (profinitePointModuleForgetPullbackIso Λ f).hom.app
            ((CondensedRing.upperStar Λ g).obj M) ≫
          (upperStar Ab.{u + 1} f).map
            ((profinitePointModuleForgetPullbackIso Λ g).hom.app M) =
        (profinitePointModuleForgetPullbackIso Λ (f ≫ g)).hom.app M ≫
          (upperStarComp Ab.{u + 1} f g).hom.app M.X := by
  intro X Y Z f g M
  let q : ((CondensedRing.upperStar Λ f).obj
      ((CondensedRing.upperStar Λ g).obj M)).X ⟶
      (upperStar Ab.{u + 1} f).obj ((upperStar Ab.{u + 1} g).obj M.X) :=
    (profinitePointModuleForgetPullbackIso Λ f).hom.app
      ((CondensedRing.upperStar Λ g).obj M) ≫
    (upperStar Ab.{u + 1} f).map ((profinitePointModuleForgetPullbackIso Λ g).hom.app M)
  have hc : conjugateEquiv
      ((CondensedRing.upperStarLowerStarAdjunction Λ g).comp
        (CondensedRing.upperStarLowerStarAdjunction Λ f))
      (CondensedRing.upperStarLowerStarAdjunction Λ (f ≫ g))
      (CondensedRing.upperStarComp Λ f g).hom =
      (CondensedRing.lowerStarComp Λ f g).hom := by
    change (conjugateIsoEquiv _ _ (CondensedRing.upperStarComp Λ f g)).hom = _
    rw [CondensedRing.upperStarComp, conjugateIsoEquiv_iso_symm]
    simp
  have hm := unit_conjugateEquiv
    ((CondensedRing.upperStarLowerStarAdjunction Λ g).comp
      (CondensedRing.upperStarLowerStarAdjunction Λ f))
    (CondensedRing.upperStarLowerStarAdjunction Λ (f ≫ g))
    (CondensedRing.upperStarComp Λ f g).hom M
  rw [hc] at hm
  have hm' := congrArg (fun k ↦ k.hom) hm
  simp only [Mod.comp_hom', moduleLowerStarComp_underlying, Functor.comp_obj] at hm'
  have ha := unit_conjugateEquiv
    ((upperStarLowerStarAdjunction Ab.{u + 1} g).comp
      (upperStarLowerStarAdjunction Ab.{u + 1} f))
    (upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ g))
    (upperStarComp Ab.{u + 1} f g).hom M.X
  rw [conjugateEquiv_upperStarComp_hom] at ha
  have hu : (((CondensedRing.upperStarLowerStarAdjunction Λ g).comp
      (CondensedRing.upperStarLowerStarAdjunction Λ f)).unit.app M).hom ≫
      ((lowerStar Ab.{u + 1} f) ⋙ (lowerStar Ab.{u + 1} g)).map q =
      ((upperStarLowerStarAdjunction Ab.{u + 1} g).comp
        (upperStarLowerStarAdjunction Ab.{u + 1} f)).unit.app M.X :=
    moduleCompositeUnit_forget Λ f g M
  exact comparisonFromUnits (upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ g))
    (lowerStarComp Ab.{u + 1} f g).hom
    ((profinitePointModuleForgetPullbackIso Λ (f ≫ g)).hom.app M)
    ((profinitePointModuleForgetPullbackIso Λ (f ≫ g)).inv.app M)
    (((CondensedRing.upperStarComp Λ f g).hom.app M).hom) q
    ((upperStarComp Ab.{u + 1} f g).hom.app M.X)
    (((CondensedRing.upperStarLowerStarAdjunction Λ (f ≫ g)).unit.app M).hom)
    ((((CondensedRing.upperStarLowerStarAdjunction Λ g).comp
      (CondensedRing.upperStarLowerStarAdjunction Λ f)).unit.app M).hom)
    (((upperStarLowerStarAdjunction Ab.{u + 1} g).comp
      (upperStarLowerStarAdjunction Ab.{u + 1} f)).unit.app M.X)
    (Iso.hom_inv_id_app _ M) (moduleUnit_forget_inv Λ (f ≫ g) M)
    hm'.symm hu ha.symm

/-- The module comparison is the linear lift of the abelian comparison. Exactness
follows because extension of scalars along the coefficient isomorphism is an equivalence.
Source: RefactorInstruction, thm:alpha; Stacks, Tags 03D2 and 03D8
(auxiliary; not a blueprint node).

Proof: (6) Apply inverse image to the module action and substitute the inverse coefficient
isomorphism in the scalar variable. The balanced maps r tensor m to alpha inverse(r)m
and m to 1 tensor m are inverse, giving profinitePointModuleForgetPullbackIso. Naturality
of the abelian composition comparison at the action makes it linear; its underlying map
is the equation below. Forgetting is faithful and creates kernels and sheafified cokernels,
so exactness and the abelian unit and associativity equations lift to modules. -/
theorem profinite_point_pullback_module_comparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
      PreservesFiniteLimits (CondensedRing.upperStar Λ f) ∧
      PreservesFiniteColimits (CondensedRing.upperStar Λ f)) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      (Mod.forget (condensedRingObj Λ X)).map
          ((profinitePointModuleIdentity Λ X).hom.app
            ((CondensedRing.upperStar Λ f).obj M)) =
        (profinitePointModuleForgetPullbackIso Λ (𝟙 X)).hom.app
            ((CondensedRing.upperStar Λ f).obj M) ≫
          (upperStarId Ab.{u + 1} X).hom.app
            ((CondensedRing.upperStar Λ f).obj M).X) ∧
    (∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
      (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)),
      (Mod.forget (condensedRingObj Λ X)).map
          ((CondensedRing.upperStarComp Λ f g).hom.app M) ≫
          (profinitePointModuleForgetPullbackIso Λ f).hom.app
            ((CondensedRing.upperStar Λ g).obj M) ≫
          (upperStar Ab.{u + 1} f).map
            ((profinitePointModuleForgetPullbackIso Λ g).hom.app M) =
        (profinitePointModuleForgetPullbackIso Λ (f ≫ g)).hom.app M ≫
          (upperStarComp Ab.{u + 1} f g).hom.app M.X) := by
  refine ⟨?_, ?_, moduleComposition_forget Λ⟩
  · intro X Y f
    exact ⟨inferInstance, inferInstance⟩
  · intro X Y f M
    exact moduleIdentity_forget Λ X ((CondensedRing.upperStar Λ f).obj M)

private lemma moduleLowerStarCongr_underlying
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((eqToHom (congrArg (CondensedRing.lowerStar Λ) w)).app M).hom =
      (eqToHom (congrArg (lowerStar Ab.{u + 1}) w)).app M.X := by
  subst w
  rfl

private lemma moduleLowerStar_map_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (φ : M ⟶ N) : ((CondensedRing.lowerStar Λ f).map φ).hom =
      (lowerStar Ab.{u + 1} f).map φ.hom := rfl

private lemma moduleLowerStarComp_id_left
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.lowerStarComp Λ (𝟙 X) f =
      Functor.isoWhiskerRight (profinitePointModuleDirectImageIdentity Λ X)
        (CondensedRing.lowerStar Λ f) ≪≫
      (CondensedRing.lowerStar Λ f).leftUnitor ≪≫
      (eqToIso (congrArg (CondensedRing.lowerStar Λ) (Category.id_comp f))).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply Mod.hom_ext
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Iso.symm_hom,
    eqToIso.inv, Mod.comp_hom', moduleLowerStarComp_underlying,
    moduleLowerStar_map_hom, moduleLowerStarId_underlying,
    Mod.id_hom']
  rw [moduleLowerStarCongr_underlying Λ (Category.id_comp f).symm]
  have h := congrArg (fun e ↦ e.hom.app M.X) (legacy_lowerStarComp_id_left Ab.{u + 1} f)
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Iso.symm_hom,
    lowerStarCongr, eqToIso.inv, Functor.comp_obj, CondensedRing.lowerStar_obj_X,
    Category.id_comp] using h

private lemma moduleLowerStarComp_id_right
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.lowerStarComp Λ f (𝟙 Y) =
      Functor.isoWhiskerLeft (CondensedRing.lowerStar Λ f)
        (profinitePointModuleDirectImageIdentity Λ Y) ≪≫
      (CondensedRing.lowerStar Λ f).rightUnitor ≪≫
      (eqToIso (congrArg (CondensedRing.lowerStar Λ) (Category.comp_id f))).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply Mod.hom_ext
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Iso.symm_hom,
    eqToIso.inv, Mod.comp_hom', moduleLowerStarComp_underlying,
    moduleLowerStarId_underlying, Mod.id_hom']
  rw [moduleLowerStarCongr_underlying Λ (Category.comp_id f).symm]
  have h := congrArg (fun e ↦ e.hom.app M.X) (lowerStarComp_id_right Ab.{u + 1} f)
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Iso.symm_hom,
    lowerStarCongr, eqToIso.inv, Functor.comp_obj, CondensedRing.lowerStar_obj_X,
    Category.id_comp] using h

private lemma moduleLowerStarComp_assoc
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    Functor.associator (CondensedRing.lowerStar Λ f)
        (CondensedRing.lowerStar Λ g) (CondensedRing.lowerStar Λ h) ≪≫
        Functor.isoWhiskerLeft (CondensedRing.lowerStar Λ f)
          (CondensedRing.lowerStarComp Λ g h) ≪≫
        CondensedRing.lowerStarComp Λ f (g ≫ h) =
      Functor.isoWhiskerRight (CondensedRing.lowerStarComp Λ f g)
          (CondensedRing.lowerStar Λ h) ≪≫
        CondensedRing.lowerStarComp Λ (f ≫ g) h ≪≫
        eqToIso (congrArg (CondensedRing.lowerStar Λ) (Category.assoc f g h)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply Mod.hom_ext
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, eqToIso.hom, Mod.comp_hom', Mod.id_hom',
    moduleLowerStarComp_underlying, moduleLowerStar_map_hom]
  rw [moduleLowerStarCongr_underlying Λ (Category.assoc f g h)]
  have hc := congrArg (fun e ↦ e.hom.app M.X) (legacy_lowerStarComp_assoc Ab.{u + 1} f g h)
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, lowerStarCongr, eqToIso.hom,
    Functor.comp_obj, CondensedRing.lowerStar_obj_X, Category.id_comp] using hc
private lemma eqToIso_symm_congr
    {A B : Type*} [Category B] (F : A → B) {a b : A} (w : a = b) :
    (eqToIso (congrArg F w.symm)).symm = eqToIso (congrArg F w) := by
  cases w
  rfl

private lemma eqToIso_congr_symm
    {A B : Type*} [Category B] (F : A → B) {a b : A} (w : a = b) :
    eqToIso (congrArg F w.symm) = (eqToIso (congrArg F w)).symm := by
  cases w
  rfl

section ModuleMates
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private lemma conjugateModuleComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateIsoEquiv ((CondensedRing.upperStarLowerStarAdjunction Λ g).comp
      (CondensedRing.upperStarLowerStarAdjunction Λ f))
      (CondensedRing.upperStarLowerStarAdjunction Λ (f ≫ g))
      (CondensedRing.upperStarComp Λ f g) = CondensedRing.lowerStarComp Λ f g := by
  rw [CondensedRing.upperStarComp, conjugateIsoEquiv_iso_symm]
  simp

private lemma conjugateModuleId (X : Scheme.{u}) :
    conjugateIsoEquiv Adjunction.id (CondensedRing.upperStarLowerStarAdjunction Λ (𝟙 X))
      (profinitePointModuleIdentity Λ X) = (profinitePointModuleDirectImageIdentity Λ X).symm := by
  exact (conjugateIsoEquiv Adjunction.id
    (CondensedRing.upperStarLowerStarAdjunction Λ (𝟙 X))).apply_symm_apply _

private lemma conjugateModuleCongr {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g) :
    conjugateIsoEquiv (CondensedRing.upperStarLowerStarAdjunction Λ g)
      (CondensedRing.upperStarLowerStarAdjunction Λ f)
      (eqToIso (congrArg (fun k : X ⟶ Y ↦
        CondensedRing.upperStar Λ k) w)) =
      (eqToIso (congrArg (CondensedRing.lowerStar Λ) w)).symm := by
  subst w
  apply Iso.ext
  exact conjugateEquiv_id (CondensedRing.upperStarLowerStarAdjunction Λ f)

private lemma moduleComp_assoc {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    CondensedRing.upperStarComp Λ f (g ≫ h) ≪≫
        Functor.isoWhiskerRight (CondensedRing.upperStarComp Λ g h)
          (CondensedRing.upperStar Λ f) ≪≫
        Functor.associator _ _ _ =
      eqToIso (congrArg (fun k : X ⟶ W ↦
        CondensedRing.upperStar Λ k) (Category.assoc f g h).symm) ≪≫
        CondensedRing.upperStarComp Λ (f ≫ g) h ≪≫
        Functor.isoWhiskerLeft (CondensedRing.upperStar Λ h)
          (CondensedRing.upperStarComp Λ f g) := by
  refine (conjugateIsoEquiv ((CondensedRing.upperStarLowerStarAdjunction Λ h).comp
    ((CondensedRing.upperStarLowerStarAdjunction Λ g).comp
      (CondensedRing.upperStarLowerStarAdjunction Λ f)))
    (CondensedRing.upperStarLowerStarAdjunction Λ (f ≫ g ≫ h))).injective ?_
  rw [conjugateIsoEquiv_trans _
      ((CondensedRing.upperStarLowerStarAdjunction Λ (g ≫ h)).comp
        (CondensedRing.upperStarLowerStarAdjunction Λ f)) _,
    conjugateIsoEquiv_trans _ (((CondensedRing.upperStarLowerStarAdjunction Λ h).comp
      (CondensedRing.upperStarLowerStarAdjunction Λ g)).comp
        (CondensedRing.upperStarLowerStarAdjunction Λ f)) _,
    conjugateIsoEquiv_trans _ (CondensedRing.upperStarLowerStarAdjunction Λ ((f ≫ g) ≫ h)) _,
    conjugateIsoEquiv_trans _ ((CondensedRing.upperStarLowerStarAdjunction Λ h).comp
      (CondensedRing.upperStarLowerStarAdjunction Λ (f ≫ g))) _]
  simp only [conjugateModuleComp Λ, conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_associator,
    Iso.trans_assoc]
  rw [moduleLowerStarComp_assoc Λ]
  congr 2
  rw [conjugateModuleCongr Λ (Category.assoc f g h).symm]
  exact (eqToIso_symm_congr (CondensedRing.lowerStar Λ) (Category.assoc f g h)).symm

private lemma moduleComp_id_left {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.upperStarComp Λ (𝟙 X) f =
      eqToIso (congrArg (fun k : X ⟶ Y ↦
        CondensedRing.upperStar Λ k) (Category.id_comp f)) ≪≫
      (CondensedRing.upperStar Λ f).rightUnitor.symm ≪≫
      Functor.isoWhiskerLeft (CondensedRing.upperStar Λ f)
        (profinitePointModuleIdentity Λ X).symm := by
  refine (conjugateIsoEquiv ((CondensedRing.upperStarLowerStarAdjunction Λ f).comp
    (CondensedRing.upperStarLowerStarAdjunction Λ (𝟙 X)))
    (CondensedRing.upperStarLowerStarAdjunction Λ (𝟙 X ≫ f))).injective ?_
  rw [conjugateIsoEquiv_trans _ (CondensedRing.upperStarLowerStarAdjunction Λ f) _,
    conjugateIsoEquiv_trans _ ((CondensedRing.upperStarLowerStarAdjunction Λ f).comp
      Adjunction.id) _]
  rw [conjugateModuleComp Λ, conjugateModuleCongr Λ (Category.id_comp f),
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_iso_symm, conjugateModuleId Λ,
    conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_rightUnitor, moduleLowerStarComp_id_left Λ]
  refine Iso.ext (NatTrans.ext (funext fun M ↦ ?_))
  simp

private lemma moduleComp_id_right {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.upperStarComp Λ f (𝟙 Y) =
      eqToIso (congrArg (fun k : X ⟶ Y ↦
        CondensedRing.upperStar Λ k) (Category.comp_id f)) ≪≫
      (CondensedRing.upperStar Λ f).leftUnitor.symm ≪≫
      Functor.isoWhiskerRight (profinitePointModuleIdentity Λ Y).symm
        (CondensedRing.upperStar Λ f) := by
  refine (conjugateIsoEquiv ((CondensedRing.upperStarLowerStarAdjunction Λ (𝟙 Y)).comp
    (CondensedRing.upperStarLowerStarAdjunction Λ f))
    (CondensedRing.upperStarLowerStarAdjunction Λ (f ≫ 𝟙 Y))).injective ?_
  rw [conjugateIsoEquiv_trans _ (CondensedRing.upperStarLowerStarAdjunction Λ f) _,
    conjugateIsoEquiv_trans _ (Adjunction.id.comp
      (CondensedRing.upperStarLowerStarAdjunction Λ f)) _]
  rw [conjugateModuleComp Λ, conjugateModuleCongr Λ (Category.comp_id f),
    conjugateIsoEquiv_isoWhiskerRight, conjugateIsoEquiv_iso_symm, conjugateModuleId Λ,
    conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_leftUnitor, moduleLowerStarComp_id_right Λ]
  refine Iso.ext (NatTrans.ext (funext fun M ↦ ?_))
  simp

private lemma moduleComp_assoc_app {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (M : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)) :
    (CondensedRing.upperStarComp Λ (f ≫ g) h).hom.app M ≫
        (CondensedRing.upperStarComp Λ f g).hom.app ((CondensedRing.upperStar Λ h).obj M) =
      (eqToHom (congrArg (CondensedRing.upperStar Λ) (Category.assoc f g h))).app M ≫
        (CondensedRing.upperStarComp Λ f (g ≫ h)).hom.app M ≫
        (CondensedRing.upperStar Λ f).map ((CondensedRing.upperStarComp Λ g h).hom.app M) := by
  have hc := moduleComp_assoc Λ f g h
  rw [eqToIso_congr_symm (CondensedRing.upperStar Λ) (Category.assoc f g h)] at hc
  have hc' := congrArg (fun e ↦
    eqToIso (congrArg (CondensedRing.upperStar Λ) (Category.assoc f g h)) ≪≫ e) hc
  simp only [Iso.self_symm_id_assoc] at hc'
  have ha := congrArg (fun e ↦ e.hom.app M) hc'
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.comp_id, eqToIso.hom] using ha.symm

end ModuleMates

/-- Module inverse images satisfy both unit equations and associativity.
Source: RefactorInstruction, Section 5, eq:triangle and thm:alpha
(auxiliary; not a blueprint node).

Proof: (6) Use the normalized linear lifts in profinite_point_pullback_module_comparison.
Apply the faithful forgetful functors and the corresponding abelian equations from step 3.
The coherence of coefficient maps in step 5 identifies all scalar actions. -/
theorem profinite_point_pullback_module_coherence
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      (CondensedRing.upperStarComp Λ (𝟙 X) f).hom.app M ≫
          (profinitePointModuleIdentity Λ X).hom.app ((CondensedRing.upperStar Λ f).obj M) =
        (eqToHom (congrArg (CondensedRing.upperStar Λ) (Category.id_comp f))).app M) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      (CondensedRing.upperStarComp Λ f (𝟙 Y)).hom.app M ≫
          (CondensedRing.upperStar Λ f).map ((profinitePointModuleIdentity Λ Y).hom.app M) =
        (eqToHom (congrArg (CondensedRing.upperStar Λ) (Category.comp_id f))).app M) ∧
    (∀ (X Y Z W : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
      (M : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)),
      (CondensedRing.upperStarComp Λ (f ≫ g) h).hom.app M ≫
          (CondensedRing.upperStarComp Λ f g).hom.app ((CondensedRing.upperStar Λ h).obj M) =
        (eqToHom (congrArg (CondensedRing.upperStar Λ) (Category.assoc f g h))).app M ≫
          (CondensedRing.upperStarComp Λ f (g ≫ h)).hom.app M ≫
          (CondensedRing.upperStar Λ f).map ((CondensedRing.upperStarComp Λ g h).hom.app M)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X Y f M
    rw [moduleComp_id_left Λ f]
    simp only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
      Functor.rightUnitor_inv_app, Category.id_comp, Category.assoc,
      Iso.inv_hom_id_app, Functor.id_obj, Category.comp_id]
  · intro X Y f M
    rw [moduleComp_id_right Λ f]
    simp only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom,
      Functor.leftUnitor_inv_app, Category.id_comp, Category.assoc,
      ← Functor.map_comp, Iso.inv_hom_id_app, Functor.id_obj,
      CategoryTheory.Functor.map_id, Category.comp_id]
  · intro X Y Z W f g h M
    exact moduleComp_assoc_app Λ f g h M

/-- Monoidality of the canonical abelian inverse-image composition comparison.
Source: RefactorInstruction, Section 5, eq:triangle and thm:alpha
(auxiliary; not a blueprint node).

Proof: (2) The sheafified Kan-extension inverse images have their canonical tensor
structures by the site inverse-image tensor theorem. (3) The composition comparison
is adjunction-compatible, so the monoidal comparison clause of that theorem applies.
Equivalently, conjugate the monoidal direct-image comparison and use the tensor mates. -/
@[instance]
theorem profinitePoint_isMonoidal_upperStarComp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} f g).hom := by
  have h₁ : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ g))
      Functor.Monoidal.toOplaxMonoidal _ :=
    isMonoidal_upperStarLowerStarAdjunction _ _
  have h₂ : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      ((upperStarLowerStarAdjunction Ab.{u + 1} g).comp
        (upperStarLowerStarAdjunction Ab.{u + 1} f))
      Functor.Monoidal.toOplaxMonoidal _ := Adjunction.isMonoidal_comp _ _
  have : NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} f g).symm.hom :=
    isMonoidal_conjugateEquiv_symm _ _ (lowerStarComp Ab.{u + 1} f g).inv
  exact inferInstanceAs (NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} f g).symm.inv)

/-- The canonical ring-object composition comparison, obtained by lifting the abelian or
linear comparison through the existing functor on algebraic structures or localization.
Source: RefactorInstruction, eq:triangle and thm:alpha; Stacks, Tags 00YV and 05RU
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointRingComp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (upperStar Ab.{u + 1} (f ≫ g)).mapMon ≅ (upperStar Ab.{u + 1} g).mapMon ⋙ (upperStar Ab.{u +
      1} f).mapMon :=
  Functor.mapMonNatIso (upperStarComp Ab.{u + 1} f g) ≪≫ Functor.mapMonCompIso

/-- The canonical ring-object identity comparison, using the existing lift of the
ordinary inverse-image identity and its normalization on the identity functor.
Source: RefactorInstruction, Section 5, eq:triangle; Stacks, Tags 00YV and 05RU
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointRingIdentity
    (X : Scheme.{u}) :
    (upperStar Ab.{u + 1} (𝟙 X)).mapMon ≅ 𝟭 (Mon (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})) :=
  Functor.mapMonNatIso (upperStarId Ab.{u + 1} X) ≪≫ Functor.mapMonIdIso

private lemma ringComparison_transport {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g)
    (M : Mon (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})) :
    ((eqToHom (congrArg (fun k ↦ (upperStar Ab.{u + 1} k).mapMon) w)).app M).hom =
      (eqToHom (congrArg (upperStar Ab.{u + 1}) w)).app M.X := by
  subst w
  rfl

/-- The ring-object inverse-image comparisons satisfy both units and associativity.
Source: RefactorInstruction, Section 5, eq:triangle and thm:alpha; Stacks, Tag 05RU
(auxiliary; not a blueprint node).

Proof: (5) Ring maps inherit the equations because forgetting multiplication is faithful.
(6) Module equations inherit them because forgetting the action is faithful.
(7) Apply the exact-functor derived factorization to the ordinary pullbacks. Naturality
at each differential makes the ordinary comparisons isomorphisms of complexes. The
localization universal property lifts them uniquely, preserves identity and composition,
and detects equality after precomposition with Q, so the degreewise unit and associativity
equations descend. (8) The two square routes are compared with the pullback of their common
composite; the same uniqueness identifies this comparison after localization. -/
theorem profinite_point_pullback_ring_coherence
    :
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (M : Mon (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})),
      (profinitePointRingComp (𝟙 X) f).hom.app M ≫
          (profinitePointRingIdentity X).hom.app ((upperStar Ab.{u + 1} f).mapMon.obj M) =
        (eqToHom (congrArg (fun k : X ⟶ Y ↦ (upperStar Ab.{u + 1} k).mapMon)
          (Category.id_comp f))).app M) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (M : Mon (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})),
      (profinitePointRingComp f (𝟙 Y)).hom.app M ≫
          (upperStar Ab.{u + 1} f).mapMon.map ((profinitePointRingIdentity Y).hom.app M) =
        (eqToHom (congrArg (fun k : X ⟶ Y ↦ (upperStar Ab.{u + 1} k).mapMon)
          (Category.comp_id f))).app M) ∧
    (∀ (X Y Z W : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
      (M : Mon (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})),
      (profinitePointRingComp (f ≫ g) h).hom.app M ≫
          (profinitePointRingComp f g).hom.app ((upperStar Ab.{u + 1} h).mapMon.obj M) =
        (eqToHom (congrArg (fun k : X ⟶ W ↦ (upperStar Ab.{u + 1} k).mapMon)
          (Category.assoc f g h))).app M ≫
          (profinitePointRingComp f (g ≫ h)).hom.app M ≫
          (upperStar Ab.{u + 1} f).mapMon.map ((profinitePointRingComp g h).hom.app M)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X Y f M
    apply Mon.Hom.ext
    simp only [profinitePointRingComp, profinitePointRingIdentity, Iso.trans_hom,
      NatTrans.comp_app, Mon.comp_hom', Functor.mapMonNatIso_hom_app_hom,
      Functor.mapMonCompIso_hom_app_hom, Functor.mapMonIdIso_hom_app_hom]
    exact profinite_point_pullback_abelian_coherence.1 X Y f M.X
  · intro X Y f M
    apply Mon.Hom.ext
    simp only [profinitePointRingComp, profinitePointRingIdentity, Iso.trans_hom,
      NatTrans.comp_app, Mon.comp_hom', Functor.mapMonNatIso_hom_app_hom,
      Functor.mapMonCompIso_hom_app_hom,
      Category.comp_id, ringComparison_transport]
    exact profinite_point_pullback_abelian_coherence.2.1 X Y f M.X
  · intro X Y Z W f g h M
    apply Mon.Hom.ext
    simp only [profinitePointRingComp, Iso.trans_hom, NatTrans.comp_app, Mon.comp_hom',
      Functor.mapMonNatIso_hom_app_hom, Functor.mapMonCompIso_hom_app_hom]
    exact profinite_point_pullback_abelian_coherence.2.2.1 X Y Z W f g h M.X

end AlgebraicGeometry.ProEtale

namespace CategoryTheory.Functor

section TransferUnits
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

private lemma derivedLeftUnit (I : D ⥤ D) [I.Additive]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (K : C ⥤ D) [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (c : K ≅ F ⋙ I) (i : I ≅ 𝟭 D) (w : K = F)
    (h : c ≪≫ isoWhiskerLeft F i = eqToIso w) (M : DerivedCategory C) :
    (mapDerivedCategoryNatIso c).hom.app M ≫
      (mapDerivedCategoryCompIso F I).inv.app M ≫
      (mapDerivedCategoryNatIso i).hom.app (F.mapDerivedCategory.obj M) ≫
      (mapDerivedCategoryIdIso D).hom.app (F.mapDerivedCategory.obj M) =
      (eqToHom (show K.mapDerivedCategory = F.mapDerivedCategory by cases w; rfl)).app M := by
  subst K
  simp only [eqToIso_refl] at h
  have hm := congrArg (fun e ↦ (mapDerivedCategoryNatIso e).hom.app M) h
  rw [mapDerivedCategoryNatIso_trans] at hm
  simp only [NatTrans.comp_app, mapDerivedCategoryNatIso_refl, NatTrans.id_app] at hm
  have hw := congr_app (CategoryTheory.Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F i) M
  simp only [NatTrans.comp_app, whiskerLeft_app] at hw
  rw [← reassoc_of% hw, reassoc_of% hm]
  simpa using congr_app (mapDerivedCategoryCompIso_comp_id F) M

private lemma derivedRightUnit (I : C ⥤ C) [I.Additive]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (K : C ⥤ D) [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (c : K ≅ I ⋙ F) (i : I ≅ 𝟭 C) (w : K = F)
    (h : c ≪≫ isoWhiskerRight i F = eqToIso w) (M : DerivedCategory C) :
    (mapDerivedCategoryNatIso c).hom.app M ≫
      (mapDerivedCategoryCompIso I F).inv.app M ≫
      F.mapDerivedCategory.map
        ((mapDerivedCategoryNatIso i).hom.app M ≫ (mapDerivedCategoryIdIso C).hom.app M) =
      (eqToHom (show K.mapDerivedCategory = F.mapDerivedCategory by cases w; rfl)).app M := by
  subst K
  simp only [eqToIso_refl] at h
  have hm := congrArg (fun e ↦ (mapDerivedCategoryNatIso e).hom.app M) h
  rw [mapDerivedCategoryNatIso_trans] at hm
  simp only [NatTrans.comp_app, mapDerivedCategoryNatIso_refl, NatTrans.id_app] at hm
  have hw := congr_app (CategoryTheory.Functor.mapDerivedCategoryNatIso_isoWhiskerRight i F) M
  simp only [NatTrans.comp_app, whiskerRight_app] at hw
  simp only [Functor.map_comp]
  rw [← reassoc_of% hw, reassoc_of% hm]
  simpa using congr_app (mapDerivedCategoryCompIso_id_comp F) M
end TransferUnits

section TransferAssociativity
variable {C D E J : Type*} [Category C] [Category D] [Category E] [Category J]
  [Abelian C] [Abelian D] [Abelian E] [Abelian J]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory J]
  (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ J)
  (P : C ⥤ E) (Q : D ⥤ J) (R R' : C ⥤ J)
  [F.Additive] [G.Additive] [H.Additive] [P.Additive] [Q.Additive] [R.Additive] [R'.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R']

private lemma derivedAssociativity
    (c₀ : R' ≅ F ⋙ Q) (c₁ : Q ≅ G ⋙ H) (c₂ : R ≅ P ⋙ H) (c₃ : P ≅ F ⋙ G)
    (w : R' = R)
    (h : c₀ ≪≫ isoWhiskerLeft F c₁ = eqToIso w ≪≫ c₂ ≪≫ isoWhiskerRight c₃ H)
    (M : DerivedCategory C) :
    (mapDerivedCategoryNatIso c₀).hom.app M ≫
        (mapDerivedCategoryCompIso F Q).inv.app M ≫
        ((mapDerivedCategoryNatIso c₁).hom.app (F.mapDerivedCategory.obj M) ≫
          (mapDerivedCategoryCompIso G H).inv.app (F.mapDerivedCategory.obj M)) =
      (eqToHom (show R'.mapDerivedCategory = R.mapDerivedCategory by cases w; rfl)).app M ≫
        (mapDerivedCategoryNatIso c₂).hom.app M ≫
        (mapDerivedCategoryCompIso P H).inv.app M ≫
        H.mapDerivedCategory.map ((mapDerivedCategoryNatIso c₃).hom.app M ≫
          (mapDerivedCategoryCompIso F G).inv.app M) := by
  subst R'
  simp only [eqToIso_refl, Iso.refl_trans] at h
  have hm := congrArg (fun e ↦ (mapDerivedCategoryNatIso e).hom.app M) h.symm
  simp only [mapDerivedCategoryNatIso_trans, NatTrans.comp_app] at hm
  have hWR := congr_app (CategoryTheory.Functor.mapDerivedCategoryNatIso_isoWhiskerRight c₃ H) M
  have hWL := congr_app (CategoryTheory.Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F c₁) M
  have hA := congr_app (mapDerivedCategoryCompIso_assoc F G H) M
  simp only [NatTrans.comp_app, whiskerRight_app] at hWR
  simp only [NatTrans.comp_app, whiskerLeft_app] at hWL
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at hA
  simp only [Functor.map_comp]
  simp only [eqToHom_refl, NatTrans.id_app, Category.id_comp]
  symm
  rw [← reassoc_of% hWR, reassoc_of% hm, ← hA, reassoc_of% hWL]
end TransferAssociativity

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open scoped CategoryTheory.Obj

/-- The canonical termwise derived composition comparison, obtained by lifting the abelian or
linear comparison through the existing functor on algebraic structures or localization.
Source: RefactorInstruction, eq:triangle and thm:alpha; Stacks, Tags 00YV and 05RU
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointAbelianDerivedComp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (upperStar Ab.{u + 1} (f ≫ g)).mapDerivedCategory ≅
      (upperStar Ab.{u + 1} g).mapDerivedCategory ⋙ (upperStar Ab.{u + 1} f).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (upperStarComp Ab.{u + 1} f g) ≪≫
    (Functor.mapDerivedCategoryCompIso (upperStar Ab.{u + 1} g) (upperStar Ab.{u + 1} f)).symm

/-- The canonical termwise derived identity comparison, using the existing lift of the
ordinary inverse-image identity and its normalization on the identity functor.
Source: RefactorInstruction, Section 5, eq:triangle; Stacks, Tags 00YV and 05RU
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointAbelianDerivedIdentity
    (X : Scheme.{u}) :
    (upperStar Ab.{u + 1} (𝟙 X)).mapDerivedCategory ≅ 𝟭 (DerivedCategory (Sheaf
      (Scheme.ProEt.topology X) Ab.{u + 1})) :=
  Functor.mapDerivedCategoryNatIso (upperStarId Ab.{u + 1} X) ≪≫ Functor.mapDerivedCategoryIdIso _

private lemma abelianDerived_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g) :
    (Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (fun k : X ⟶ Y ↦ upperStar Ab.{u + 1} k) w))).hom =
      eqToHom (congrArg (fun k : X ⟶ Y ↦ (upperStar Ab.{u + 1} k).mapDerivedCategory) w) := by
  subst w
  exact Functor.mapDerivedCategoryNatIso_refl

/-- The termwise derived inverse-image comparisons satisfy both units and associativity.
The square clause identifies the derived square comparison with the unique descent of
the termwise ordinary comparison through the common composite.
Source: RefactorInstruction, Section 5, eq:triangle and thm:alpha; Stacks, Tag 05RU
(auxiliary; not a blueprint node).

Proof: (5) Ring maps inherit the equations because forgetting multiplication is faithful.
(6) Module equations inherit them because forgetting the action is faithful.
(7) Apply the exact-functor derived factorization to the ordinary pullbacks. Naturality
at each differential makes the ordinary comparisons isomorphisms of complexes. The
localization universal property lifts them uniquely, preserves identity and composition,
and detects equality after precomposition with Q, so the degreewise unit and associativity
equations descend. (8) The two square routes are compared with the pullback of their common
composite; the same uniqueness identifies this comparison after localization. -/
theorem profinite_point_pullback_abelianderived_coherence
    :
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) Ab.{u
      + 1})),
      (profinitePointAbelianDerivedComp (𝟙 X) f).hom.app M ≫
          (profinitePointAbelianDerivedIdentity X).hom.app ((upperStar Ab.{u + 1}
            f).mapDerivedCategory.obj M) =
        (eqToHom (congrArg (fun k : X ⟶ Y ↦ (upperStar Ab.{u + 1} k).mapDerivedCategory)
          (Category.id_comp f))).app M) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) Ab.{u
      + 1})),
      (profinitePointAbelianDerivedComp f (𝟙 Y)).hom.app M ≫
          (upperStar Ab.{u + 1} f).mapDerivedCategory.map ((profinitePointAbelianDerivedIdentity
            Y).hom.app M) =
        (eqToHom (congrArg (fun k : X ⟶ Y ↦ (upperStar Ab.{u + 1} k).mapDerivedCategory)
          (Category.comp_id f))).app M) ∧
    (∀ (X Y Z W : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
      (M : DerivedCategory (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})),
      (profinitePointAbelianDerivedComp (f ≫ g) h).hom.app M ≫
          (profinitePointAbelianDerivedComp f g).hom.app ((upperStar Ab.{u + 1}
            h).mapDerivedCategory.obj M) =
        (eqToHom (congrArg (fun k : X ⟶ W ↦ (upperStar Ab.{u + 1} k).mapDerivedCategory)
          (Category.assoc f g h))).app M ≫
          (profinitePointAbelianDerivedComp f (g ≫ h)).hom.app M ≫
          (upperStar Ab.{u + 1} f).mapDerivedCategory.map ((profinitePointAbelianDerivedComp g
            h).hom.app M)) ∧
    (∀ (X' X Y' Y : Scheme.{u}) (b : X' ⟶ X) (f : X ⟶ Y)
      (f' : X' ⟶ Y') (g : Y' ⟶ Y) (w : b ≫ f = f' ≫ g) (M : DerivedCategory (Sheaf
        (Scheme.ProEt.topology Y) Ab.{u + 1})),
      (profinitePointAbelianDerivedComp b f).inv.app M ≫
          (eqToHom (congrArg (fun k : X' ⟶ Y ↦ (upperStar Ab.{u + 1} k).mapDerivedCategory)
            w)).app M ≫
          (profinitePointAbelianDerivedComp f' g).hom.app M =
        (Functor.mapDerivedCategoryCompIso (upperStar Ab.{u + 1} f) (upperStar Ab.{u + 1}
          b)).hom.app M ≫
          (Functor.mapDerivedCategoryNatIso
            ((upperStarComp Ab.{u + 1} b f).symm ≪≫
              eqToIso (congrArg (fun k : X' ⟶ Y ↦ (upperStar Ab.{u + 1} k)) w) ≪≫
              (upperStarComp Ab.{u + 1} f' g))).hom.app M ≫
          (Functor.mapDerivedCategoryCompIso (upperStar Ab.{u + 1} g) (upperStar Ab.{u + 1}
            f')).inv.app M) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y f M
    have h : upperStarComp Ab.{u + 1} (𝟙 X) f ≪≫
        Functor.isoWhiskerLeft (upperStar Ab.{u + 1} f) (upperStarId Ab.{u + 1} X) =
        eqToIso (congrArg (upperStar Ab.{u + 1}) (Category.id_comp f)) := by
      apply Iso.ext
      apply NatTrans.ext
      funext N
      exact profinite_point_pullback_abelian_coherence.1 X Y f N
    simpa only [profinitePointAbelianDerivedComp, profinitePointAbelianDerivedIdentity,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc] using
      CategoryTheory.Functor.derivedLeftUnit (upperStar Ab.{u + 1} f)
        (upperStar Ab.{u + 1} (𝟙 X)) (upperStar Ab.{u + 1} (𝟙 X ≫ f))
        (upperStarComp Ab.{u + 1} (𝟙 X) f) (upperStarId Ab.{u + 1} X)
        (congrArg (upperStar Ab.{u + 1}) (Category.id_comp f)) h M
  · intro X Y f M
    have h : upperStarComp Ab.{u + 1} f (𝟙 Y) ≪≫
        Functor.isoWhiskerRight (upperStarId Ab.{u + 1} Y) (upperStar Ab.{u + 1} f) =
        eqToIso (congrArg (upperStar Ab.{u + 1}) (Category.comp_id f)) := by
      apply Iso.ext
      apply NatTrans.ext
      funext N
      exact profinite_point_pullback_abelian_coherence.2.1 X Y f N
    simpa only [profinitePointAbelianDerivedComp, profinitePointAbelianDerivedIdentity,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc] using
      CategoryTheory.Functor.derivedRightUnit (upperStar Ab.{u + 1} f)
        (upperStar Ab.{u + 1} (𝟙 Y)) (upperStar Ab.{u + 1} (f ≫ 𝟙 Y))
        (upperStarComp Ab.{u + 1} f (𝟙 Y)) (upperStarId Ab.{u + 1} Y)
        (congrArg (upperStar Ab.{u + 1}) (Category.comp_id f)) h M
  · intro X Y Z W f g h M
    have hc : upperStarComp Ab.{u + 1} (f ≫ g) h ≪≫
        Functor.isoWhiskerLeft (upperStar Ab.{u + 1} h) (upperStarComp Ab.{u + 1} f g) =
        eqToIso (congrArg (upperStar Ab.{u + 1}) (Category.assoc f g h)) ≪≫
          upperStarComp Ab.{u + 1} f (g ≫ h) ≪≫
          Functor.isoWhiskerRight (upperStarComp Ab.{u + 1} g h) (upperStar Ab.{u + 1} f) := by
      apply Iso.ext
      apply NatTrans.ext
      funext N
      simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
        Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
        eqToIso.hom, Category.assoc] using
        profinite_point_pullback_abelian_coherence.2.2.1 X Y Z W f g h N
    simpa only [profinitePointAbelianDerivedComp, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Category.assoc] using
      CategoryTheory.Functor.derivedAssociativity
        (upperStar Ab.{u + 1} h) (upperStar Ab.{u + 1} g) (upperStar Ab.{u + 1} f)
        (upperStar Ab.{u + 1} (g ≫ h)) (upperStar Ab.{u + 1} (f ≫ g))
        (upperStar Ab.{u + 1} (f ≫ g ≫ h)) (upperStar Ab.{u + 1} ((f ≫ g) ≫ h))
        (upperStarComp Ab.{u + 1} (f ≫ g) h) (upperStarComp Ab.{u + 1} f g)
        (upperStarComp Ab.{u + 1} f (g ≫ h)) (upperStarComp Ab.{u + 1} g h)
        (congrArg (upperStar Ab.{u + 1}) (Category.assoc f g h)) hc M
  · intro X' X Y' Y b f f' g w M
    simp only [profinitePointAbelianDerivedComp, Iso.trans_inv, Iso.trans_hom,
      Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.mapDerivedCategoryNatIso_trans,
      Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
    rw [abelianDerived_congr w]

/-- The canonical termwise derived composition comparison, obtained by lifting the abelian or
linear comparison through the existing functor on algebraic structures or localization.
Source: RefactorInstruction, eq:triangle and thm:alpha; Stacks, Tags 00YV and 05RU
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointModuleDerivedComp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (CondensedRing.upperStar Λ (f ≫ g)).mapDerivedCategory ≅
      (CondensedRing.upperStar Λ g).mapDerivedCategory ⋙ (CondensedRing.upperStar Λ
        f).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp Λ f g) ≪≫
    (Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar Λ g)
      (CondensedRing.upperStar Λ f)).symm

/-- The canonical termwise derived identity comparison, using the existing lift of the
ordinary inverse-image identity and its normalization on the identity functor.
Source: RefactorInstruction, Section 5, eq:triangle; Stacks, Tags 00YV and 05RU
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointModuleDerivedIdentity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) :
    (CondensedRing.upperStar Λ (𝟙 X)).mapDerivedCategory ≅ 𝟭 (DerivedCategory (Mod (Sheaf
      (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
  Functor.mapDerivedCategoryNatIso (profinitePointModuleIdentity Λ X) ≪≫
      Functor.mapDerivedCategoryIdIso _

private lemma moduleDerived_congr
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g) :
    (Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (fun k : X ⟶ Y ↦ CondensedRing.upperStar Λ k) w))).hom =
      eqToHom (congrArg (fun k : X ⟶ Y ↦ (CondensedRing.upperStar Λ k).mapDerivedCategory) w) := by
  subst w
  exact Functor.mapDerivedCategoryNatIso_refl

/-- The termwise derived inverse-image comparisons satisfy both units and associativity.
The square clause identifies the derived square comparison with the unique descent of
the termwise ordinary comparison through the common composite.
Source: RefactorInstruction, Section 5, eq:triangle and thm:alpha; Stacks, Tag 05RU
(auxiliary; not a blueprint node).

Proof: (5) Ring maps inherit the equations because forgetting multiplication is faithful.
(6) Module equations inherit them because forgetting the action is faithful.
(7) Apply the exact-functor derived factorization to the ordinary pullbacks. Naturality
at each differential makes the ordinary comparisons isomorphisms of complexes. The
localization universal property lifts them uniquely, preserves identity and composition,
and detects equality after precomposition with Q, so the degreewise unit and associativity
equations descend. (8) The two square routes are compared with the pullback of their common
composite; the same uniqueness identifies this comparison after localization. -/
theorem profinite_point_pullback_modulederived_coherence
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    :
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y)
      Ab.{u + 1}) (condensedRingObj Λ Y))),
      (profinitePointModuleDerivedComp Λ (𝟙 X) f).hom.app M ≫
          (profinitePointModuleDerivedIdentity Λ X).hom.app ((CondensedRing.upperStar Λ
            f).mapDerivedCategory.obj M) =
        (eqToHom (congrArg (fun k : X ⟶ Y ↦ (CondensedRing.upperStar Λ k).mapDerivedCategory)
          (Category.id_comp f))).app M) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y)
      Ab.{u + 1}) (condensedRingObj Λ Y))),
      (profinitePointModuleDerivedComp Λ f (𝟙 Y)).hom.app M ≫
          (CondensedRing.upperStar Λ f).mapDerivedCategory.map
            ((profinitePointModuleDerivedIdentity Λ Y).hom.app M) =
        (eqToHom (congrArg (fun k : X ⟶ Y ↦ (CondensedRing.upperStar Λ k).mapDerivedCategory)
          (Category.comp_id f))).app M) ∧
    (∀ (X Y Z W : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
      (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ
        W))),
      (profinitePointModuleDerivedComp Λ (f ≫ g) h).hom.app M ≫
          (profinitePointModuleDerivedComp Λ f g).hom.app ((CondensedRing.upperStar Λ
            h).mapDerivedCategory.obj M) =
        (eqToHom (congrArg (fun k : X ⟶ W ↦ (CondensedRing.upperStar Λ k).mapDerivedCategory)
          (Category.assoc f g h))).app M ≫
          (profinitePointModuleDerivedComp Λ f (g ≫ h)).hom.app M ≫
          (CondensedRing.upperStar Λ f).mapDerivedCategory.map ((profinitePointModuleDerivedComp Λ
            g h).hom.app M)) ∧
    (∀ (X' X Y' Y : Scheme.{u}) (b : X' ⟶ X) (f : X ⟶ Y)
      (f' : X' ⟶ Y') (g : Y' ⟶ Y) (w : b ≫ f = f' ≫ g) (M : DerivedCategory (Mod (Sheaf
        (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))),
      (profinitePointModuleDerivedComp Λ b f).inv.app M ≫
          (eqToHom (congrArg (fun k : X' ⟶ Y ↦ (CondensedRing.upperStar Λ k).mapDerivedCategory)
            w)).app M ≫
          (profinitePointModuleDerivedComp Λ f' g).hom.app M =
        (Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar Λ f) (CondensedRing.upperStar
          Λ b)).hom.app M ≫
          (Functor.mapDerivedCategoryNatIso
            ((CondensedRing.upperStarComp Λ b f).symm ≪≫
              eqToIso (congrArg (fun k : X' ⟶ Y ↦ (CondensedRing.upperStar Λ k)) w) ≪≫
              (CondensedRing.upperStarComp Λ f' g))).hom.app M ≫
          (Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar Λ g)
            (CondensedRing.upperStar Λ f')).inv.app M) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y f M
    have h : CondensedRing.upperStarComp Λ (𝟙 X) f ≪≫
        Functor.isoWhiskerLeft (CondensedRing.upperStar Λ f) (profinitePointModuleIdentity Λ X) =
        eqToIso (congrArg (CondensedRing.upperStar Λ) (Category.id_comp f)) := by
      apply Iso.ext
      apply NatTrans.ext
      funext N
      exact (profinite_point_pullback_module_coherence Λ).1 X Y f N
    simpa only [profinitePointModuleDerivedComp, profinitePointModuleDerivedIdentity,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc] using
      CategoryTheory.Functor.derivedLeftUnit (CondensedRing.upperStar Λ f)
        (CondensedRing.upperStar Λ (𝟙 X)) (CondensedRing.upperStar Λ (𝟙 X ≫ f))
        (CondensedRing.upperStarComp Λ (𝟙 X) f) (profinitePointModuleIdentity Λ X)
        (congrArg (CondensedRing.upperStar Λ) (Category.id_comp f)) h M
  · intro X Y f M
    have h : CondensedRing.upperStarComp Λ f (𝟙 Y) ≪≫
        Functor.isoWhiskerRight (profinitePointModuleIdentity Λ Y) (CondensedRing.upperStar Λ f) =
        eqToIso (congrArg (CondensedRing.upperStar Λ) (Category.comp_id f)) := by
      apply Iso.ext
      apply NatTrans.ext
      funext N
      exact (profinite_point_pullback_module_coherence Λ).2.1 X Y f N
    simpa only [profinitePointModuleDerivedComp, profinitePointModuleDerivedIdentity,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc] using
      CategoryTheory.Functor.derivedRightUnit (CondensedRing.upperStar Λ f)
        (CondensedRing.upperStar Λ (𝟙 Y)) (CondensedRing.upperStar Λ (f ≫ 𝟙 Y))
        (CondensedRing.upperStarComp Λ f (𝟙 Y)) (profinitePointModuleIdentity Λ Y)
        (congrArg (CondensedRing.upperStar Λ) (Category.comp_id f)) h M
  · intro X Y Z W f g h M
    have hc : CondensedRing.upperStarComp Λ (f ≫ g) h ≪≫
        Functor.isoWhiskerLeft (CondensedRing.upperStar Λ h) (CondensedRing.upperStarComp Λ f g) =
        eqToIso (congrArg (CondensedRing.upperStar Λ) (Category.assoc f g h)) ≪≫
          CondensedRing.upperStarComp Λ f (g ≫ h) ≪≫
          Functor.isoWhiskerRight (CondensedRing.upperStarComp Λ g h)
            (CondensedRing.upperStar Λ f) := by
      apply Iso.ext
      apply NatTrans.ext
      funext N
      simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
        Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
        eqToIso.hom, Category.assoc] using
        (profinite_point_pullback_module_coherence Λ).2.2 X Y Z W f g h N
    simpa only [profinitePointModuleDerivedComp, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Category.assoc] using
      CategoryTheory.Functor.derivedAssociativity
        (CondensedRing.upperStar Λ h) (CondensedRing.upperStar Λ g) (CondensedRing.upperStar Λ f)
        (CondensedRing.upperStar Λ (g ≫ h)) (CondensedRing.upperStar Λ (f ≫ g))
        (CondensedRing.upperStar Λ (f ≫ g ≫ h)) (CondensedRing.upperStar Λ ((f ≫ g) ≫ h))
        (CondensedRing.upperStarComp Λ (f ≫ g) h) (CondensedRing.upperStarComp Λ f g)
        (CondensedRing.upperStarComp Λ f (g ≫ h)) (CondensedRing.upperStarComp Λ g h)
        (congrArg (CondensedRing.upperStar Λ) (Category.assoc f g h)) hc M
  · intro X' X Y' Y b f f' g w M
    simp only [profinitePointModuleDerivedComp, Iso.trans_inv, Iso.trans_hom,
      Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.mapDerivedCategoryNatIso_trans,
      Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
    rw [moduleDerived_congr Λ w]

private lemma ringLiftUnderlying
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
    (e : F ⋙ G ≅ H) [NatTrans.IsMonoidal e.hom] (R : Mon C) :
    (((Functor.mapMonCompIso (F := F) (G := G)).symm.app R ≪≫
      (Functor.mapMonNatIso e).app R).hom).hom = e.hom.app R.X := by
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Mon.comp_hom',
    Functor.mapMonCompIso_inv_app_hom, Functor.mapMonNatIso_hom_app_hom]
  exact Category.id_comp _

/-- The coefficient comparison is the ring lift of the stipulated point comparison.
Its component preserves both multiplication and addition because it is a morphism in
monoid objects of abelian sheaves; commutative rings remain commutative by braidedness.
Source: RefactorInstruction, Section 5, thm:alpha
(auxiliary; not a blueprint node).

Proof: (5) Apply the monoidal natural isomorphism to a ring object. Naturality with
respect to every operation gives the ring map; the construction of mapMonNatIso gives
the asserted underlying component. Its inverse is also a ring map. The coefficient
identity and composition equations are the earlier abelian equations under a faithful
forgetful functor, so they hold as equations of ring maps as well. -/
theorem profinite_point_pullback_ring_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) :
    (coefficientPullbackIso f Λ).hom.hom = (upperStarFromPointComp f).hom.app Λ.X := by
  exact ringLiftUnderlying (upperStarFromPoint Y) (upperStar Ab.{u + 1} f)
    (upperStarFromPoint X) (upperStarFromPointComp f) Λ

private lemma moduleForget_transport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (Mod.forget (condensedRingObj Λ X)).map
        ((eqToHom (congrArg (fun k : X ⟶ Y ↦ CondensedRing.upperStar Λ k) w)).app M) ≫
        (profinitePointModuleForgetPullbackIso Λ g).hom.app M =
      (profinitePointModuleForgetPullbackIso Λ f).hom.app M ≫
        (eqToHom (congrArg (upperStar Ab.{u + 1}) w)).app M.X := by
  subst w
  simp only [eqToHom_refl, NatTrans.id_app]
  erw [Category.id_comp]
private lemma squareOfMorphisms
    {C : Type*} [Category C] {A B A' B' D E D' E' : C}
    (s : A ⟶ B) (si : B ⟶ A) (t : A' ⟶ B')
    (a : D ⟶ E) (ai : E ⟶ D) (b : D' ⟶ E')
    (p : A ⟶ D) (q : B ⟶ E) (p' : A' ⟶ D') (q' : B' ⟶ E')
    (v : A ⟶ A') (w : D ⟶ D')
    (his : si ≫ s = 𝟙 B) (hai : a ≫ ai = 𝟙 D)
    (hs : s ≫ q = p ≫ a) (ht : t ≫ q' = p' ≫ b)
    (hw : v ≫ p' = p ≫ w) :
    si ≫ v ≫ t ≫ q' = q ≫ ai ≫ w ≫ b := by
  calc
    si ≫ v ≫ t ≫ q' = si ≫ p ≫ w ≫ b := by
      rw [ht, reassoc_of% hw]
    _ = si ≫ p ≫ a ≫ ai ≫ w ≫ b := by
      rw [reassoc_of% hai]
    _ = si ≫ s ≫ q ≫ ai ≫ w ≫ b := by
      rw [reassoc_of% hs]
    _ = q ≫ ai ≫ w ≫ b := by
      rw [reassoc_of% his]

/-- The module square comparison has precisely the underlying abelian square map
obtained via the common composite. The displayed normalization prevents an arbitrary
choice of an isomorphism between the two module pullbacks.
Source: RefactorInstruction, Section 5, eq:triangle and thm:alpha
(auxiliary; not a blueprint node).

Proof: (8) Use the inverse of the linear composition comparison for the first route,
transport along the given equality of composite scheme maps, then use the comparison
for the second route. Step 6 identifies these maps after forgetting the module actions
with their abelian counterparts. Step 5 identifies both routes on coefficients with
the point comparison for the common morphism. This gives exactly the equation below. -/
theorem profinite_point_pullback_module_square
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} (b : X' ⟶ X) (f : X ⟶ Y)
    (f' : X' ⟶ Y') (g : Y' ⟶ Y) (w : b ≫ f = f' ≫ g)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (Mod.forget (condensedRingObj Λ X')).map
        ((CondensedRing.upperStarComp Λ b f).inv.app M ≫
          (eqToHom (congrArg (fun k : X' ⟶ Y ↦ CondensedRing.upperStar Λ k) w)).app M ≫
          (CondensedRing.upperStarComp Λ f' g).hom.app M) ≫
        (profinitePointModuleForgetPullbackIso Λ f').hom.app
          ((CondensedRing.upperStar Λ g).obj M) ≫
        (upperStar Ab.{u + 1} f').map
          ((profinitePointModuleForgetPullbackIso Λ g).hom.app M) =
      (profinitePointModuleForgetPullbackIso Λ b).hom.app
          ((CondensedRing.upperStar Λ f).obj M) ≫
        (upperStar Ab.{u + 1} b).map
          ((profinitePointModuleForgetPullbackIso Λ f).hom.app M) ≫
        (upperStarComp Ab.{u + 1} b f).inv.app M.X ≫
        (eqToHom (congrArg (upperStar Ab.{u + 1}) w)).app M.X ≫
        (upperStarComp Ab.{u + 1} f' g).hom.app M.X := by
  let V : Mod (Sheaf (Scheme.ProEt.topology X') Ab.{u + 1})
      (condensedRingObj Λ X') ⥤ Sheaf (Scheme.ProEt.topology X') Ab.{u + 1} :=
    Mod.forget (condensedRingObj Λ X')
  have his : V.map ((CondensedRing.upperStarComp Λ b f).inv.app M) ≫
      V.map ((CondensedRing.upperStarComp Λ b f).hom.app M) = 𝟙 _ := by
    rw [← V.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have hh := squareOfMorphisms
    (V.map ((CondensedRing.upperStarComp Λ b f).hom.app M))
    (V.map ((CondensedRing.upperStarComp Λ b f).inv.app M))
    (V.map ((CondensedRing.upperStarComp Λ f' g).hom.app M))
    ((upperStarComp Ab.{u + 1} b f).hom.app M.X)
    ((upperStarComp Ab.{u + 1} b f).inv.app M.X)
    ((upperStarComp Ab.{u + 1} f' g).hom.app M.X)
    ((profinitePointModuleForgetPullbackIso Λ (b ≫ f)).hom.app M)
    ((profinitePointModuleForgetPullbackIso Λ b).hom.app
      ((CondensedRing.upperStar Λ f).obj M) ≫
      (upperStar Ab.{u + 1} b).map ((profinitePointModuleForgetPullbackIso Λ f).hom.app M))
    ((profinitePointModuleForgetPullbackIso Λ (f' ≫ g)).hom.app M)
    ((profinitePointModuleForgetPullbackIso Λ f').hom.app
      ((CondensedRing.upperStar Λ g).obj M) ≫
      (upperStar Ab.{u + 1} f').map ((profinitePointModuleForgetPullbackIso Λ g).hom.app M))
    (V.map ((eqToHom (congrArg
      (fun k : X' ⟶ Y ↦ CondensedRing.upperStar Λ k) w)).app M))
    ((eqToHom (congrArg (upperStar Ab.{u + 1}) w)).app M.X)
    his (Iso.hom_inv_id_app _ M.X)
    ((profinite_point_pullback_module_comparison Λ).2.2 X' X Y b f M)
    ((profinite_point_pullback_module_comparison Λ).2.2 X' Y' Y f' g M)
    (moduleForget_transport Λ w M)
  simpa only [V, Functor.map_comp, Category.assoc] using hh

/-- The geometric set inverse image for an arbitrary scheme is the point inverse image
followed by the actual scheme inverse image along its structure morphism.
Source: RefactorInstruction, prop:pX and eq:triangle
(auxiliary; not a blueprint node). -/
noncomputable abbrev profinitePointSetSchemeInverseImage (X : Scheme.{u}) :=
  profinitePointSetInverseImage.{u} ⋙
    Scheme.proEtaleSheafInverseImage (toSpecZ X) (Type (u + 1))

/-- Set inverse-image composition, conjugate to the canonical direct-image comparison.
Source: RefactorInstruction, Section 5, eq:triangle; Stacks, Tag 03CB
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointSetComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Scheme.proEtaleSheafInverseImage (f ≫ g) (Type (u + 1)) ≅
      Scheme.proEtaleSheafInverseImage g (Type (u + 1)) ⋙
        Scheme.proEtaleSheafInverseImage f (Type (u + 1)) :=
  ((conjugateIsoEquiv (Scheme.proEtaleSheafAdjunction (f ≫ g) (Type (u + 1)))
      ((Scheme.proEtaleSheafAdjunction g (Type (u + 1))).comp
        (Scheme.proEtaleSheafAdjunction f (Type (u + 1))))).symm
    (lowerStarComp (Type (u + 1)) f g).symm).symm

/-- Set inverse-image identity, conjugate to the canonical direct-image identity.
Source: RefactorInstruction, Section 5, eq:triangle; Stacks, Tag 03CB
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointSetIdentity (X : Scheme.{u}) :
    Scheme.proEtaleSheafInverseImage (𝟙 X) (Type (u + 1)) ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id
    (Scheme.proEtaleSheafAdjunction (𝟙 X) (Type (u + 1)))).symm
      (lowerStarId (Type (u + 1)) X).symm

/-- The set-level point comparison is composition followed by the structure-map equality.
Source: RefactorInstruction, Section 5, eq:triangle
(auxiliary; not a blueprint node). -/
noncomputable def profinitePointSetSchemeComp {X Y : Scheme.{u}} (f : X ⟶ Y) :
    profinitePointSetSchemeInverseImage Y ⋙
        Scheme.proEtaleSheafInverseImage f (Type (u + 1)) ≅
      profinitePointSetSchemeInverseImage X :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft profinitePointSetInverseImage
    ((profinitePointSetComp f (toSpecZ Y)).symm ≪≫
      eqToIso (congrArg
        (fun k : X ⟶ specZ ↦ Scheme.proEtaleSheafInverseImage k (Type (u + 1)))
        (comp_toSpecZ f)))

private lemma conjugateSetComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateIsoEquiv ((Scheme.proEtaleSheafAdjunction g (Type (u + 1))).comp
      (Scheme.proEtaleSheafAdjunction f (Type (u + 1))))
      (Scheme.proEtaleSheafAdjunction (f ≫ g) (Type (u + 1)))
      (profinitePointSetComp f g) = lowerStarComp (Type (u + 1)) f g := by
  rw [profinitePointSetComp, conjugateIsoEquiv_iso_symm]
  simp

private lemma conjugateSetId (X : Scheme.{u}) :
    conjugateIsoEquiv Adjunction.id (Scheme.proEtaleSheafAdjunction (𝟙 X) (Type (u + 1)))
      (profinitePointSetIdentity X) = (lowerStarId (Type (u + 1)) X).symm := by
  exact (conjugateIsoEquiv Adjunction.id
    (Scheme.proEtaleSheafAdjunction (𝟙 X) (Type (u + 1)))).apply_symm_apply _

private lemma conjugateSetCongr {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g) :
    conjugateIsoEquiv (Scheme.proEtaleSheafAdjunction g (Type (u + 1)))
      (Scheme.proEtaleSheafAdjunction f (Type (u + 1)))
      (eqToIso (congrArg (fun k : X ⟶ Y ↦
        Scheme.proEtaleSheafInverseImage k (Type (u + 1))) w)) =
      (lowerStarCongr (Type (u + 1)) w).symm := by
  subst w
  apply Iso.ext
  exact conjugateEquiv_id (Scheme.proEtaleSheafAdjunction f (Type (u + 1)))

private lemma setComp_assoc {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    profinitePointSetComp f (g ≫ h) ≪≫
        Functor.isoWhiskerRight (profinitePointSetComp g h)
          (Scheme.proEtaleSheafInverseImage f (Type (u + 1))) ≪≫
        Functor.associator _ _ _ =
      eqToIso (congrArg (fun k : X ⟶ W ↦
        Scheme.proEtaleSheafInverseImage k (Type (u + 1))) (Category.assoc f g h).symm) ≪≫
        profinitePointSetComp (f ≫ g) h ≪≫
        Functor.isoWhiskerLeft (Scheme.proEtaleSheafInverseImage h (Type (u + 1)))
          (profinitePointSetComp f g) := by
  refine (conjugateIsoEquiv ((Scheme.proEtaleSheafAdjunction h (Type (u + 1))).comp
    ((Scheme.proEtaleSheafAdjunction g (Type (u + 1))).comp
      (Scheme.proEtaleSheafAdjunction f (Type (u + 1)))))
    (Scheme.proEtaleSheafAdjunction (f ≫ g ≫ h) (Type (u + 1)))).injective ?_
  rw [conjugateIsoEquiv_trans _ ((Scheme.proEtaleSheafAdjunction (g ≫ h)
      (Type (u + 1))).comp (Scheme.proEtaleSheafAdjunction f (Type (u + 1)))) _,
    conjugateIsoEquiv_trans _ (((Scheme.proEtaleSheafAdjunction h (Type (u + 1))).comp
      (Scheme.proEtaleSheafAdjunction g (Type (u + 1)))).comp
        (Scheme.proEtaleSheafAdjunction f (Type (u + 1)))) _,
    conjugateIsoEquiv_trans _ (Scheme.proEtaleSheafAdjunction ((f ≫ g) ≫ h)
      (Type (u + 1))) _,
    conjugateIsoEquiv_trans _ ((Scheme.proEtaleSheafAdjunction h (Type (u + 1))).comp
      (Scheme.proEtaleSheafAdjunction (f ≫ g) (Type (u + 1)))) _]
  simp only [conjugateSetComp, conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_associator,
    Iso.trans_assoc]
  rw [legacy_lowerStarComp_assoc]
  congr 2
  rw [conjugateSetCongr (Category.assoc f g h).symm]
  rfl

private lemma setComp_id_left {X Y : Scheme.{u}} (f : X ⟶ Y) :
    profinitePointSetComp (𝟙 X) f =
      eqToIso (congrArg (fun k : X ⟶ Y ↦
        Scheme.proEtaleSheafInverseImage k (Type (u + 1))) (Category.id_comp f)) ≪≫
      (Scheme.proEtaleSheafInverseImage f (Type (u + 1))).rightUnitor.symm ≪≫
      Functor.isoWhiskerLeft (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
        (profinitePointSetIdentity X).symm := by
  refine (conjugateIsoEquiv ((Scheme.proEtaleSheafAdjunction f (Type (u + 1))).comp
    (Scheme.proEtaleSheafAdjunction (𝟙 X) (Type (u + 1))))
    (Scheme.proEtaleSheafAdjunction (𝟙 X ≫ f) (Type (u + 1)))).injective ?_
  rw [conjugateIsoEquiv_trans _ (Scheme.proEtaleSheafAdjunction f (Type (u + 1))) _,
    conjugateIsoEquiv_trans _ ((Scheme.proEtaleSheafAdjunction f (Type (u + 1))).comp
      Adjunction.id) _]
  rw [conjugateSetComp, conjugateSetCongr (Category.id_comp f),
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_iso_symm, conjugateSetId,
    conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_rightUnitor, legacy_lowerStarComp_id_left]
  refine Iso.ext (NatTrans.ext (funext fun M ↦ ?_))
  simp

private lemma normalizedSetPointComparison_comp
    {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (kX : X ⟶ W) (kY : Y ⟶ W) (kZ : Z ⟶ W)
    (hX : f ≫ kY = kX) (hY : g ≫ kZ = kY) (hfg : (f ≫ g) ≫ kZ = kX)
    (M : Sheaf (Scheme.ProEt.topology W) (Type (u + 1))) :
    (profinitePointSetComp f g).hom.app
        ((Scheme.proEtaleSheafInverseImage kZ (Type (u + 1))).obj M) ≫
      (Scheme.proEtaleSheafInverseImage f (Type (u + 1))).map
        ((profinitePointSetComp g kZ).inv.app M ≫
          (eqToHom (congrArg (fun k : Y ⟶ W ↦
            Scheme.proEtaleSheafInverseImage k (Type (u + 1))) hY)).app M) ≫
      ((profinitePointSetComp f kY).inv.app M ≫
        (eqToHom (congrArg (fun k : X ⟶ W ↦
          Scheme.proEtaleSheafInverseImage k (Type (u + 1))) hX)).app M) =
    (profinitePointSetComp (f ≫ g) kZ).inv.app M ≫
      (eqToHom (congrArg (fun k : X ⟶ W ↦
        Scheme.proEtaleSheafInverseImage k (Type (u + 1))) hfg)).app M := by
  subst hY
  subst hX
  have h := congrArg (fun e ↦ e.inv.app M) (setComp_assoc f g kZ)
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Category.id_comp, eqToIso.inv] at h
  simp only [eqToHom_refl, NatTrans.id_app, Category.comp_id]
  rw [h]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rfl

private lemma setPointComparison_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g)
    (F : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))) :
    (eqToHom (congrArg (fun k : X ⟶ Y ↦
      Scheme.proEtaleSheafInverseImage k (Type (u + 1))) w)).app
        ((profinitePointSetSchemeInverseImage Y).obj F) ≫
        (profinitePointSetSchemeComp g).hom.app F =
      (profinitePointSetSchemeComp f).hom.app F := by
  subst w
  simp
private lemma setPointSchemeComp_hom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (profinitePointSetSchemeComp f).hom =
      (Functor.associator profinitePointSetInverseImage
        (Scheme.proEtaleSheafInverseImage (toSpecZ Y) (Type (u + 1)))
        (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))).hom ≫
      Functor.whiskerLeft profinitePointSetInverseImage
        ((profinitePointSetComp f (toSpecZ Y)).inv ≫
          eqToHom (congrArg
            (fun k : X ⟶ specZ ↦ Scheme.proEtaleSheafInverseImage k (Type (u + 1)))
            (comp_toSpecZ f))) := by
  simp only [profinitePointSetSchemeComp, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom, eqToIso.hom]

private lemma setPointSchemeComp_hom_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))) :
    (profinitePointSetSchemeComp f).hom.app F =
      (profinitePointSetComp f (toSpecZ Y)).inv.app (profinitePointSetInverseImage.obj F) ≫
        (eqToHom (congrArg (fun k : X ⟶ specZ ↦
          Scheme.proEtaleSheafInverseImage k (Type (u + 1))) (comp_toSpecZ f))).app
          (profinitePointSetInverseImage.obj F) := by
  have hh := congrArg (fun η ↦ η.app F) (setPointSchemeComp_hom f)
  simpa only [NatTrans.comp_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp] using hh

/-- The geometric point comparisons are coherent already on sets.
Source: RefactorInstruction, prop:pX and Section 5, eq:triangle
(auxiliary; not a blueprint node).

Proof: (2) The scheme base-change functors preserve finite limits and coverings, so their
inverse images and their composite with the point inverse image preserve finite limits.
(3) Conjugate the fibre-product identity and composition comparisons. Their diagrams
commute by uniqueness of maps preserving the projections; uniqueness of the conjugate
comparison carries these diagrams to inverse images. (4) Whisker with the point inverse
image and use the structure-map identity. (8) Both routes around a commutative square
therefore give the comparison for its common composite. -/
theorem profinite_point_pullback_set_coherence :
    (∀ X : Scheme.{u}, PreservesFiniteLimits (profinitePointSetSchemeInverseImage X)) ∧
    (∀ (X : Scheme.{u}) (F : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))),
      (profinitePointSetSchemeComp (𝟙 X)).hom.app F =
        (profinitePointSetIdentity X).hom.app ((profinitePointSetSchemeInverseImage X).obj F)) ∧
    (∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
      (F : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))),
      (profinitePointSetComp f g).hom.app ((profinitePointSetSchemeInverseImage Z).obj F) ≫
          (Scheme.proEtaleSheafInverseImage f (Type (u + 1))).map
            ((profinitePointSetSchemeComp g).hom.app F) ≫
          (profinitePointSetSchemeComp f).hom.app F =
        (profinitePointSetSchemeComp (f ≫ g)).hom.app F) ∧
    (∀ (X' X Y' Y : Scheme.{u}) (b : X' ⟶ X) (f : X ⟶ Y)
      (f' : X' ⟶ Y') (g : Y' ⟶ Y) (w : b ≫ f = f' ≫ g)
      (F : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))),
      (profinitePointSetComp b f).inv.app ((profinitePointSetSchemeInverseImage Y).obj F) ≫
          (eqToHom (congrArg
            (fun k : X' ⟶ Y ↦ Scheme.proEtaleSheafInverseImage k (Type (u + 1))) w)).app
              ((profinitePointSetSchemeInverseImage Y).obj F) ≫
          (profinitePointSetComp f' g).hom.app ((profinitePointSetSchemeInverseImage Y).obj F) ≫
          (Scheme.proEtaleSheafInverseImage f' (Type (u + 1))).map
            ((profinitePointSetSchemeComp g).hom.app F) ≫
          (profinitePointSetSchemeComp f').hom.app F =
        (Scheme.proEtaleSheafInverseImage b (Type (u + 1))).map
            ((profinitePointSetSchemeComp f).hom.app F) ≫
          (profinitePointSetSchemeComp b).hom.app F) := by
  have hcomp : ∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
      (F : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))),
      (profinitePointSetComp f g).hom.app ((profinitePointSetSchemeInverseImage Z).obj F) ≫
        (Scheme.proEtaleSheafInverseImage f (Type (u + 1))).map
          ((profinitePointSetSchemeComp g).hom.app F) ≫
        (profinitePointSetSchemeComp f).hom.app F =
      (profinitePointSetSchemeComp (f ≫ g)).hom.app F := by
    intro X Y Z f g F
    rw [setPointSchemeComp_hom_app, setPointSchemeComp_hom_app,
      setPointSchemeComp_hom_app]
    exact normalizedSetPointComparison_comp f g (toSpecZ X) (toSpecZ Y) (toSpecZ Z)
      (comp_toSpecZ f) (comp_toSpecZ g) (comp_toSpecZ (f ≫ g))
      (profinitePointSetInverseImage.obj F)
  refine ⟨?_, ?_, hcomp, ?_⟩
  · intro X
    let : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
      AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} _
    have : PreservesFiniteLimits profinitePointSetInverseImage.{u} :=
      profinite_point_pullback.2.2.2.2.2.2.1
    let : AB5OfSize.{u + 1, u + 1} (Type (u + 1)) := inferInstance
    let : RepresentablyFlat (Scheme.proEtaleBaseChange (toSpecZ X)) :=
      flat_of_preservesFiniteLimits _
    have : PreservesFiniteLimits
        (Scheme.proEtaleSheafInverseImage (toSpecZ X) (Type (u + 1))) := by
      unfold Scheme.proEtaleSheafInverseImage Functor.sheafPullbackConstruction.sheafPullback
      have : PreservesFiniteLimits
          ((Scheme.proEtaleBaseChange (toSpecZ X)).op.lan :
            ((Scheme.ProEt specZ)ᵒᵖ ⥤ Type (u + 1)) ⥤
              (Scheme.ProEt X)ᵒᵖ ⥤ Type (u + 1)) := by
        apply CategoryTheory.preservesFiniteLimits_op_lan_of_flat
      infer_instance
    exact comp_preservesFiniteLimits _ _
  · intro X F
    simp [profinitePointSetSchemeComp, setComp_id_left]
  · intro X' X Y' Y b f f' g w F
    rw [hcomp X' Y' Y f' g F, setPointComparison_congr w F]
    rw [← cancel_epi ((profinitePointSetComp b f).hom.app
      ((profinitePointSetSchemeInverseImage Y).obj F))]
    simpa [Category.assoc] using (hcomp X' X Y b f F).symm

end AlgebraicGeometry.ProEtale
