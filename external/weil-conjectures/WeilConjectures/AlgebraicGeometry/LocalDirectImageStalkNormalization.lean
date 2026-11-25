/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocalDirectImageStalkClassMap
public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.LocalDirectImageStalkClassRestriction
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Local direct-image stalks and total cohomology

Source: Stacks Project, Tags 02OD and 01E4.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
attribute [local instance] Scheme.Modules.enoughInjectives

private theorem fmap_iso {X Y : Scheme.{u}} (h : X ⟶ Y)
    [(Scheme.Modules.pushforward h).PreservesHomology] {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (Scheme.Modules.pushforward h).obj F) [IsIso φ] (p : ℕ) :
    IsIso (Scheme.Modules.moduleCohomologyFMap h φ p) := by
  let D := Classical.choice (Scheme.Modules.moduleCohomologyFMapData_nonempty h G F φ)
  let P := Scheme.Modules.pushforward h
  let PC := P.mapHomologicalComplex (ComplexShape.up ℕ)
  let a := (HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℕ) 0).inv.app F
  have ha : IsIso a := by dsimp [a]; infer_instance
  have hl : QuasiIso D.lambda := D.quasiIso
  have he : D.J.ι ≫ D.β = (CochainComplex.single₀ Y.Modules).map φ ≫
      a ≫ PC.map D.I.ι ≫ D.lambda := by
    apply (CochainComplex.fromSingle₀Equiv _ _).injective
    apply Subtype.ext
    simpa [a, P, PC] using D.compatible
  have hb : QuasiIso D.β := by
    have : QuasiIso (D.J.ι ≫ D.β) := by rw [he]; infer_instance
    exact quasiIso_of_comp_left D.J.ι D.β
  let : ∀ n, Injective (D.K.X n) := D.injective
  obtain ⟨e, he⟩ := (CochainComplex.quasiIso_iff_of_injective D.β).1 hb
  let Γ := RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙ forget₂ _ AddCommGrpCat.{u}
  have hi : IsIso ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
      (ComplexShape.up ℕ) p).map ((Γ.mapHomologicalComplex _).map D.β)) := by
    rw [← he]
    exact ((Γ.mapHomotopyEquiv e).toHomologyIso p).isIso_hom
  change IsIso (D.map p)
  have := D.invertible p
  unfold Scheme.Modules.ModuleCohomologyFMapData.map
  infer_instance
private theorem pushforward_equiv {X Y : Scheme.{u}} (h : X ⟶ Y) [IsIso h] :
    (Scheme.Modules.pushforward h).IsEquivalence := by
  let e : X.Modules ≌ Y.Modules :=
    CategoryTheory.Equivalence.mk (Scheme.Modules.pushforward h)
      (Scheme.Modules.pushforward (inv h))
    ((Scheme.Modules.pushforwardId X).symm ≪≫
      (Scheme.Modules.pushforwardCongr (IsIso.hom_inv_id h)).symm ≪≫
      (Scheme.Modules.pushforwardComp h (inv h)).symm)
    (Scheme.Modules.pushforwardComp (inv h) h ≪≫
      Scheme.Modules.pushforwardCongr (IsIso.inv_hom_id h) ≪≫ Scheme.Modules.pushforwardId Y)
  exact e.isEquivalence_functor

private theorem restriction_iso {Y : Scheme.{u}} (U : Y.Opens) (hU : U = ⊤)
    (G : Y.Modules) (p : ℕ) :
    IsIso (Scheme.Modules.moduleCohomologyRestriction U G p) := by
  subst U
  have : IsIso (⊤ : Y.Opens).ι := Y.topIso.isIso_hom
  have := pushforward_equiv (⊤ : Y.Opens).ι
  have : (Scheme.Modules.pushforward (⊤ : Y.Opens).ι).PreservesHomology := inferInstance
  have : IsIso ((Scheme.Modules.restrictAdjunction (⊤ : Y.Opens).ι).unit.app G) := by
    infer_instance
  exact fmap_iso _ _ p


/-- Normalization of the inverse of the specified canonical class map.
Source: Stacks Project, Tags 01E4 and 01FB; Tag 02OD for the local spectrum.
(blueprint: lem-weil-pbc-local-direct-image-stalk-cohomology-normalization)

Proof: For V containing y, c^{-1}V is top. The pullback-square identity therefore
identifies W = g'^{-1}(f^{-1}V) with all of X'. Restriction from X' to W is thus
an isomorphism on module cohomology. Let eta be the unique global class restricting
to xi. Compute its image under localDirectImage_stalk_class using the fixed
injective resolution. Compute germ(D.targetClass p xi) using the supplied K
and the restricted resolution D.target.resolution. The component identity of
D.target.sections identifies the latter section-complex map with restriction
of K; its augmentation identity identifies its degree-zero map with the
restriction unit. Comparing the fixed resolution with K gives augmented
comparison maps, unique up to homotopy. Their maps on homology agree. Naturality
of evaluation, sectionCohomologyTheta, and isoRightDerivedObj then gives
localDirectImage_stalk_class eta = germ(D.targetClass p xi). The hypothesis
he identifies e with this class map. Applying e.symm yields eta, and restricting
eta to W yields xi, as required. This uses only D.target, and works for every
supplied I, K, V and D. It includes p = 0 and zero cohomology modules. -/
theorem localDirectImage_stalk_cohomology_normalization
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (F : X.Modules) (p : ℕ)
    (e : (RingedSpace.moduleCohomology (pullback (Y.fromSpecStalk y) f).toRingedSpace p ⋙
        ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫
            (pullback.fst (Y.fromSpecStalk y) f).appTop).hom).obj
        ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)
      ≃ₗ[Y.presheaf.stalk y]
      (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
      ((Scheme.Modules.pushforward (Y.fromSpecStalk y)).obj
        (((Scheme.Modules.pushforward (pullback.fst (Y.fromSpecStalk y) f)).rightDerived
          p).obj
          ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))))
    (he : ∀ x, e x = localDirectImage_stalk_class f y F p x) :
      ∀ (I : InjectiveResolution F)
        (K : InjectiveResolution
          ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))
        (V : Y.Opens) (hy : y ∈ V)
        (D : Scheme.Modules.FlatBaseChangeOpenChoices f (Y.fromSpecStalk y) F I K V)
        (xi : (forget₂ _ AddCommGrpCat.{u}).obj
          ((RingedSpace.moduleCohomology
            ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme.toRingedSpace p).obj
            ((Scheme.Modules.restrictFunctor
              ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).obj
              ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)))),
        Scheme.Modules.moduleCohomologyFMap
          ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι
          ((Scheme.Modules.restrictAdjunction
            ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).unit.app
              ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)) p
          (e.symm.toLinearMap (TopCat.Presheaf.germ
            ((Scheme.Modules.pushforward (Y.fromSpecStalk y)).obj
              (((Scheme.Modules.pushforward (pullback.fst (Y.fromSpecStalk y) f)).rightDerived
                p).obj
                ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj
                  F))).presheaf V y hy (D.targetClass p xi))) = xi := by
  intro I K V hy D
  have hc : (Y.fromSpecStalk y) ⁻¹ᵁ V = ⊤ := by
    apply top_unique
    intro q _
    have hs : (Y.fromSpecStalk y) q ⤳ y := by
      have h := Set.mem_range_self (f := Y.fromSpecStalk y) q
      rw [Scheme.range_fromSpecStalk] at h
      exact h
    exact hs.mem_open V.isOpen hy
  have hW : (pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V) = ⊤ := by
    rw [Scheme.Modules.flatBaseChangeOpenEquality, hc]
    simp
  have hi := restriction_iso _ hW
    ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F) p
  let r := Scheme.Modules.moduleCohomologyFMap
    ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι
    ((Scheme.Modules.restrictAdjunction
      ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).unit.app
        ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)) p
  have : IsIso r := hi
  have hr : Function.Surjective r := (ConcreteCategory.bijective_of_isIso r).2
  refine hr.forall.mpr ?_
  intro eta
  have hclass := localDirectImage_stalk_class_restriction f y F p I K V hy D eta
  have heclass := (he eta).trans hclass
  have hs := congrArg e.symm.toLinearMap heclass
  have hs' := (e.symm_apply_apply eta).symm.trans hs
  exact congrArg r hs'.symm

end AlgebraicGeometry
