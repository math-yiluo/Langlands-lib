/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocalDirectImageStalkClassMap
import Mathlib.Topology.Sheaves.Sheafify
import WeilConjectures.AlgebraicGeometry.LocalDirectImageStalkClassLinear

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

private theorem germ_bijective_of_nhds_top {T : TopCat.{u}}
    (P : T.Presheaf AddCommGrpCat.{u}) (z : T)
    (htop : ∀ (V : TopologicalSpace.Opens T), z ∈ V → V = ⊤) :
    Function.Bijective (P.germ ⊤ z (by trivial)) := by
  constructor
  · intro a b hab
    obtain ⟨V, hzV, ia, ib, he⟩ := P.germ_eq z (by trivial) (by trivial) a b hab
    obtain rfl := htop V hzV
    have hia : ia = 𝟙 _ := Subsingleton.elim _ _
    have hib : ib = 𝟙 _ := Subsingleton.elim _ _
    simpa [hia, hib] using he
  · intro a
    obtain ⟨V, hzV, b, hb⟩ := P.exists_germ_eq a
    obtain rfl := htop V hzV
    exact ⟨b, hb⟩

private theorem local_germ_bijective (A : CommRingCat.{u}) [IsLocalRing A]
    (P : (Spec A).toRingedSpace.carrier.Presheaf AddCommGrpCat.{u}) :
    Function.Bijective (P.germ ⊤ (IsLocalRing.closedPoint A) (by trivial)) := by
  apply germ_bijective_of_nhds_top
  intro V hV
  exact IsLocalRing.closed_point_mem_iff.mp hV

private theorem local_section_comparison_isIso (A : CommRingCat.{u}) [IsLocalRing A]
    (K : CochainComplex (Spec A).Modules ℕ) (p : ℕ) :
    IsIso (((PresheafOfModules.toPresheaf (Spec A).ringCatSheaf.obj).map
      (Scheme.Modules.sectionCohomologyTheta K p)).app (op ⊤)) := by
  let z : Spec A := IsLocalRing.closedPoint A
  let P := Scheme.Modules.sectionCohomologyPresheaf K p
  let Q := (SheafOfModules.forget (Spec A).ringCatSheaf).obj (K.homology p)
  let t := (PresheafOfModules.toPresheaf (Spec A).ringCatSheaf.obj).map
    (Scheme.Modules.sectionCohomologyTheta K p)
  have hc : IsIso (Scheme.Modules.sectionCohomologyComparison K p) := by
    have hi : IsIso (((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Spec A).ringCatSheaf.obj)).counit.mapHomologicalComplex
          (ComplexShape.up ℕ)).app K) := by
      have hcomp : ∀ n : ℕ, IsIso ((((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Spec A).ringCatSheaf.obj)).counit.mapHomologicalComplex
            (ComplexShape.up ℕ)).app K).f n) := fun n ↦ by
        change IsIso ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Spec A).ringCatSheaf.obj)).counit.app (K.X n))
        infer_instance
      exact HomologicalComplex.Hom.isIso_of_components _
    have hm := (HomologicalComplex.homologyFunctor (Spec A).Modules
      (ComplexShape.up ℕ) p).map_isIso
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Spec A).ringCatSheaf.obj)).counit.mapHomologicalComplex
            (ComplexShape.up ℕ)).app K)
    unfold Scheme.Modules.sectionCohomologyComparison
    exact IsIso.comp_isIso
  have hs : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map t) := by
    dsimp only [t, Scheme.Modules.sectionCohomologyTheta]
    rw [PresheafOfModules.sheafificationAdjunction_homEquiv_apply,
      PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def, Functor.map_comp]
    have hu := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso z
      AddCommGrpCat.{u} P.presheaf
    have hv : IsIso ((PresheafOfModules.toPresheaf (Spec A).ringCatSheaf.obj).map
        (Scheme.Modules.sectionCohomologyComparison K p).val) :=
      (SheafOfModules.forget (Spec A).ringCatSheaf ⋙
        PresheafOfModules.toPresheaf (Spec A).ringCatSheaf.obj).map_isIso
          (Scheme.Modules.sectionCohomologyComparison K p)
    exact IsIso.comp_isIso
  have ht : Function.Bijective (t.app (op ⊤)) := by
    have hg (a : P.presheaf.obj (op ⊤)) :
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map t)
          (TopCat.Presheaf.germ P.presheaf ⊤ z (by trivial) a) =
        TopCat.Presheaf.germ Q.presheaf ⊤ z (by trivial) (t.app (op ⊤) a) :=
      TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ z (by trivial) t a
    have hb := ConcreteCategory.bijective_of_isIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map t)
    have hP := local_germ_bijective A P.presheaf
    have hQ := local_germ_bijective A Q.presheaf
    constructor
    · intro a b hab
      apply hP.1
      apply hb.1
      rw [hg, hg, hab]
    · intro b
      obtain ⟨a, ha⟩ := hb.2 (TopCat.Presheaf.germ Q.presheaf ⊤ z (by trivial) b)
      obtain ⟨c, hc⟩ := hP.2 a
      refine ⟨c, hQ.1 ?_⟩
      rw [← hg, hc, ha]
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ht

private theorem local_pushforward_germ_bijective (Y : Scheme.{u}) (y : Y)
    (N : (Spec (Y.presheaf.stalk y)).Modules) :
    Function.Bijective (TopCat.Presheaf.germ
      ((Scheme.Modules.pushforward (Y.fromSpecStalk y)).obj N).presheaf
        ⊤ y (by trivial)) := by
  let c := Y.fromSpecStalk y
  let P := (Scheme.Modules.pushforward c).obj N
  have hres (V : Y.Opens) (hy : y ∈ V) (i : V ⟶ ⊤) :
      IsIso (P.presheaf.map i.op) := by
    change IsIso (N.presheaf.map ((TopologicalSpace.Opens.map c.base).map i).op)
    have he : c ⁻¹ᵁ V = c ⁻¹ᵁ ⊤ := by
      have hV : c ⁻¹ᵁ V = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem c
        (by simpa only [c, Scheme.fromSpecStalk_closedPoint] using hy)
      exact hV.trans (TopologicalSpace.Opens.map_top c.base).symm
    have hi : (TopologicalSpace.Opens.map c.base).map i = (eqToIso he).hom :=
      Subsingleton.elim _ _
    rw [hi]
    infer_instance
  constructor
  · intro a b hab
    obtain ⟨V, hy, ia, ib, he⟩ :=
      TopCat.Presheaf.germ_eq P.presheaf y (by trivial) (by trivial) a b hab
    have : IsIso (P.presheaf.map ia.op) := hres V hy ia
    apply (ConcreteCategory.bijective_of_isIso (P.presheaf.map ia.op)).1
    simpa only [Subsingleton.elim ib ia] using he
  · intro a
    obtain ⟨V, hy, b, hb⟩ := TopCat.Presheaf.exists_germ_eq P.presheaf a
    let i : V ⟶ ⊤ := homOfLE le_top
    have : IsIso (P.presheaf.map i.op) := hres V hy i
    obtain ⟨s, hs⟩ := (ConcreteCategory.bijective_of_isIso (P.presheaf.map i.op)).2 b
    refine ⟨s, ?_⟩
    rw [← TopCat.Presheaf.germ_res_apply P.presheaf i y hy s, hs, hb]

private theorem local_resolution_class_bijective {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (F : X.Modules) (p : ℕ) :
    Function.Bijective (localDirectImage_stalk_class f y F p) := by
  let F' := (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F
  let K := injectiveResolution F'
  let f' := pullback.fst (Y.fromSpecStalk y) f
  let L := ((Scheme.Modules.pushforward f').mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K.cocomplex
  have htheta := local_section_comparison_isIso
    (CommRingCat.of (Y.presheaf.stalk y)) L p
  have hr : IsIso (Scheme.Modules.resolutionSectionClass K L ⊤ (Iso.refl _) p) := by
    dsimp only [Scheme.Modules.resolutionSectionClass]
    infer_instance
  have hd : IsIso (Scheme.Modules.Hom.app
      (K.isoRightDerivedObj (Scheme.Modules.pushforward f') p).inv ⊤) := by
    change IsIso ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _ ⋙
      (CategoryTheory.evaluation _ AddCommGrpCat.{u}).obj (op ⊤)).map
        (K.isoRightDerivedObj (Scheme.Modules.pushforward f') p).inv)
    infer_instance
  change Function.Bijective (ConcreteCategory.hom
    (Scheme.Modules.resolutionSectionClass K L ⊤ (Iso.refl _) p ≫
      Scheme.Modules.Hom.app
        (K.isoRightDerivedObj (Scheme.Modules.pushforward f') p).inv ⊤ ≫ _))
  have hfirst := ConcreteCategory.bijective_of_isIso
    (Scheme.Modules.resolutionSectionClass K L ⊤ (Iso.refl _) p)
  have hsecond := ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app
    (K.isoRightDerivedObj (Scheme.Modules.pushforward f') p).inv ⊤)
  have hthird := local_pushforward_germ_bijective Y y
    (((Scheme.Modules.pushforward f').rightDerived p).obj F')
  exact hthird.comp (hsecond.comp hfirst)

/-- The canonical class map is an A-linear equivalence.
Source: Stacks Project, Tag 02OD, the local-stalk/global-cohomology identification;
Tag 01E4, the cocycle-to-cohomology-sheaf comparison.
(blueprint: lem-weil-pbc-local-direct-image-stalk-cohomology-equiv)

Proof: Set A = O_{Y,y}, c : Spec A → Y, f' : X' → Spec A, F' = g'^*F.
For every neighborhood V of y, c^{-1}V is top. Thus taking the germ identifies
Gamma(Spec A,N) with (c_*N)_y. Every open of Spec A containing its closed point
is top, so Gamma(Spec A,-) is closed-point stalk evaluation and is exact.
Apply this evaluation to f'_*K for the specified injective resolution K of F'.
It commutes with homology. The sectionCohomologyTheta map on top is precisely
this homology comparison: sheafification induces an isomorphism at the closed
point, and the counit on the already sheaf-valued complex is an isomorphism.
The termwise identity Gamma(Spec A,f'_*K) = Gamma(X',K), together with the
right-derived resolution comparisons in localDirectImage_stalk_class, proves
that this particular additive map is bijective. To check A-linearity, represent
a scalar by a structure-sheaf germ on V; its action on the class map is the action
on Gamma(X',K) via Gamma-Spec followed by f'.appTop, because c^{-1}V is top and
the structure-sheaf germ square commutes. All resolution and homology maps are
linear for that action. Equip this same bijective map with its linear structure.
The equation in the conclusion determines e pointwise, hence uniquely. -/
theorem localDirectImage_stalk_cohomology_equiv {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (F : X.Modules) (p : ℕ) :
    ∃ e : (RingedSpace.moduleCohomology (pullback (Y.fromSpecStalk y) f).toRingedSpace p ⋙
        ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫
            (pullback.fst (Y.fromSpecStalk y) f).appTop).hom).obj
        ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)
      ≃ₗ[Y.presheaf.stalk y]
      (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
      ((Scheme.Modules.pushforward (Y.fromSpecStalk y)).obj
        (((Scheme.Modules.pushforward (pullback.fst (Y.fromSpecStalk y) f)).rightDerived
          p).obj
          ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))),
      ∀ x, e x = localDirectImage_stalk_class f y F p x := by
  let b := localDirectImage_stalk_class f y F p
  let l : (RingedSpace.moduleCohomology (pullback (Y.fromSpecStalk y) f).toRingedSpace p ⋙
      ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫
          (pullback.fst (Y.fromSpecStalk y) f).appTop).hom).obj
      ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)
      →ₗ[Y.presheaf.stalk y]
      (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
        ((Scheme.Modules.pushforward (Y.fromSpecStalk y)).obj
          (((Scheme.Modules.pushforward (pullback.fst (Y.fromSpecStalk y) f)).rightDerived
            p).obj
            ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))) :=
    { toAddHom := b
      map_smul' := fun r x ↦ localDirectImage_stalk_class_smul f y F p r x }
  exact ⟨LinearEquiv.ofBijective l (local_resolution_class_bijective f y F p), fun _ ↦ rfl⟩

end AlgebraicGeometry
