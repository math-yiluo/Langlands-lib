/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
import all WeilConjectures.AlgebraicGeometry.Geometric.GeometricOrdinaryRealization
import all WeilConjectures.AlgebraicGeometry.Geometric.GeometricOperationsBaseExistence
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOperationsTransitionExistence
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictBaseCoordinates
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFiniteSectionInverseImages

/-! # Geometry with the actual direct-image section coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u c v r
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
attribute [local irreducible] SemilinearSections.systemRing
  SemilinearSections.ringPresheaf SemilinearSections.rings
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
  AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction
  AlgebraicGeometry.Scheme.proEtaleRingDirectImageMap
  AlgebraicGeometry.Scheme.proEtaleConstantRingComparison
  CategoryTheory.constantSheaf Padic Padic.coefficientExtensionIntegers

namespace AlgebraicGeometry.ProEtale.SpTowerClasses
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

open SemilinearSections

private theorem restriction_unit_general
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{max c v r} C]
    (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n, B (n + 1) ⟶ B n)
    {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
    (J' : GrothendieckTopology C')
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adjSet : uInv ⊣ uPush)
    (F : ℕ → Sheaf J' CommRingCat.{max c v r}) (σ : ∀ n, F (n + 1) ⟶ F n)
    (I : ∀ n, SheafOfModules.AlgebraicInverseImage uInv (B n) (F n))
    (P : OrdinaryInverseSystem.{c, v, r} J B τ J' uInv F σ I)
    (V : ∀ n, SemilinearSections.Mod.{c, v, max c v r} J' (F n) ⥤
      SemilinearSections.Mod.{c, v, max c v r} J (B n))
    (a : ∀ n, (I n).modules ⊣ V n)
    (eV : ∀ n, V n ⋙ SemilinearSections.underlying.{c, v, r} J (B n) ≅
      SemilinearSections.underlying.{c, v, r} J' (F n) ⋙ uPush)
    (ha : ∀ n (M : SemilinearSections.Mod.{c, v, max c v r} J (B n))
      (N : SemilinearSections.Mod.{c, v, max c v r} J' (F n)) (k : (I n).modules.obj M ⟶ N),
      (SemilinearSections.underlying.{c, v, r} J (B n)).map ((a n).homEquiv M N k) ≫
          (eV n).hom.app N = adjSet.homEquiv _ _
        ((I n).moduleUnderlying.inv.app M ≫ (SemilinearSections.underlying.{c, v, r} J' (F n)).map
          k))
    {m n : ℕ} (h : n ≤ m) (M : SemilinearSections.Mod.{c, v, max c v r} J (B m))
    (N : SemilinearSections.Mod.{c, v, max c v r} J (B n))
    (t : M ⟶ (SemilinearSections.res.{c, v, max c v r} (SemilinearSections.coefficientMap.{c, v, max
      c v r} J B τ h)).obj N) :
    (SemilinearSections.underlying.{c, v, r} J (B m)).map ((a m).homEquiv _ _
        ((I m).modules.map t ≫ (P.restriction h).hom.app N)) ≫
      (eV m).hom.app ((SemilinearSections.res.{c, v, max c v r}
        (SemilinearSections.coefficientMap.{c, v, max c v r} J' F σ h)).obj ((I n).modules.obj N)) =
    (SemilinearSections.underlying.{c, v, r} J (B m)).map t ≫
      (SemilinearSections.underlying.{c, v, r} J (B n)).map ((a n).unit.app N) ≫
        (eV n).hom.app ((I n).modules.obj N) := by
  have hr : (I m).moduleUnderlying.inv.app
        ((SemilinearSections.res.{c, v, max c v r} (SemilinearSections.coefficientMap.{c, v, max c v
          r} J B τ h)).obj N) ≫
      (SemilinearSections.underlying.{c, v, r} J' (F m)).map ((P.restriction h).hom.app N) =
        (I n).moduleUnderlying.inv.app N := by
    apply (cancel_mono ((I n).moduleUnderlying.hom.app N)).1
    simp only [Category.assoc, P.restriction_underlying,
      Iso.inv_hom_id_app]
    rfl
  have ht : (I m).moduleUnderlying.inv.app M ≫
      (SemilinearSections.underlying.{c, v, r} J' (F m)).map
        ((I m).modules.map t ≫ (P.restriction h).hom.app N) =
      uInv.map ((SemilinearSections.underlying.{c, v, r} J (B m)).map t) ≫
        (I n).moduleUnderlying.inv.app N := by
    have hn := (I m).moduleUnderlying.inv.naturality t
    dsimp only [Functor.comp_map] at hn
    have hmap := congrArg (fun k ↦ (I m).moduleUnderlying.inv.app M ≫ k)
      ((SemilinearSections.underlying.{c, v, r} J' (F m)).map_comp
        ((I m).modules.map t) ((P.restriction h).hom.app N))
    exact hmap.trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun k ↦ k ≫ (SemilinearSections.underlying.{c, v, r} J' (F m)).map
        ((P.restriction h).hom.app N)) hn.symm).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun k ↦ uInv.map
              ((SemilinearSections.underlying.{c, v, r} J (B m)).map t) ≫ k) hr))))
  have hn := ha n N ((I n).modules.obj N) (𝟙 _)
  simp only [Adjunction.homEquiv_id] at hn
  have hh := ha m M
    ((SemilinearSections.res.{c, v, max c v r}
      (SemilinearSections.coefficientMap.{c, v, max c v r} J' F σ h)).obj
        ((I n).modules.obj N))
    ((I m).modules.map t ≫ (P.restriction h).hom.app N)
  have htp := congrArg (fun k ↦ (adjSet.homEquiv _ _) k) ht
  have hnat := adjSet.homEquiv_naturality_left
    ((SemilinearSections.underlying.{c, v, r} J (B m)).map t)
    ((I n).moduleUnderlying.inv.app N)
  exact hh.trans (htp.trans (hnat.trans
    (congrArg (fun k ↦ (SemilinearSections.underlying.{c, v, r} J (B m)).map t ≫ k)
      hn.symm)))

private theorem unit_point
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{max c v r} C]
    (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n, B (n + 1) ⟶ B n)
    {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
    (J' : GrothendieckTopology C')
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adjSet : uInv ⊣ uPush)
    (F : ℕ → Sheaf J' CommRingCat.{max c v r}) (σ : ∀ n, F (n + 1) ⟶ F n)
    (I : ∀ n, SheafOfModules.AlgebraicInverseImage uInv (B n) (F n))
    (P : OrdinaryInverseSystem.{c, v, r} J B τ J' uInv F σ I)
    (V : ∀ n, SemilinearSections.Mod.{c, v, max c v r} J' (F n) ⥤
      SemilinearSections.Mod.{c, v, max c v r} J (B n))
    (a : ∀ n, (I n).modules ⊣ V n)
    (eV : ∀ n, V n ⋙ SemilinearSections.underlying.{c, v, r} J (B n) ≅
      SemilinearSections.underlying.{c, v, r} J' (F n) ⋙ uPush)
    (ha' : ∀ n (M : SemilinearSections.Mod.{c, v, max c v r} J (B n))
      (N : SemilinearSections.Mod.{c, v, max c v r} J' (F n)) (k : (I n).modules.obj M ⟶ N),
      (SemilinearSections.underlying.{c, v, r} J (B n)).map ((a n).homEquiv M N k) ≫
          (eV n).hom.app N = adjSet.homEquiv _ _
        ((I n).moduleUnderlying.inv.app M ≫ (SemilinearSections.underlying.{c, v, r} J' (F n)).map
          k))
    (hV : ∀ n (N : SemilinearSections.Mod.{c, v, max c v r} J' (F n)) (U : Cᵒᵖ)
      (x : ((V n).obj N).val.obj U),
      HEq (((eV n).hom.app N).hom.app U x) x) :
    ∀ (M : SemilinearSections.Systems.{c, v, max c v r} J B τ) {m n : ℕ} (h : n ≤ m)
      (U : Cᵒᵖ)
      (x : ((SemilinearSections.evaluation.{c, v, max c v r} J B τ m).obj M).val.obj U)
      (y : ((SemilinearSections.evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U),
      HEq (((SemilinearSections.transition.{c, v, max c v r} J B τ h).app M).val.app U x) y →
      HEq ((((a m).homEquiv _ _)
        ((P.component m).inv.app M ≫
          (SemilinearSections.transition.{c, v, max c v r} J' F σ h).app (P.pull.obj M) ≫
          (SemilinearSections.res.{c, v, max c v r}
            (SemilinearSections.coefficientMap.{c, v, max c v r} J' F σ h)).map
              ((P.component n).hom.app M))).val.app U x)
        (((a n).unit.app
          ((SemilinearSections.evaluation.{c, v, max c v r} J B τ n).obj M)).val.app U y) := by
  intro M m n h U x y hy
  have hk : (P.component m).inv.app M ≫
      (SemilinearSections.transition.{c, v, max c v r} J' F σ h).app (P.pull.obj M) ≫
        (SemilinearSections.res.{c, v, max c v r}
          (SemilinearSections.coefficientMap.{c, v, max c v r} J' F σ h)).map
            ((P.component n).hom.app M) =
      (I m).modules.map ((SemilinearSections.transition.{c, v, max c v r} J B τ h).app M) ≫
        (P.restriction h).hom.app ((SemilinearSections.evaluation.{c, v, max c v r} J B τ n).obj
          M) := by
    have ht := congrArg (fun k ↦ (P.component m).inv.app M ≫ k)
      (P.transition h M)
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using ht
  have ht := restriction_unit_general.{c, v, r}
    J B τ J' uInv uPush adjSet F σ I P V a eV ha' h
      ((SemilinearSections.evaluation.{c, v, max c v r} J B τ m).obj M)
    ((SemilinearSections.evaluation.{c, v, max c v r} J B τ n).obj M)
      ((SemilinearSections.transition.{c, v, max c v r} J B τ h).app M)
  have hp := congrArg (fun k ↦ k.hom.app U x) ht
  have hs := congrArg
    (fun k ↦ (((a m).homEquiv _ _) k).val.app U x) hk
  have hl := hV m _ U
    ((((a m).homEquiv _ _)
      ((I m).modules.map ((SemilinearSections.transition J B τ h).app M) ≫
        (P.restriction h).hom.app
          ((SemilinearSections.evaluation.{c, v, max c v r} J B τ n).obj M))).val.app U x)
  have hr := hV n _ U
    (((a n).unit.app ((SemilinearSections.evaluation.{c, v, max c v r} J B τ n).obj M)).val.app U
      (((SemilinearSections.transition J
        B τ h).app M).val.app U x))
  have hy' := congrArg (fun z ↦ ((a n).unit.app
    ((SemilinearSections.evaluation.{c, v, max c v r} J B τ n).obj M)).val.app U z) (eq_of_heq hy)
  exact (heq_of_eq hs).trans (hl.symm.trans
    ((heq_of_eq hp).trans (hr.trans (heq_of_eq hy'))))

private theorem whisker_transport
    {A D K : Type*} [Category A] [Category D] [Category K]
    {F : A ⥤ D} {L L' : D ⥤ K} (h : L = L')
    {H : A ⥤ K} (e : H ≅ F ⋙ L) :
    HEq (e ≪≫ Functor.isoWhiskerLeft F (eqToIso h)) e := by
  cases h
  simp

private theorem exact_derived_congr
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory D]
    {L L' : A ⥤ D} [L.Additive] [L'.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L'] (h : L = L') :
    L.mapDerivedCategory = L'.mapDerivedCategory := by
  subst L'
  rfl

private theorem unit_from_transpose
    {A D A' D' : Type*} [Category A] [Category D] [Category A'] [Category D']
    (L : A ⥤ D) (R : D ⥤ A) (a : L ⊣ R) (U : A ⥤ A') (W : D ⥤ D')
    (i : A' ⥤ D') (p : D' ⥤ A') (adj : i ⊣ p)
    (eL : L ⋙ W ≅ U ⋙ i) (eR : R ⋙ U ≅ W ⋙ p)
    (ht : ∀ M N (h : L.obj M ⟶ N),
      U.map (a.homEquiv M N h) ≫ eR.hom.app N =
        adj.homEquiv _ _ (eL.inv.app M ≫ W.map h)) (M : A) :
    U.map (a.unit.app M) ≫ eR.hom.app (L.obj M) ≫ p.map (eL.hom.app M) =
      adj.unit.app (U.obj M) := by
  erw [← a.homEquiv_id M, ← Category.assoc, ht M (L.obj M) (𝟙 _)]
  erw [CategoryTheory.Functor.map_id, Category.comp_id (eL.inv.app M)]
  erw [Adjunction.homEquiv_unit, Category.assoc, ← p.map_comp,
    eL.inv_hom_id_app M, CategoryTheory.Functor.map_id,
    Category.comp_id (adj.unit.app (U.obj M))]

private theorem unitModel_transport
    {X Y : Scheme.{u}} (F : SpTowerShriek.S l E Y ⥤ SpTowerShriek.S l E X)
    (A A' : ∀ n : ℕ,
      Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (SpTowerShriek.B l E X n),
      Σ R : SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (SpTowerShriek.B l E X n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n), L ⊣ R)
    (h : A = A')
    (e : ∀ n, F ⋙ SpTowerShriek.ev l E X n ≅
      SpTowerShriek.ev l E Y n ⋙ (A n).1)
    (hu : SpTowerShriek.OrdinaryUnitTransitionModel l E
      (fun n ↦ (A n).1) (fun n ↦ (A n).2.1) (fun n ↦ (A n).2.2)
      (SpTowerShriek.ev l E Y) (SpTowerShriek.ev l E X)
      (fun h ↦ SemilinearSections.res (SemilinearSections.coefficientMap (Scheme.ProEt.topology Y)
        (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y) h))
      (fun h ↦ SemilinearSections.res (SemilinearSections.coefficientMap (Scheme.ProEt.topology X)
        (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) h))
      (fun h ↦ SemilinearSections.transition (Scheme.ProEt.topology Y)
        (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y) h)
      (fun h ↦ SemilinearSections.transition (Scheme.ProEt.topology X)
        (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) h) F e) :
    SpTowerShriek.OrdinaryUnitTransitionModel l E
      (fun n ↦ (A' n).1) (fun n ↦ (A' n).2.1) (fun n ↦ (A' n).2.2)
      (SpTowerShriek.ev l E Y) (SpTowerShriek.ev l E X)
      (fun h ↦ SemilinearSections.res (SemilinearSections.coefficientMap (Scheme.ProEt.topology Y)
        (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y) h))
      (fun h ↦ SemilinearSections.res (SemilinearSections.coefficientMap (Scheme.ProEt.topology X)
        (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) h))
      (fun h ↦ SemilinearSections.transition (Scheme.ProEt.topology Y)
        (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y) h)
      (fun h ↦ SemilinearSections.transition (Scheme.ProEt.topology X)
        (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) h) F
      (fun n ↦ e n ≪≫ Functor.isoWhiskerLeft _
        (eqToIso (congrArg (fun a ↦ (a n).1) h))) := by
  subst A'
  simpa only [eqToIso_refl, Functor.isoWhiskerLeft_refl, Iso.trans_refl] using hu

-- The geometry records require many dependent category and instance checks.
/-- Choose geometry before constructing any coefficient-unit comparison.
Source: Stacks 03D2, 03D7; Zheng Construction 4.1 and Lemma 4.10; blueprint
`sk-lem-sp-tower-bound-operations.proof.md`, clause (2).
(blueprint: lem-sfb-tower-class-section-geometry-existence).

Proof: take the ramification and strict sequence-site realization of
strictBaseCoordinates. At each scheme select the semilinear system
calculus. On the actual constant quotient rings transport the canonical algebraic
inverse image through proEtaleConstantRingComparison. Its coefficient squares
commute by naturality of the constant-section maps. Use ordinaryInverseSystem_exists
on these inverse images. For the right adjoints use proEtaleConstantRingPushforward
with proEtaleConstantRingAdjunction, and use the identity on their underlying
section sheaves. The normalized tensor-insertion formula of that adjunction
identifies its underlying transpose with the set adjunction, as required by
ordinaryDirectSystem_exists. Assemble the ordinary system Hom equivalence and
adjunction. Keep its actual level functors, adjunctions and identity underlying
comparisons when constructing GeometryOrdinary. Apply semilinearGeometryEvaluation
and semilinearGeometryTensor to these fixed ordinary data and the two selected
calculi. Derive the ordinary adjunctions canonically; their unit and counit
identities and ordinaryPullTransition give the transition and projection formulas.
Transport the resulting generic Geometry to the constant quotient presentation,
retaining the bundled level adjunctions and all evaluation comparisons. This
produces SpTowerShriek.Geometry with the stated identity on sections. Its actual
finite-unit transition law follows from the restriction-underlying identity and
set-sheaf adjunction naturality. No coefficient-unit comparison is constructed.
All constructions apply
also to empty schemes and the positive coefficient level indexed by zero. -/
theorem exists_sectionGeometry {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ b : SpTowerShriek.Base l E, ∃ g : SpTowerShriek.Geometry l E b f,
      ∀ (n : ℕ)
        (N : SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
          (g.generic.coefficients n)) (U : Y.ProEtᵒᵖ)
        (x : ((SemilinearSections.underlying.{u + 1, u, u + 1}
          (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n)).obj
            ((g.generic.levelPush n).obj N)).obj.obj U),
        HEq (((g.generic.levelPushUnderlying n).hom.app N).hom.app U x) x := by
  classical
  obtain ⟨b, _⟩ := SpTowerShriek.strictBaseCoordinates l E
  obtain ⟨I, a, hmodules, hpackage, hI, ha⟩ :=
    finite_sectionInverseImages l E f
  let J := Scheme.ProEt.topology Y
  let J' := Scheme.ProEt.topology X
  let B := SpTowerShriek.B l E Y
  let τ := SpTowerShriek.tau l E Y
  let F := SpTowerShriek.B l E X
  let σ := SpTowerShriek.tau l E X
  let uInv := Scheme.proEtaleSheafInverseImage f (Type (u + 1))
  let uPush := Scheme.proEtaleSheafDirectImage f (Type (u + 1))
  let adjSet := Scheme.proEtaleSheafAdjunction f (Type (u + 1))
  let V := fun n ↦ Scheme.proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f
  let : PreservesFiniteLimits uInv :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 Y)).2.2.2.1
  let eV (n : ℕ) : V n ⋙ underlying.{u + 1, u, u + 1} J (B n) ≅
      underlying.{u + 1, u, u + 1} J' (F n) ⋙ uPush :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  have ha' n (M : SemilinearSections.Mod.{u + 1, u, u + 1} J (B n))
      (N : SemilinearSections.Mod.{u + 1, u, u + 1} J' (F n)) (h : (I n).modules.obj M ⟶ N) :
      (underlying.{u + 1, u, u + 1} J (B n)).map ((a n).homEquiv M N h) ≫
          (eV n).hom.app N =
        adjSet.homEquiv _ _ ((I n).moduleUnderlying.inv.app M ≫
          (underlying.{u + 1, u, u + 1} J' (F n)).map h) := by
    change (underlying.{u + 1, u, u + 1} J (B n)).map ((a n).homEquiv M N h) ≫ 𝟙 _ = _
    exact (Category.comp_id _).trans (ha n M N h)
  let (n : ℕ) : PreservesFiniteLimits (I n).modules :=
    algebraicInverse_limits.{u + 1, u, u + 1} J J' uInv (B n) (F n) (I n)
  let (n : ℕ) : PreservesColimits (I n).modules := (a n).leftAdjoint_preservesColimits
  let (n : ℕ) : (I n).modules.Additive :=
    Functor.additive_of_preserves_binary_products _
  let (n : ℕ) : (V n).Additive := (a n).right_adjoint_additive
  obtain ⟨P⟩ := ordinaryInverseSystem_exists.{u + 1, u, u + 1} J B τ J' uInv F σ I hI
  obtain ⟨D⟩ := ordinaryDirectSystem_exists.{u + 1, u, u + 1} J B τ J' uInv F σ I P V a
    hI uPush adjSet eV ha'
  let core : Adjunction.CoreHomEquiv P.pull D.push :=
    { homEquiv := D.homEquiv
      homEquiv_naturality_left_symm := by
        intro M M' N f g
        apply (D.homEquiv M N).injective
        rw [Equiv.apply_symm_apply,
          system_transpose_natural_left.{u + 1, u, u + 1} J B τ J' uInv P a D,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right :=
        system_transpose_natural_right.{u + 1, u, u + 1} J B τ J' uInv P a D _ }
  let aSys := Adjunction.mkOfHomEquiv core
  let : PreservesColimits P.pull := aSys.leftAdjoint_preservesColimits
  let : P.pull.Additive := Functor.additive_of_preserves_binary_products _
  let : D.push.Additive := aSys.right_adjoint_additive
  have hunit n (M : SemilinearSections.Mod.{u + 1, u, u + 1} J (B n)) :
      (underlying.{u + 1, u, u + 1} J (B n)).map ((a n).unit.app M) ≫
          (eV n).hom.app ((I n).modules.obj M) ≫
          uPush.map ((I n).moduleUnderlying.hom.app M) =
        adjSet.unit.app ((underlying.{u + 1, u, u + 1} J (B n)).obj M) := by
    exact unit_from_transpose (I n).modules (V n) (a n)
      (underlying.{u + 1, u, u + 1} J (B n))
      (underlying.{u + 1, u, u + 1} J' (F n))
      uInv uPush adjSet (I n).moduleUnderlying (eV n) (ha' n) M
  have hsunit n (M : Systems.{u + 1, u, u + 1} J B τ) :
      (evaluation.{u + 1, u, u + 1} J B τ n).map (aSys.unit.app M) ≫
          (D.component n).hom.app (P.pull.obj M) ≫
          (V n).map ((P.component n).hom.app M) =
        (a n).unit.app ((evaluation.{u + 1, u, u + 1} J B τ n).obj M) := by
    rw [← aSys.homEquiv_id M]
    dsimp only [aSys]
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    change (evaluation.{u + 1, u, u + 1} J B τ n).map
      (D.homEquiv M (P.pull.obj M) (𝟙 _)) ≫ _ ≫ _ = _
    rw [← Category.assoc, D.homEquiv_component, ← (a n).homEquiv_naturality_right]
    simpa using (a n).homEquiv_id ((evaluation.{u + 1, u, u + 1} J B τ n).obj M)
  have hmodel : SpTowerShriek.OrdinaryUnitTransitionModel l E
      (fun n ↦ (I n).modules) V a
      (SpTowerShriek.ev l E Y) (SpTowerShriek.ev l E X)
      (fun h ↦ SemilinearSections.res.{u + 1, u, u + 1} (SemilinearSections.coefficientMap.{u + 1,
        u, u + 1} J B τ h))
      (fun h ↦ SemilinearSections.res.{u + 1, u, u + 1} (SemilinearSections.coefficientMap.{u + 1,
        u, u + 1} J' F σ h))
      (fun h ↦ SemilinearSections.transition.{u + 1, u, u + 1} J B τ h) (fun h ↦
        SemilinearSections.transition.{u + 1, u, u + 1} J' F σ h)
      P.pull P.component := by
    unfold SpTowerShriek.OrdinaryUnitTransitionModel
    exact unit_point.{u + 1, u, u + 1} J B τ J' uInv uPush adjSet F σ I P V a eV ha'
      (fun _ _ _ _ ↦ HEq.rfl)
  let O : GeometryOrdinary.{u + 1, u, u + 1} J B τ J' uInv uPush adjSet :=
    { coefficients := F
      coefficientTransition := σ
      inverseImage := I
      coefficient_compatibility := hI
      levelPush := V
      levelAdjunction := a
      levelPushUnderlying := eV
      level_unit_underlying := hunit
      pull := P.pull
      ordinaryPullEvaluation := P.component
      push := D.push
      ordinaryAdjunction := aSys
      ordinaryPullEvaluation_sections := P.component_sections
      ordinaryPushEvaluation := D.component
      ordinaryPushEvaluation_sections := D.component_sections
      ordinary_unit_evaluation := hsunit
      restrictionPullback := P.restriction
      restrictionPullback_underlying := P.restriction_underlying
      ordinaryPullTransition := P.transition }
  let systems := b.calculus Y
  let target := b.calculus X
  let : ∀ n, Abelian.HasKInjectiveResolutions
      (SemilinearSections.Mod.{u + 1, u, u + 1} J' (O.coefficients n)) := fun n ↦ inferInstance
  let : Abelian.HasKInjectiveResolutions
      (Systems.{u + 1, u, u + 1} J' O.coefficients O.coefficientTransition) :=
    b.kinjective X
  obtain ⟨evData⟩ := semilinearGeometryEvaluation.{u + 1, u, u + 1}
    J B τ J' uInv uPush adjSet systems O target
  obtain ⟨T⟩ := semilinearGeometryTensor.{u + 1, u, u + 1}
    J B τ J' uInv uPush adjSet systems O target
  let G : SemilinearSections.Geometry.{u + 1, u, u + 1}
      J B τ systems J' uInv uPush adjSet := {
    toGeometryBase := GeometryOrdinary.toBase.{u + 1, u, u + 1} J B τ J' uInv uPush adjSet O target
    derivedLevelAdjunction := fun n ↦
      (O.levelAdjunction n).mapDerivedCategoryRightDerivedAdjunction
    derivedLevelAdjunction_canonical := fun _ ↦ rfl
    derivedAdjunction_canonical := rfl
    pullEvaluation := geometryPullEvaluation.{u + 1, u, u + 1} J B τ J' uInv uPush adjSet O
    pushEvaluation := evData.pushEvaluation
    unit_evaluation := evData.unit_evaluation
    counit_evaluation := evData.counit_evaluation
    coefficientPullback := evData.coefficientPullback
    tensorPullback := T.tensorPullback
    levelTensorPullback := T.levelTensorPullback
    tensorPullback_evaluation := T.tensorPullback_evaluation
    ordinaryPullEvaluation_sections := O.ordinaryPullEvaluation_sections
    ordinaryPushEvaluation := O.ordinaryPushEvaluation
    ordinaryPushEvaluation_sections := O.ordinaryPushEvaluation_sections
    ordinary_unit_evaluation := O.ordinary_unit_evaluation
    derivedLevel_transpose_model := fun n P I _ f ↦
      CategoryTheory.Adjunction.canonical_transpose (O.levelAdjunction n) P I f
    derived_transpose_model := fun P I _ f ↦
      CategoryTheory.Adjunction.canonical_transpose O.ordinaryAdjunction P I f
    pullEvaluation_model := fun _ ↦ rfl
    restrictionPullback := O.restrictionPullback
    restrictionPullback_underlying := O.restrictionPullback_underlying
    ordinaryPullTransition := O.ordinaryPullTransition
    coefficientPullback_transpose := evData.coefficientPullback_transpose
    levelTensorModel := T.levelTensorModel
    levelTensor_pure := T.levelTensor_pure
    tensorModel := T.tensorModel
    tensor_ordinary_evaluation := T.tensor_ordinary_evaluation }
  have hpull : G.PullTransitionFormula J B τ systems J' uInv uPush adjSet :=
    semilinearGeometryTransitionExistence J B τ systems J' uInv uPush adjSet G
  let g : SpTowerShriek.Geometry l E b f := {
    generic := G
    transitionFormula := push_transition_of_pull J B τ systems J' uInv uPush adjSet G hpull
    pullTransitionFormula := hpull
    projectionEvaluation := projection_evaluation J B τ systems J' uInv uPush adjSet G
    coefficients := rfl
    transitions := HEq.rfl
    target := HEq.rfl
    pull := O.pull
    push := O.push
    pull_eq := HEq.rfl
    push_eq := HEq.rfl
    ordinaryAdjunction := O.ordinaryAdjunction
    ordinaryAdjunction_eq := HEq.rfl
    derivedAdjunction_eq := HEq.rfl
    ordinaryPullEvaluation := fun n ↦ O.ordinaryPullEvaluation n ≪≫
      Functor.isoWhiskerLeft _ (eqToIso (hmodules n))
    ordinaryUnitTransition := by
      unfold SpTowerShriek.OrdinaryUnitTransition
      exact unitModel_transport l E P.pull _ _ (funext hpackage) P.component hmodel
    ordinaryPullEvaluation_eq := fun n ↦
      whisker_transport (hmodules n) (O.ordinaryPullEvaluation n)
    pullEvaluation := fun n ↦ G.pullEvaluation n ≪≫
      Functor.isoWhiskerLeft _ (eqToIso (exact_derived_congr (hmodules n)))
    pullEvaluation_eq := fun n ↦
      whisker_transport (exact_derived_congr (hmodules n))
        (G.pullEvaluation n)
    ordinaryPushEvaluation := O.ordinaryPushEvaluation
    ordinaryPushEvaluation_eq := fun _ ↦ HEq.rfl
    levelAdjunction_eq := fun n ↦ heq_of_eq (hpackage n)
    pushEvaluation := G.pushEvaluation
    pushEvaluation_eq := fun _ ↦ HEq.rfl
    tensorPullback := G.tensorPullback
    tensorPullback_eq := HEq.rfl }
  exact ⟨b, g, fun _ _ _ _ ↦ HEq.rfl⟩

end AlgebraicGeometry.ProEtale.SpTowerClasses
