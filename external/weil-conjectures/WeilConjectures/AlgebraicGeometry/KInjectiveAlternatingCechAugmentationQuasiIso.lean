/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
import WeilConjectures.AlgebraicGeometry.InjectiveTermsAlternatingCechAugmentation
import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalHomotopy
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.AlgebraicGeometry.AlternatingCechComputes
import WeilConjectures.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions

/-! # Čech augmentation of a K-injective complex

Source: Stacks Project, Cohomology, Lemma 08C1.
(blueprint: lem-sc-kinjective-alternating-cech-augmentation-quasi-iso)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The finite-cover Čech augmentation is a quasi-isomorphism on every K-injective
complex. Injectivity of its individual terms is not required.

Source: Stacks Project, Cohomology, Lemma 08C1 and Tag 01EP.
(blueprint: lem-sc-kinjective-alternating-cech-augmentation-quasi-iso).

Proof: Resolve J into a K-injective complex I with injective terms. Each augmented
alternating section row of I is exact: degree zero is the sheaf gluing axiom, and
positive degrees follow from injective Čech acyclicity and ordered-to-alternating
comparison. The cone of the augmentation is the total of these exact augmented rows.
It has only finitely many Čech columns. Eliminate a total cocycle column by column
using row exactness; at the augmentation column its injectivity eliminates the last
component. This proves acyclicity of the cone and hence that the augmentation of I
is a quasi-isomorphism. The quasi-isomorphism J → I between K-injectives is a homotopy
equivalence. Termwise sections preserve its homotopies. Čech totalization preserves
homotopies as well: in Čech degree p apply the sectionwise homotopy with sign (-1)^p;
the horizontal homotopy terms cancel and the vertical equation is dh + hd.
The augmentation's naturality square therefore has homotopy equivalences as its two
vertical maps. Two-out-of-three transports the quasi-isomorphism from I to J.
For the empty covering the scheme is empty and all its section modules are zero. -/
theorem kInjective_alternatingCech_augmentation_quasiIso
    (X : Scheme.{u}) (r : ℕ) (U : Fin r → X.Opens) (hU : iSup U = ⊤)
    (J : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [J.IsKInjective] :
    QuasiIso ((alternatingCechAugmentation U).app J) := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u} C).obj J
  let j : J ⟶ I := (CochainComplex.toKInjectiveResolution.{u} C).app J
  have hj : QuasiIso j :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} C J).2
  have : I.IsKInjective := inferInstance
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff j).mp hj
  let S := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let T := alternatingCechTotalFunctor U
  have hS : QuasiIso (S.map j) := by
    rw [← he]
    exact (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomotopyEquiv e
      |>.quasiIso_hom
  have hT : QuasiIso (T.map j) := by
    obtain ⟨h₁⟩ := alternatingCechTotal_map_homotopy U e.homotopyHomInvId
    obtain ⟨h₂⟩ := alternatingCechTotal_map_homotopy U e.homotopyInvHomId
    change Homotopy (T.map (e.hom ≫ e.inv)) (T.map (𝟙 J)) at h₁
    change Homotopy (T.map (e.inv ≫ e.hom)) (T.map (𝟙 I)) at h₂
    let eT : HomotopyEquiv (T.obj J) (T.obj I) :=
      { hom := T.map e.hom
        inv := T.map e.inv
        homotopyHomInvId := by
          rw [T.map_comp, T.map_id] at h₁
          exact h₁
        homotopyInvHomId := by
          rw [T.map_comp, T.map_id] at h₂
          exact h₂ }
    rw [← he]
    exact eT.quasiIso_hom
  have hI : QuasiIso ((alternatingCechAugmentation U).app I) :=
    injectiveTerms_alternatingCech_augmentation_quasiIso X r U hU I
      (fun n ↦ inferInstance)
  have hcomp : QuasiIso
      (((alternatingCechAugmentation U).app J) ≫ T.map j) := by
    rw [← (alternatingCechAugmentation U).naturality j]
    change QuasiIso (S.map j ≫ (alternatingCechAugmentation U).app I)
    infer_instance
  exact (quasiIso_iff_comp_right ((alternatingCechAugmentation U).app J) (T.map j)).mp
    hcomp

end AlgebraicGeometry
