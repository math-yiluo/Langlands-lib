/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.Algebra.Homology.HomologyEvaluationDefinitions
import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import WeilConjectures.Mathlib.Algebra.Homology.SingleHomology
/-! Homology quotient comparison square.
(blueprint: new-t4-open-over-hom-complex-cycle-projection-comparison-homology-square). -/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

local instance (priority := 2000) openOverHomComplexCycleProjectionComparisonCategoryHomology
    (X : Scheme.{u}) : Category X.Modules :=
  SheafOfModules.instCategory (R := X.ringCatSheaf)
local instance (priority := 2000) openOverHomComplexCycleProjectionComparisonPreadditiveHomology
    (X : Scheme.{u}) : Preadditive X.Modules :=
  SheafOfModules.instPreadditive X.ringCatSheaf
noncomputable local instance (priority := 2000)
    openOverHomComplexCycleProjectionComparisonAbelianHomology
    (X : Scheme.{u}) : Abelian X.Modules :=
  SheafOfModules.instAbelian X.ringCatSheaf
set_option backward.isDefEq.respectTransparency false in
/-- A restricted chain isomorphism induces compatible cycle and homology comparisons.
Source: Stacks Project, Tag 08DL, exactness of restriction; Mathlib's short-complex
mapCyclesIso and mapHomologyIso comparison and naturality identities.
(blueprint: new-t4-open-over-hom-complex-cycle-projection-comparison-homology-square).
Proof: Restriction to an open is exact, since it computes kernels sectionwise and
cokernels after sheafification, which commutes with open restriction. The over-site
functor has the same properties, transported through the open-site equivalence.
Let z and d be the inverse mapCyclesIso and mapHomologyIso comparisons for P.
Compose z with the cycle isomorphism induced by h, and d with the homology
isomorphism induced by h, obtaining c and a. Naturality of cycle inclusions gives
the first identity. Naturality of the homology quotient under exact functors and
chain maps gives the second identity. In particular both comparisons come from
the SAME chain isomorphism; an arbitrary cycle isomorphism is insufficient. -/
theorem openOver_chain_cycle_homology_comparison (X : Scheme.{u})
    (V : X.Opens) (W : V.toScheme.Opens)
    (P : CochainComplex X.Modules ℤ)
    (Q : CochainComplex (SheafOfModules.{u} (V.toScheme.ringCatSheaf.over W)) ℤ)
    (h : (moduleOpenOverComplexFunctor X V W).obj P ≅ Q) (n : ℤ) :
    let F := Scheme.Modules.restrictFunctor V.ι ⋙
      SheafOfModules.overFunctor V.toScheme.ringCatSheaf W
    ∃ a : F.obj (P.homology n) ≅ Q.homology n,
    ∃ c : F.obj (P.cycles n) ≅ Q.cycles n,
      F.map (P.iCycles n) ≫ h.hom.f n = c.hom ≫ Q.iCycles n ∧
      F.map (P.homologyπ n) ≫ a.hom = c.hom ≫ Q.homologyπ n := by
  intro F
  have : PreservesFiniteLimits (SheafOfModules.overFunctor X.ringCatSheaf V) :=
    moduleOverFunctor_limits X.toRingedSpace V
  have : PreservesFiniteLimits
      (SheafOfModules.overFunctor V.toScheme.ringCatSheaf W) :=
    moduleOverFunctor_limits V.toScheme.toRingedSpace W
  have : PreservesFiniteColimits
      (SheafOfModules.overFunctor V.toScheme.ringCatSheaf W) :=
    moduleOverFunctor_colimits V.toScheme.toRingedSpace W
  have : PreservesFiniteLimits
      (SheafOfModules.overFunctor X.ringCatSheaf V ⋙ (Scheme.Modules.overEquiv V).functor) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (Scheme.Modules.restrictFunctor V.ι) :=
    preservesFiniteLimits_of_natIso (Scheme.Modules.overFunctorEquiv V)
  have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor V.ι) :=
    (Scheme.Modules.restrictAdjunction V.ι).leftAdjoint_preservesColimits
  have : F.PreservesZeroMorphisms := moduleOpenOver_preservesZeroMorphisms X V W
  have : PreservesFiniteLimits F := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits F := comp_preservesFiniteColimits _ _
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  let z := (P.sc n).mapCyclesIso F
  let d := (P.sc n).mapHomologyIso F
  refine ⟨d.symm ≪≫ HomologicalComplex.homologyMapIso h n,
    z.symm ≪≫ HomologicalComplex.cyclesMapIso h n, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [← cancel_epi z.hom]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    erw [ShortComplex.mapCyclesIso_hom_iCycles (P.sc n) F]
    exact (HomologicalComplex.cyclesMap_i h.hom n).symm
  · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [← cancel_epi z.hom]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    erw [← ShortComplex.homologyπ_mapHomologyIso_hom F (P.sc n)]
    simp only [d, Category.assoc, Iso.hom_inv_id_assoc]
    exact HomologicalComplex.homologyπ_naturality h.hom n
end CategoryTheory
