/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Strict.StrictScalarKoszulInstances
import all WeilConjectures.CategoryTheory.Koszul.KoszulModuleBasisEvaluation
import all WeilConjectures.CategoryTheory.Koszul.KoszulTensorEvaluationComponents

/-! # KoszulTensorEvaluationCoordinates for strict Koszul comparison

Source: Stacks Project, Tags 0A0E and 0913.
(blueprint: lem-f5-koszul-tensor-evaluation-coordinates).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FlatScalarKoszul

variable {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}
variable {R B : Sheaf J CommRingCat.{u}}

open MonoidalCategory
open scoped CategoryTheory.Prod

attribute [local irreducible] homComplexFunctor
  SheafOfModules.tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction
  Localization.Monoidal.tensorBifunctor

attribute [local instance] gradedTensorCache gradedGoodTensorLeftCache
  gradedGoodTensorRightCache gradedFourCache tensorPreservesEmptyLeftCache
  tensorPreservesEmptyRightCache cachedModuleMonoidal cachedModuleSymmetric
  cachedModulePreadditive cachedModuleClosed cachedComplexMonoidal
  cachedComplexBraided cachedComplexClosed

private theorem unitTensor_inclusion (O : Sheaf J CommRingCat.{u})
    (N : ringedSiteComplex O) (p : ℤ) :
    let : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
    let := cachedModuleMonoidal O
    let := cachedModuleSymmetric O
    let := cachedModulePreadditive O
    let := cachedModuleClosed O
    HomologicalComplex.ιTensorObj (ringedSiteRingComplex O) N 0 p p (zero_add p) ≫
        (λ_ N).hom.f p =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (one O)).hom ▷ N.X p ≫
        (λ_ (N.X p)).hom := by
  let : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
  let := cachedModuleMonoidal O
  let := cachedModuleSymmetric O
  let := cachedModulePreadditive O
  let := cachedModuleClosed O
  dsimp only
  apply (cancel_epi ((λ_ (N.X p)).inv ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (one O)).inv ▷ N.X p)).mp
  simp only [Category.assoc]
  erw [← reassoc_of% (HomologicalComplex.leftUnitor'_inv N p)]
  change (λ_ N).inv.f p ≫ (λ_ N).hom.f p = _
  rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight,
    Category.id_comp]

/-- Evaluate the degree-n Hom component on a fixed homogeneous unit vector.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-koszul-tensor-evaluation-coordinates). -/
def basisHomCoordinate (O : Sheaf J CommRingCat.{u})
    (P N : ringedSiteComplex O) (d : ℤ) (b : one O ⟶ P.X d) (n : ℤ) :
    (homComplex (R := O) P N).X n ⟶ N.X (n + d) :=
  homComplexπ P N n d (n + d) (add_comm _ _) ≫
    SheafOfModules.homObjMap (R := O) b (𝟙 _) ≫
    (SheafOfModules.homObjUnitIso (R := O) (N.X (n + d))).hom

/-- The dual coordinate is zero unless the vector and Hom degrees sum to zero.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-koszul-tensor-evaluation-coordinates). -/
def basisDualCoordinate (O : Sheaf J CommRingCat.{u})
    (P : ringedSiteComplex O) (d : ℤ) (b : one O ⟶ P.X d) (q : ℤ) :
    (homComplex (R := O) P (ringedSiteRingComplex O)).X q ⟶ one O :=
  if h : d + q = 0 then
    homComplexπ P (ringedSiteRingComplex O) q d 0 h ≫
      SheafOfModules.homObjMap (R := O) b
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (one O)).hom ≫
      (SheafOfModules.homObjUnitIso (R := O) (one O)).hom
  else 0

/-- Descend dual-coordinate contraction along the total tensor coproduct.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-koszul-tensor-evaluation-coordinates). -/
def basisTensorCoordinate (O : Sheaf J CommRingCat.{u})
    (P N : ringedSiteComplex O) (d : ℤ) (b : one O ⟶ P.X d) (n : ℤ) :
    (((ringedKoszulTensor O).obj N).obj
      (homComplex (R := O) P (ringedSiteRingComplex O))).X n ⟶ N.X (n + d) :=
  letI : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
  letI := cachedModuleMonoidal O
  letI := cachedModuleSymmetric O
  letI := cachedModulePreadditive O
  letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
  HomologicalComplex.mapBifunctorDesc
    (K₁ := N) (K₂ := homComplex (R := O) P (ringedSiteRingComplex O))
    (F := tensor O) (c := .up ℤ) (fun p q _ ↦
      if hp : p = n + d then
        ((tensor O).obj (N.X p)).map (basisDualCoordinate O P d b q) ≫
          (ρ_ (N.X p)).hom ≫ eqToHom (congrArg N.X hp)
      else 0)

-- Compare the total tensor inclusions and cancel the signed evaluation factors.
/-- Canonical signed tensor-Hom evaluation preserves every homogeneous basis coordinate.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
Proof step 1: Define the Hom coordinate by homComplex projection, precomposition with b and Hom-
unit evaluation. Define the dual coordinate to be zero outside degree -d; in that degree use the
single-unit component and Hom-unit evaluation. Define the tensor coordinate by the total-tensor
coproduct descent with this dual coordinate.
Proof step 2: It suffices to compare composites with each tensor inclusion N[p] tensor
Hom(P,unit)[q], p+q=n. The signed curry component formula and curryBasis contribute (-1)^(dn).
The explicit uncurried evaluation component contributes (-1)^(pq+dq).
Proof step 3: When p=n+d, one has d+q=0. The three signs multiply to one because dn+pq+dq=2dq.
Apply the unit tensor inclusion and module basis contraction identities; naturality of Hom and
unit evaluation identify the remaining map with the dual coordinate followed by the right unitor.
Otherwise d+q is nonzero; the corresponding single-unit component is zero, so evaluation and the
defined tensor coordinate both vanish. Tensor coproduct extensionality finishes.
(blueprint: lem-f5-koszul-tensor-evaluation-coordinates). -/
theorem evaluation_coordinates (O : Sheaf J CommRingCat.{u})
    (P N : ringedSiteComplex O) (d : ℤ) (b : one O ⟶ P.X d) (n : ℤ) :
    (ringedComplexTensorEvaluation O P N).f n ≫ basisHomCoordinate O P N d b n =
      basisTensorCoordinate O P N d b n := by
  let : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
  let := cachedModuleMonoidal O
  let := cachedModuleSymmetric O
  let := cachedModulePreadditive O
  let := cachedModuleClosed O
  let := cachedComplexClosed O
  let D := homComplex (R := O) P (ringedSiteRingComplex O)
  rw [evaluation_eq_curry]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  have hc :
      HomologicalComplex.ιTensorObj N D p q n hpq ≫
          (MonoidalClosed.curry (evaluationUncurry O P N)).f n ≫
          basisHomCoordinate O P N d b n =
        (d * n).negOnePow •
          ((λ_ (N.X p ⊗ D.X q)).inv ≫
            b ▷ (N.X p ⊗ D.X q) ≫
            HomologicalComplex.mapBifunctor₂₃.ι (tensor O) (tensor O) P N D
              (.up ℤ) (.up ℤ) (.up ℤ) d p q (n + d) (by
                change d + p + q = n + d
                omega) ≫
            (evaluationUncurry O P N).f (n + d)) := by
    dsimp only [basisHomCoordinate]
    rw [reassoc_of% (ringedComplexCurry_component O
        (evaluationUncurry O P N) n d (n + d) (add_comm _ _))]
    simp only [Linear.comp_units_smul, Linear.units_smul_comp]
    congr 1
    rw [← MonoidalClosed.curry_natural_left_assoc, curryBasis O]
    rw [CochainComplex.Monoidal.ι₂₃_eq P N D d p q n (n + d) hpq (add_comm _ _)]
    simp only [Category.assoc]
    rfl
  rw [hc]
  dsimp only [basisTensorCoordinate]
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  by_cases hp : p = n + d
  · subst p
    have ht : d + q = 0 := by omega
    rw [dite_eq_left rfl, eqToHom_refl, Category.comp_id]
    erw [evaluationUncurry_component O P N d (n + d) q 0 (n + d)
      ht (by omega), Linear.comp_units_smul]
    rw [unitTensor_inclusion]
    simp only [← comp_whiskerRight_assoc]
    simp only [Linear.comp_units_smul, smul_smul]
    erw [basisContraction]
    have hu := curryBasis O (b)
      (MonoidalClosed.uncurry
        (homComplexπ P (ringedSiteRingComplex O) q d 0 ht) ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (one O)).hom)
    dsimp only at hu
    erw [MonoidalClosed.curry_natural_right, MonoidalClosed.curry_uncurry] at hu
    rw [← hu]
    have hs : (d * n).negOnePow * ((n + d) * q + d * q).negOnePow = 1 := by
      rw [← Int.negOnePow_add]
      have he : d * n + ((n + d) * q + d * q) = 2 * (d * q) := by
        rw [show q = -d by omega]
        ring
      rw [he, Int.negOnePow_two_mul]
    simp only [hs, one_smul]
    change _ = N.X (n + d) ◁ basisDualCoordinate O P d b q ≫ (ρ_ (N.X (n + d))).hom
    unfold basisDualCoordinate
    rw [dite_eq_left (show d + q = 0 from ht)]
    erw [moduleHomMap]
    simp only [Category.assoc]
    exact congrArg (fun z ↦ N.X (n + d) ◁
      (homComplexπ P (ringedSiteRingComplex O) q d 0 ht ≫ z) ≫
        (ρ_ (N.X (n + d))).hom)
      (homPostBasis O (b)
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (one O)).hom)
  · rw [dite_eq_right hp]
    have ht : d + q ≠ 0 := by omega
    erw [evaluationUncurry_component O P N d p q (d + q) (n + d)
      rfl (by omega), Linear.comp_units_smul]
    have hz : MonoidalClosed.uncurry
        (homComplexπ P (ringedSiteRingComplex O) q d (d + q) rfl) = 0 :=
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (one O) (d + q) ht).eq_of_tgt _ _
    simp only [hz]
    erw [MonoidalPreadditive.zero_whiskerRight]
    simp only [zero_comp, comp_zero, smul_zero]

end CategoryTheory.FlatScalarKoszul
