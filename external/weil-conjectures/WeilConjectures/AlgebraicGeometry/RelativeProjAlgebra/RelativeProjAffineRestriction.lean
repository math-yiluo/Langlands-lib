/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProjAlgebra.RelativeProjData
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
import WeilConjectures.AlgebraicGeometry.RelativeProj.GradedTensor
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange

/-! # Affine restriction of relative Proj charts

## References

* Stacks Project, Constructions, Tags 01NO and 01NP
* Stacks, Tags 01LH and 01NQ
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TensorProduct

noncomputable section

namespace AlgebraicGeometry.RelativeProjAlgebra

private theorem baseChange_of_directSum
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M N : ℕ → Type*} [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (M i)] [∀ i, Module R (N i)] [∀ i, Module S (N i)]
    [∀ i, IsScalarTower R S (N i)] (f : ∀ i, M i →ₗ[R] N i)
    (h : IsBaseChange S (DirectSum.lmap f)) (i : ℕ) : IsBaseChange S (f i) := by
  classical
  let e := TensorProduct.directSumRight R S S M
  let g := DirectSum.lmap (fun i ↦ (f i).liftBaseChange S)
  have hg : g.comp e.toLinearMap = h.equiv.toLinearMap := by
    apply LinearMap.ext
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul s m =>
        apply DirectSum.ext
        intro j
        simp [g, e, TensorProduct.directSumRight_tmul, IsBaseChange.equiv_tmul,
          DirectSum.smul_apply]
    | add x y hx hy => simp_all
  have hb : Function.Bijective g := by
    have hh : Function.Bijective (g.comp e.toLinearMap) := by
      rw [hg]
      exact h.equiv.bijective
    exact (Function.Bijective.of_comp_iff g e.bijective).mp hh
  have hi : Function.Bijective ((f i).liftBaseChange S) :=
    ⟨(DirectSum.lmap_injective _).mp hb.1 i, (DirectSum.lmap_surjective _).mp hb.2 i⟩
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hi) (by simp)

variable {X : Scheme.{u}} (A : RelativeProjAlgebra X)

/-- The section algebra structure supplied by the algebra sheaf. -/
noncomputable instance sectionAlgebra (V : X.affineOpens) :
    Algebra Γ(X, V.1) (A.sections V) := (A.algebra.obj.hom.hom.app (op V.1)).hom.toAlgebra

/-- Homogeneous section images as submodules over the base section ring. -/
noncomputable def grade (V : X.affineOpens) (n : ℕ) :
    Submodule Γ(X, V.1) (A.sections V) :=
  ((Sigma.ι A.piece n ≫ A.decomposition.hom).val.app (op V.1)).hom.range

/-- The section grading, with its base-module structure. -/
noncomputable instance gradeRing (V : X.affineOpens) : GradedAlgebra (A.grade V) where
  toDecomposition :=
    { decompose' := DirectSum.decompose (A.sectionGrade V)
      left_inv := fun a ↦ (DirectSum.decompose (A.sectionGrade V)).left_inv a
      right_inv := fun a ↦ (DirectSum.decompose (A.sectionGrade V)).right_inv a }
  one_mem := A.sectionGrade_one V
  mul_mem := A.sectionGrade_mul V

/-- Identity on sections, viewed as a map to the submodule grading. -/
def toGrade (V : X.affineOpens) : A.sectionGrade V →+*ᵍ A.grade V :=
  { RingHom.id _ with map_mem := fun ha ↦ ha }

/-- Identity on sections, viewed as a map to the additive-subgroup grading. -/
def fromGrade (V : X.affineOpens) : A.grade V →+*ᵍ A.sectionGrade V :=
  { RingHom.id _ with map_mem := fun ha ↦ ha }

/-- The identity grading comparison preserves the irrelevant ideal. -/
lemma toGrade_irrelevant (V : X.affineOpens) :
    HomogeneousIdeal.irrelevant (A.grade V) ≤
      (HomogeneousIdeal.irrelevant (A.sectionGrade V)).map (A.toGrade V) := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro n hn x hx
  exact Ideal.mem_map_of_mem (A.toGrade V)
    (HomogeneousIdeal.mem_irrelevant_of_mem _ hn hx)

/-- The inverse grading comparison preserves the irrelevant ideal. -/
lemma fromGrade_irrelevant (V : X.affineOpens) :
    HomogeneousIdeal.irrelevant (A.sectionGrade V) ≤
      (HomogeneousIdeal.irrelevant (A.grade V)).map (A.fromGrade V) := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro n hn x hx
  exact Ideal.mem_map_of_mem (A.fromGrade V)
    (HomogeneousIdeal.mem_irrelevant_of_mem _ hn hx)

/-- The local Proj is unchanged by retaining the base-module structure of its grading. -/
noncomputable def gradeIso (V : X.affineOpens) :
    A.localProj V ≅ Proj (A.grade V) where
  hom := Proj.map (A.fromGrade V) (A.fromGrade_irrelevant V)
  inv := Proj.map (A.toGrade V) (A.toGrade_irrelevant V)
  hom_inv_id := by
    rw [← Proj.map_comp]
    exact (Proj.map_congr
      (show (A.fromGrade V).comp (A.toGrade V) = .id _ from
        GradedRingHom.ext fun _ ↦ rfl) _ (by simp)).trans Proj.map_id
  inv_hom_id := by
    rw [← Proj.map_comp]
    exact (Proj.map_congr
      (show (A.toGrade V).comp (A.fromGrade V) = .id _ from
        GradedRingHom.ext fun _ ↦ rfl) _ (by simp)).trans Proj.map_id

/-- The grading comparison respects the structural morphism. -/
lemma gradeIso_hom_base (V : X.affineOpens) :
    (A.gradeIso V).hom ≫ Proj.toSpecOfAlgebra (A.grade V) ≫ V.2.isoSpec.inv =
      A.localBase V := by
  dsimp only [gradeIso, Proj.toSpecOfAlgebra, localBase]
  rw [← Category.assoc, ← Category.assoc, Proj.map_toSpecZero]
  simp only [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

end AlgebraicGeometry.RelativeProjAlgebra

namespace GradedRingHom

private theorem gradedBaseChange_of_total
    {R S C E : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [CommRing C] [Algebra R C] [CommRing E] [Algebra S E] [Algebra R E]
    [IsScalarTower R S E]
    {𝒞 : ℕ → Submodule R C} [GradedAlgebra 𝒞]
    {ℰ : ℕ → Submodule S E} [GradedAlgebra ℰ]
    (f : 𝒞 →+*ᵍ ℰ) (hf : ∀ r, f (algebraMap R C r) = algebraMap R E r)
    (h : IsBaseChange S (f.toLinearMap' hf)) : f.IsGradedBaseChange := by
  classical
  refine ⟨hf, fun n ↦ ?_⟩
  have hh : IsBaseChange S (DirectSum.lmap fun i ↦ f.degreeLinearMap hf i) := by
    apply (IsBaseChange.iff_of_equiv_comm (DirectSum.decomposeLinearEquiv 𝒞).symm
      (DirectSum.decomposeLinearEquiv ℰ).symm ?_).mpr h
    refine DirectSum.linearMap_ext R fun i ↦ LinearMap.ext fun a ↦ ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      DirectSum.decomposeLinearEquiv_symm_lof, toLinearMap'_apply,
      LinearEquiv.restrictScalars_apply, DirectSum.lmap_lof]
    rw [DirectSum.lof_eq_of, DirectSum.decomposeLinearEquiv_symm_apply,
      DirectSum.decompose_symm_of]
    rfl
  exact AlgebraicGeometry.RelativeProjAlgebra.baseChange_of_directSum _ hh n

end GradedRingHom

namespace AlgebraicGeometry.RelativeProjAlgebra

variable {X : Scheme.{u}} (A : RelativeProjAlgebra X)

/-- Section restriction as a homomorphism of submodule-graded algebras. -/
def gradeRestriction {V W : X.affineOpens} (h : W ≤ V) : A.grade V →+*ᵍ A.grade W :=
  { A.restriction h with map_mem := fun ha ↦ A.restriction_mem h _ _ ha }

/-- Affine section restrictions are base change in every degree. -/
theorem gradeRestriction_baseChange {V W : X.affineOpens} (h : W ≤ V) :
    (A.gradeRestriction h).IsGradedBaseChangeAlong
      (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom := by
  classical
  let R := Γ(X, V.1)
  let S := Γ(X, W.1)
  let C := A.sections V
  let E := A.sections W
  let f := (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom
  let : Algebra R S := f.toAlgebra
  let : Algebra R E := ((algebraMap S E).comp f).toAlgebra
  let : IsScalarTower R S E := .of_algebraMap_eq' rfl
  let ψ := A.gradeRestriction h
  have hψ : ∀ r : R, ψ (algebraMap R C r) = algebraMap R E r := by
    intro r
    exact congrArg (fun q ↦ q r)
      (congrArg CommRingCat.Hom.hom (A.algebra.obj.hom.hom.naturality
        (homOfLE (X := X.Opens) h).op)).symm
  have hqc : A.algebra.obj.toModule.IsQuasicoherent := A.algebra.property
  let := hqc
  obtain ⟨c, hc, _, ht⟩ :=
    Scheme.Modules.quasiCoherent_affine_section_baseChange X A.algebra.obj.toModule W V h
  have ht' (a : C) (r : S) : c (a ⊗ₜ[R] r) = r • ψ a := by
    exact ht a r
  let d : S ⊗[R] C →ₗ[S] E :=
    { toFun t := c (TensorProduct.comm R S C t)
      map_add' x y := by simp
      map_smul' s t := by
        induction t using TensorProduct.inductionOn with
        | tmul r a =>
            simp only [TensorProduct.smul_tmul', smul_eq_mul,
              TensorProduct.comm_tmul, ht', mul_smul, RingHom.id_apply]
        | add x y hx hy => simp_all }
  have hd : Function.Bijective d := hc.comp (TensorProduct.comm R S C).bijective
  have hb : IsBaseChange S (ψ.toLinearMap' hψ) := by
    apply IsBaseChange.of_equiv (LinearEquiv.ofBijective d hd)
    intro a
    change c (TensorProduct.comm R S C (1 ⊗ₜ[R] a)) = ψ a
    rw [TensorProduct.comm_tmul]
    simpa only [one_smul] using ht' a 1
  exact GradedRingHom.gradedBaseChange_of_total ψ hψ hb

/-- The affine graded-algebra data of the given quasi-coherent algebra sheaf.
All rings and restrictions are the actual section rings and section restrictions.
Degreewise base change follows from total quasi-coherent base change by direct sums. -/
noncomputable def affineData : X.GradedAlgebraData where
  obj V := A.sections V
  algebra V := A.sectionAlgebra V
  grading := A.grade
  gradedAlgebra := A.gradeRing
  res h := A.gradeRestriction h
  res_id V a := by
    change A.algebra.obj.right.obj.map (𝟙 (op V.1)) a = a
    simp
  res_res h k a := by
    exact (congrArg (fun q ↦ q a)
      (A.algebra.obj.right.obj.map_comp
        (homOfLE (X := X.Opens) k).op (homOfLE (X := X.Opens) h).op)).symm
  isGradedBaseChangeAlong h := A.gradeRestriction_baseChange h

/-- The chart grading comparisons commute with affine restriction. -/
lemma gradeIso_naturality {V W : X.affineOpens} (h : W ≤ V) :
    (A.gradeIso W).hom ≫ A.affineData.relProjFunctor.map (homOfLE h) =
      A.localTransition h ≫ (A.gradeIso V).hom := by
  dsimp only [gradeIso, localTransition, Scheme.GradedAlgebraData.relProjFunctor]
  rw [← Proj.map_comp, ← Proj.map_comp]
  apply Proj.map_congr
  exact GradedRingHom.ext fun _ ↦ rfl

/-- Identify the affine chart of `relProj` with the inverse image of its base open. -/
noncomputable def affineRestrictionIso (V : X.affineOpens) :
    Proj (A.affineData.grading V) ≅ (A.affineData.relProjHom ⁻¹ᵁ V.1).toScheme := by
  apply IsOpenImmersion.isoOfRangeEq (A.affineData.relProjι V)
    (A.affineData.relProjHom ⁻¹ᵁ V.1).ι
  rw [Scheme.Opens.range_ι]
  exact congrArg (fun U : A.affineData.relProj.Opens ↦ (U : Set A.affineData.relProj))
    (A.affineData.relProjHom_preimage V).symm

/-- The restriction identification followed by inclusion is the chart map of `relProj`. -/
lemma affineRestrictionIso_hom_ι (V : X.affineOpens) :
    (A.affineRestrictionIso V).hom ≫ (A.affineData.relProjHom ⁻¹ᵁ V.1).ι =
      A.affineData.relProjι V := by
  unfold affineRestrictionIso
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The relative Proj `relProj`, with structure map `relProjHom`, equipped with the sheaf-input
chart interface. -/
noncomputable def realization : RelativeProjData A where
  gluing := A.affineData.relProjGluingData
  localIso V := (A.gradeIso V).symm
  local_over V := by
    rw [← A.gradeIso_hom_base V]
    simp only [Iso.symm_hom, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rfl
  local_transition V W h := by
    change A.affineData.relProjFunctor.map (homOfLE h) ≫ (A.gradeIso V).inv =
      (A.gradeIso W).inv ≫ A.localTransition h
    apply (cancel_epi (A.gradeIso W).hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [A.gradeIso_naturality h]
    simp
  restrictionIso V := (A.affineRestrictionIso V).symm ≪≫ (A.gradeIso V).symm
  restriction_ι V := by
    change (A.affineRestrictionIso V).inv ≫ (A.gradeIso V).inv ≫
      (A.gradeIso V).hom ≫ A.affineData.relProjι V = _
    rw [Iso.inv_hom_id_assoc, ← A.affineRestrictionIso_hom_ι V]
    simp only [Iso.inv_hom_id_assoc]
    rfl
  restriction_over V := by
    change (A.affineRestrictionIso V).inv ≫ (A.gradeIso V).inv ≫
      A.localBase V ≫ V.1.ι = _
    rw [← A.gradeIso_hom_base V]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change (A.affineRestrictionIso V).inv ≫ A.affineData.toOpen V ≫ V.1.ι = _
    rw [← A.affineData.relProjι_relProjHom V, ← A.affineRestrictionIso_hom_ι V]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  restriction_compatibility V W h := by
    apply (cancel_epi (A.gradeIso W).inv).mp
    apply (cancel_mono (A.gradeIso V).hom).mp
    simp only [Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.inv_hom_id_assoc]
    rw [← A.gradeIso_naturality h]
    apply (cancel_mono (A.affineRestrictionIso V).hom).mp
    apply (cancel_mono (A.affineData.relProjHom ⁻¹ᵁ V.1).ι).mp
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change (A.affineRestrictionIso W).hom ≫ A.affineData.relProj.homOfLE
      (A.affineData.relProjHom.preimage_mono h) ≫ (A.affineData.relProjHom ⁻¹ᵁ V.1).ι =
      A.affineData.relProjFunctor.map (homOfLE h) ≫ (A.affineRestrictionIso V).hom ≫
        (A.affineData.relProjHom ⁻¹ᵁ V.1).ι
    rw [Scheme.homOfLE_ι, ← Category.assoc, A.affineRestrictionIso_hom_ι,
      Category.assoc, A.affineRestrictionIso_hom_ι]
    exact (A.affineData.relProjFunctor_map_relProjι (homOfLE h)).symm

end AlgebraicGeometry.RelativeProjAlgebra
