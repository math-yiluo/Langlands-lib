/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProjectiveSpace.RelativeProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Compactification.NagataAffineProjScalarExtension
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import WeilConjectures.AlgebraicGeometry.RelativeProj.Universal

/-! # Free projective bundles and base-change projective space

The local normalization uses the recorded polynomial equivalence for the symmetric
algebra, followed by coefficient extension from the integral polynomial ring. Equality
with `Proj.map` specifies the entire local Proj comparison, including its homogeneous
localization formulas. The two restriction equations record compatibility of both the
polynomial identifications and the local scheme maps.

## Main definitions and statement

* `integralPolynomialMap`: the prescribed map from the integral polynomial ring.
* `IsIntegralProjComparison`: equality with its canonical Proj map.
* `affineToIntegral`: the integral projection of an affine restriction.
* `existsUnique_freeProjectiveBundleBaseChangeSpace`: the normalized global isomorphism.

## References

* Stacks Project, Constructions, Tags 01NF and 01O3
* Morphisms, Tag 087S
* Stacks Project, Tags 01NF, 01O3 and 01N2
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.RelativeProjectiveSpace

/-- The integral polynomial map on an affine base: extend coefficients, fix the ordered
variables, and apply the inverse of the symmetric-algebra polynomial identification.
Thus `T_i` maps to `j_F(e_i)` and integers map by the structural unit. -/
def integralPolynomialMap (S : Scheme.{u}) (r : ℕ) (V : S.affineOpens) :
    MvPolynomial (ULift.{u} (Fin (r + 1))) (ULift.{u} ℤ) →+* (algebra S r).sections V :=
  (affinePolynomialEquiv S r V).toRingHom.comp
    (MvPolynomial.eval₂Hom
      (MvPolynomial.C.comp ((Int.castRingHom (S.presheaf.obj (op V.1))).comp
        (ULift.ringEquiv (R := ℤ)).toRingHom))
      (fun i : ULift.{u} (Fin (r + 1)) ↦ MvPolynomial.X i.down))

/-- The local map to the integral Proj specified by the coefficient extension and the
ordered symmetric generators. The irrelevant-ideal condition is an existential witness
for the prescribed map, not an extra hypothesis on the base. `Proj.map` carries exactly
the standard degree-zero homogeneous-localization formulas. -/
def IsIntegralProjComparison (S : Scheme.{u}) (r : ℕ) (V : S.affineOpens)
    (f : (algebra S r).localProj V ⟶
      Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (r + 1))) (ULift.{u} ℤ)) : Prop :=
  letI := MvPolynomial.gradedAlgebra (σ := ULift.{u} (Fin (r + 1))) (R := ULift.{u} ℤ)
  ∃ ψ : MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) (ULift.{u} ℤ)
      →+*ᵍ (algebra S r).sectionGrade V,
    ψ.toRingHom = integralPolynomialMap S r V ∧
      ∃ hψ : HomogeneousIdeal.irrelevant ((algebra S r).sectionGrade V) ≤
          (HomogeneousIdeal.irrelevant
            (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1)))
              (ULift.{u} ℤ))).map ψ,
        f = Proj.map ψ hψ

/-- Restrict a global comparison to the affine relative-Proj model and project to the
integral Proj. Together with the structural map to `V`, this determines its map to the
base-change projective space over `V` by the fibre-product universal property. -/
def affineToIntegral (S : Scheme.{u}) (r : ℕ)
    (θ : scheme S r ≅ ProjectiveSpace (ULift.{u} (Fin (r + 1))) S)
    (V : S.affineOpens) :
    (algebra S r).localProj V ⟶
      Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (r + 1))) (ULift.{u} ℤ) :=
  ((construction S r).restrictionIso V).inv ≫ (π S r ⁻¹ᵁ V.1).ι ≫ θ.hom ≫
    ProjectiveSpace.toProjInt (ULift.{u} (Fin (r + 1))) S

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem polynomial_C (S : Scheme.{u}) (r : ℕ) (V : S.affineOpens)
    (a : Γ(S, V.1)) :
    affinePolynomialEquiv S r V (MvPolynomial.C a) =
      (algebra S r).algebra.obj.hom.hom.app (op V.1) a :=
  (existsUnique_affinePolynomialEquiv S r V).exists.choose_spec.1 a

private theorem polynomial_X (S : Scheme.{u}) (r : ℕ) (V : S.affineOpens)
    (i : Fin (r + 1)) :
    affinePolynomialEquiv S r V (MvPolynomial.X i) = coordinate S r V i :=
  (existsUnique_affinePolynomialEquiv S r V).exists.choose_spec.2 i

private def polynomialAlgEquiv (S : Scheme.{u}) (r : ℕ) (V : S.affineOpens) :
    MvPolynomial (ULift.{u} (Fin (r + 1))) Γ(S, V.1) ≃ₐ[Γ(S, V.1)]
      (algebra S r).sections V :=
  (MvPolynomial.renameEquiv Γ(S, V.1) Equiv.ulift).trans
    { (affinePolynomialEquiv S r V) with commutes' := polynomial_C S r V }

private theorem polynomialAlgEquiv_mem (S : Scheme.{u}) (r : ℕ) (V : S.affineOpens)
    (n : ℕ) (p : MvPolynomial (ULift.{u} (Fin (r + 1))) Γ(S, V.1)) :
    polynomialAlgEquiv S r V p ∈ (algebra S r).grade V n ↔
      p ∈ MvPolynomial.homogeneousSubmodule _ _ n := by
  change affinePolynomialEquiv S r V (MvPolynomial.rename ULift.down p) ∈
    (algebra S r).sectionGrade V n ↔ _
  rw [affinePolynomial_homogeneous]
  exact MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff Equiv.ulift.injective

private def integralGradedMap (S : Scheme.{u}) (r : ℕ) (V : S.affineOpens) :
    MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) (ULift.{u} ℤ)
      →+*ᵍ (algebra S r).sectionGrade V :=
  { integralPolynomialMap S r V with
    map_mem := by
      intro n p hp
      apply (affinePolynomial_homogeneous S r V n _).mpr
      simpa only [one_mul, MvPolynomial.mem_homogeneousSubmodule,
        MvPolynomial.coe_eval₂Hom] using hp.eval₂
        (MvPolynomial.C.comp ((Int.castRingHom Γ(S, V.1)).comp
          (ULift.ringEquiv (R := ℤ)).toRingHom)) _
        (fun a ↦ MvPolynomial.isHomogeneous_C _ _) (fun i ↦
          MvPolynomial.isHomogeneous_X Γ(S, V.1) i.down) }

private theorem homogeneous_coefficient_span
    {σ R T : Type u} [CommRing R] [CommRing T] (f : R →+* T) (n : ℕ) :
    MvPolynomial.homogeneousSubmodule σ T n =
      Submodule.span T (MvPolynomial.map f ''
        (MvPolynomial.homogeneousSubmodule σ R n : Set (MvPolynomial σ R))) := by
  classical
  apply le_antisymm
  · rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
      AddMonoidAlgebra.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨d, hd, rfl⟩
    apply Submodule.subset_span
    refine ⟨MvPolynomial.monomial d 1, MvPolynomial.isHomogeneous_monomial 1 hd, ?_⟩
    simp only [MvPolynomial.map_monomial, map_one, MvPolynomial.single_eq_monomial]
  · rw [Submodule.span_le]
    rintro _ ⟨p, hp, rfl⟩
    exact hp.map f

private theorem integral_apply (S : Scheme.{u}) (r : ℕ) (V : S.affineOpens)
    (p : MvPolynomial (ULift.{u} (Fin (r + 1))) (ULift.{u} ℤ)) :
    polynomialAlgEquiv S r V
      (MvPolynomial.map ((Int.castRingHom Γ(S, V.1)).comp
        (ULift.ringEquiv (R := ℤ)).toRingHom) p) = integralGradedMap S r V p := by
  let f : ULift.{u} ℤ →+* Γ(S, V.1) :=
    (Int.castRingHom _).comp ULift.ringEquiv.toRingHom
  have he : (MvPolynomial.rename (R := Γ(S, V.1))
      (ULift.down : ULift.{u} (Fin (r + 1)) → Fin (r + 1))).toRingHom.comp
      (MvPolynomial.map f) =
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp f) (fun i ↦ MvPolynomial.X i.down) := by
    apply MvPolynomial.ringHom_ext <;> intro a <;> simp
  exact DFunLike.congr_fun (congrArg
    (fun q ↦ (affinePolynomialEquiv S r V).toRingHom.comp q) he) p

private theorem integral_span (S : Scheme.{u}) (r : ℕ) (V : S.affineOpens)
    (n : ℕ) :
    (algebra S r).grade V n = Submodule.span Γ(S, V.1)
      (integralGradedMap S r V ''
        (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) (ULift.{u} ℤ) n :
          Set (MvPolynomial (ULift.{u} (Fin (r + 1))) (ULift.{u} ℤ)))) := by
  let f : ULift.{u} ℤ →+* Γ(S, V.1) :=
    (Int.castRingHom _).comp ULift.ringEquiv.toRingHom
  have he : (algebra S r).grade V n =
      (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1) n).map
        (polynomialAlgEquiv S r V).toLinearMap := by
    ext x
    constructor
    · intro hx
      refine ⟨(polynomialAlgEquiv S r V).symm x, ?_, by simp⟩
      exact (polynomialAlgEquiv_mem S r V n _).mp (by simpa)
    · rintro ⟨p, hp, rfl⟩
      exact (polynomialAlgEquiv_mem S r V n p).mpr hp
  rw [he, homogeneous_coefficient_span f, Submodule.map_span]
  congr 1
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, (integral_apply S r V p).symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨_, ⟨p, hp, rfl⟩, integral_apply S r V p⟩

private theorem integral_irrelevant (S : Scheme.{u}) (r : ℕ) (V : S.affineOpens) :
    HomogeneousIdeal.irrelevant ((algebra S r).sectionGrade V) ≤
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1)))
          (ULift.{u} ℤ))).map (integralGradedMap S r V) := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro n hn b hb
  change b ∈ (algebra S r).grade V n at hb
  rw [integral_span S r V n] at hb
  induction hb using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ hn ha)
  | zero => exact Ideal.zero_mem _
  | add x y hx hy hx' hy' => exact Ideal.add_mem _ hx' hy'
  | smul s x hx hx' =>
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ hx'

private def integralMap (S : Scheme.{u}) (r : ℕ) (V : S.affineOpens) :
    (algebra S r).localProj V ⟶
      Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (r + 1))) (ULift.{u} ℤ) :=
  Proj.map (integralGradedMap S r V) (integral_irrelevant S r V)

private theorem integral_pullback (S : Scheme.{u}) (r : ℕ) (V : S.affineOpens) :
    IsPullback (integralMap S r V) ((algebra S r).localBase V)
      (terminal.from _) (terminal.from _) := by
  let : Algebra (ULift.{u} ℤ) Γ(S, V.1) := ULift.algebra' ℤ Γ(S, V.1)
  -- Scalar extension is applied with the equivalent submodule grading.
  let β := (MvPolynomial.algebraTensorAlgEquiv (σ := ULift.{u} (Fin (r + 1)))
    (ULift.{u} ℤ) Γ(S, V.1)).trans (polynomialAlgEquiv S r V)
  let ψ : MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) (ULift.{u} ℤ)
      →+*ᵍ (algebra S r).grade V :=
    { integralGradedMap S r V with map_mem := fun hp ↦ (integralGradedMap S r V).map_mem hp }
  have hβ (a : MvPolynomial (ULift.{u} (Fin (r + 1))) (ULift.{u} ℤ)) :
      β (TensorProduct.tmul (ULift.{u} ℤ) (1 : Γ(S, V.1)) a) = ψ a := by
    dsimp only [β, AlgEquiv.trans_apply]
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
    exact integral_apply S r V a
  obtain ⟨f, hf, -, -, -, hu⟩ := lem_nagata_affine_proj_scalar_extension
    (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) (ULift.{u} ℤ))
    ((algebra S r).grade V)
    (MvPolynomial.homogeneousSubmoduleZeroEquiv _ _).toRingHom
    (algebraMap Γ(S, V.1) ((algebra S r).grade V 0))
    (fun _ ↦ rfl) (fun _ ↦ rfl) β ψ hβ (integral_span S r V)
  have hψ : HomogeneousIdeal.irrelevant ((algebra S r).grade V) ≤
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1)))
          (ULift.{u} ℤ))).map ψ := by
    apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
    intro n hn b hb
    rw [integral_span S r V n] at hb
    induction hb using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        exact Ideal.mem_map_of_mem ψ (HomogeneousIdeal.mem_irrelevant_of_mem _ hn ha)
    | zero => exact Ideal.zero_mem _
    | add x y hx hy hx' hy' => exact Ideal.add_mem _ hx' hy'
    | smul s x hx hx' =>
        rw [Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ hx'
  -- The chart formulas identify the supplied comparison with the prescribed Proj map.
  have hfp : Proj.map ψ hψ = f := hu _
    (fun _ _ _ _ ↦ Proj.map_preimage_basicOpen ψ hψ _)
    (fun _ _ hp hn ↦ Proj.awayι_comp_map ψ hψ hn _ hp)
  rw [← hfp] at hf
  have hc : ((algebra S r).gradeIso V).inv ≫ integralMap S r V = Proj.map ψ hψ := by
    dsimp only [RelativeProjAlgebra.gradeIso, integralMap]
    rw [← Proj.map_comp]
    apply Proj.map_congr
    exact GradedRingHom.ext fun _ ↦ rfl
  let e := specULiftZIsTerminal.uniqueUpToIso (terminalIsTerminal (C := Scheme.{u}))
  apply hf.of_iso ((algebra S r).gradeIso V).symm (Iso.refl _)
    V.2.isoSpec.symm e
  · simpa only [Iso.refl_hom, Category.comp_id, Iso.symm_hom] using hc.symm
  · change Proj.toSpecOfAlgebra ((algebra S r).grade V) ≫ V.2.isoSpec.inv = _
    exact ((cancel_epi ((algebra S r).gradeIso V).hom).mp (by
      simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using
        (algebra S r).gradeIso_hom_base V))
  · exact terminalIsTerminal.hom_ext _ _
  · exact terminalIsTerminal.hom_ext _ _

private theorem coordinate_restrict (S : Scheme.{u}) (r : ℕ)
    {V W : S.affineOpens} (h : W ≤ V) (i : Fin (r + 1)) :
    (algebra S r).restriction h (coordinate S r V i) = coordinate S r W i := by
  have hg := PresheafOfModules.naturality_apply
    ((SheafOfModules.ιFree (R := S.ringCatSheaf) (ULift.up i)) ≫
      SymmetricAlgebraSheaf.inclusion (freeModule S r)).val
    (homOfLE (X := S.Opens) h).op (1 : S.ringCatSheaf.obj.obj (op V.1))
  have hunit : (SheafOfModules.unit S.ringCatSheaf).val.map
      (homOfLE (X := S.Opens) h).op (1 : S.ringCatSheaf.obj.obj (op V.1)) =
      (1 : S.ringCatSheaf.obj.obj (op W.1)) :=
    (S.ringCatSheaf.obj.map (homOfLE (X := S.Opens) h).op).hom.map_one
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply, hunit] at hg
  change generator S r W.1 i =
    (SymmetricAlgebraSheaf.algebra (freeModule S r)).right.obj.map
      (homOfLE (X := S.Opens) h).op (generator S r V.1 i) at hg
  let t := (eqToHom (algebra_eq S r).symm).right.hom
  have ht := CategoryTheory.congr_fun (t.naturality (homOfLE (X := S.Opens) h).op)
    (generator S r V.1 i)
  change t.app (op W.1)
      ((SymmetricAlgebraSheaf.algebra (freeModule S r)).right.obj.map
        (homOfLE (X := S.Opens) h).op (generator S r V.1 i)) =
    (algebra S r).restriction h (coordinate S r V i) at ht
  rw [← hg] at ht
  exact ht.symm

private theorem polynomial_restrict (S : Scheme.{u}) (r : ℕ)
    {V W : S.affineOpens} (h : W ≤ V)
    (p : MvPolynomial (Fin (r + 1)) Γ(S, V.1)) :
    (algebra S r).restriction h (affinePolynomialEquiv S r V p) =
      affinePolynomialEquiv S r W
        (MvPolynomial.map (S.presheaf.map (homOfLE (X := S.Opens) h).op).hom p) := by
  have he : ((algebra S r).restriction h).toRingHom.comp
        (affinePolynomialEquiv S r V).toRingHom =
      (affinePolynomialEquiv S r W).toRingHom.comp
        (MvPolynomial.map (S.presheaf.map (homOfLE (X := S.Opens) h).op).hom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.map_C, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, polynomial_C]
      exact (CategoryTheory.congr_fun
        ((algebra S r).algebra.obj.hom.hom.naturality
          (homOfLE (X := S.Opens) h).op) a).symm
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.map_X, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, polynomial_X]
      exact coordinate_restrict S r h i
  exact DFunLike.congr_fun he p

private theorem integralGradedMap_restrict (S : Scheme.{u}) (r : ℕ)
    {V W : S.affineOpens} (h : W ≤ V) :
    ((algebra S r).restriction h).comp (integralGradedMap S r V) =
      integralGradedMap S r W := by
  have he : ((algebra S r).restriction h).toRingHom.comp
      (integralGradedMap S r V).toRingHom = (integralGradedMap S r W).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      dsimp only [integralGradedMap, integralPolynomialMap]
      simp only [RingHom.comp_apply, GradedRingHom.coe_toRingHom,
        MvPolynomial.eval₂Hom_C, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [polynomial_restrict, MvPolynomial.map_C]
      congr 2
      rcases a with ⟨a⟩
      change (S.presheaf.map (homOfLE (X := S.Opens) h).op).hom (a : Γ(S, V.1)) =
        (a : Γ(S, W.1))
      exact map_intCast _ a
    · intro i
      dsimp only [integralGradedMap, integralPolynomialMap]
      simp only [RingHom.comp_apply, GradedRingHom.coe_toRingHom,
        MvPolynomial.eval₂Hom_X', RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [polynomial_restrict, MvPolynomial.map_X]
  apply GradedRingHom.ext
  intro p
  exact DFunLike.congr_fun he p

private theorem integralMap_restrict (S : Scheme.{u}) (r : ℕ)
    {V W : S.affineOpens} (h : W ≤ V) :
    (algebra S r).localTransition h ≫ integralMap S r V = integralMap S r W := by
  dsimp only [RelativeProjAlgebra.localTransition, integralMap]
  rw [← Proj.map_comp]
  apply Proj.map_congr
  exact integralGradedMap_restrict S r h

private def comparisonChart (S : Scheme.{u}) (r : ℕ) (V : S.affineOpens) :
    Proj ((algebra S r).affineData.grading V) ⟶
      ProjectiveSpace (ULift.{u} (Fin (r + 1))) S :=
  pullback.lift ((algebra S r).affineData.toOpen V ≫ V.1.ι)
    (((algebra S r).gradeIso V).inv ≫ integralMap S r V)
    (terminalIsTerminal.hom_ext _ _)

private theorem comparisonChart_pullback (S : Scheme.{u}) (r : ℕ) (V : S.affineOpens) :
    IsPullback ((algebra S r).affineData.toOpen V) (comparisonChart S r V) V.1.ι
      (ProjectiveSpace (ULift.{u} (Fin (r + 1))) S ↘ S) := by
  have hf : IsPullback
      (((algebra S r).gradeIso V).inv ≫ integralMap S r V)
      ((algebra S r).affineData.toOpen V) (terminal.from _) (terminal.from _) := by
    apply (integral_pullback S r V).of_iso ((algebra S r).gradeIso V)
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
    · simp only [Iso.refl_hom, Category.comp_id]
      change (algebra S r).localBase V = ((algebra S r).gradeIso V).hom ≫
        Proj.toSpecOfAlgebra ((algebra S r).grade V) ≫ V.2.isoSpec.inv
      exact ((algebra S r).gradeIso_hom_base V).symm
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  have hf' : IsPullback ((algebra S r).affineData.toOpen V)
      (((algebra S r).gradeIso V).inv ≫ integralMap S r V)
      (V.1.ι ≫ terminal.from S) (terminal.from _) := by
    simpa only [terminal.comp_from] using hf.flip
  have hp := IsPullback.of_bot' hf'
    (ProjectiveSpace.isPullback_over_toProjInt (ULift.{u} (Fin (r + 1))) S)
  convert hp using 1
  apply ProjectiveSpace.hom_ext
  · change comparisonChart S r V ≫ pullback.fst _ _ = _
    simp only [comparisonChart, pullback.lift_fst, IsPullback.lift_fst]
  · simp only [comparisonChart, IsPullback.lift_snd,
      ProjectiveSpace.toProjInt, pullback.lift_snd]

private theorem comparisonChart_restrict (S : Scheme.{u}) (r : ℕ)
    {V W : S.affineOpens} (h : W ≤ V) :
    (algebra S r).affineData.relProjFunctor.map (homOfLE h) ≫ comparisonChart S r V =
      comparisonChart S r W := by
  apply ProjectiveSpace.hom_ext
  · change _ ≫ (comparisonChart S r V ≫ pullback.fst _ _) =
      comparisonChart S r W ≫ pullback.fst _ _
    dsimp only [comparisonChart]
    rw [pullback.lift_fst, pullback.lift_fst]
    have hw := ((algebra S r).affineData.isPullback_relProjFunctor_map h).w
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f ↦ f ≫ V.1.ι) hw).trans (by
        rw [Category.assoc, Scheme.homOfLE_ι]))
  · simp only [comparisonChart, Category.assoc, ProjectiveSpace.toProjInt,
      pullback.lift_snd]
    rw [← Category.assoc]
    have hn := (algebra S r).gradeIso_naturality h
    have hn' : (algebra S r).affineData.relProjFunctor.map (homOfLE h) ≫
        ((algebra S r).gradeIso V).inv =
        ((algebra S r).gradeIso W).inv ≫ (algebra S r).localTransition h := by
      apply (cancel_epi ((algebra S r).gradeIso W).hom).mp
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rw [hn]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hn', Category.assoc, integralMap_restrict]

private theorem local_comparison_eq (S : Scheme.{u}) (r : ℕ)
    (θ : scheme S r ≅ ProjectiveSpace (ULift.{u} (Fin (r + 1))) S)
    (V : S.affineOpens) :
    affineToIntegral S r θ V = ((algebra S r).gradeIso V).hom ≫
      (algebra S r).affineData.relProjι V ≫ θ.hom ≫
      ProjectiveSpace.toProjInt (ULift.{u} (Fin (r + 1))) S := by
  unfold affineToIntegral
  dsimp only [π, RelativeProjData.π]
  rw [← (construction S r).restriction_ι V]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- The symmetric-algebra relative projective space is canonically the base change of
integral projective space. On every affine open it is the Proj map of the standard
symmetric-algebra polynomial equivalence, compatibly with base restriction. -/
theorem existsUnique_freeProjectiveBundleBaseChangeSpace (S : Scheme.{u}) (r : ℕ) :
    ∃! θ : scheme S r ≅ ProjectiveSpace (ULift.{u} (Fin (r + 1))) S,
      (θ.hom ≫ ProjectiveSpace (ULift.{u} (Fin (r + 1))) S ↘ S = π S r) ∧
      (∀ V : S.affineOpens, IsIntegralProjComparison S r V (affineToIntegral S r θ V)) ∧
      (∀ (V W : S.affineOpens) (h : W ≤ V),
        (algebra S r).localTransition h ≫ affineToIntegral S r θ V =
          affineToIntegral S r θ W) ∧
      (∀ (V W : S.affineOpens) (h : W ≤ V)
          (p : MvPolynomial (Fin (r + 1)) (S.presheaf.obj (op V.1))),
        (algebra S r).restriction h (affinePolynomialEquiv S r V p) =
          affinePolynomialEquiv S r W
            (MvPolynomial.map (S.presheaf.map (homOfLE (X := S.Opens) h).op).hom p)) := by
  let A := (algebra S r).affineData
  -- Compatible cartesian affine charts determine the global relative Proj.
  let θ : scheme S r ≅ ProjectiveSpace (ULift.{u} (Fin (r + 1))) S :=
    A.relProjIsoOfIsPullback _ (comparisonChart S r) (comparisonChart_pullback S r)
      (fun h ↦ comparisonChart_restrict S r h)
  have ho : θ.hom ≫ ProjectiveSpace (ULift.{u} (Fin (r + 1))) S ↘ S = π S r :=
    A.relProjIsoOfIsPullback_hom_comp _ _ _ _
  have hl (V : S.affineOpens) : affineToIntegral S r θ V = integralMap S r V := by
    rw [local_comparison_eq]
    have ht : A.relProjι V ≫ θ.hom = comparisonChart S r V :=
      A.relProjι_relProjIsoOfIsPullback_hom _ _ _ _ V
    have ht' := congrArg (fun f ↦ ((algebra S r).gradeIso V).hom ≫ f ≫
      ProjectiveSpace.toProjInt (ULift.{u} (Fin (r + 1))) S) ht
    simp only [Category.assoc] at ht'
    refine ht'.trans ?_
    simp only [comparisonChart, ProjectiveSpace.toProjInt, pullback.lift_snd,
      Iso.hom_inv_id_assoc]
  refine ⟨θ, ⟨ho, ?_, ?_, ?_⟩, ?_⟩
  · intro V
    rw [hl]
    exact ⟨integralGradedMap S r V, rfl, integral_irrelevant S r V, rfl⟩
  · intro V W h
    rw [hl, hl]
    exact integralMap_restrict S r h
  · intro V W h p
    exact polynomial_restrict S r h p
  · intro θ' hθ'
    apply Iso.ext
    apply ProjectiveSpace.hom_ext
    · exact hθ'.1.trans ho.symm
    · refine colimit.hom_ext (F := A.relProjFunctor) (fun V ↦ ?_)
      apply (cancel_epi ((algebra S r).gradeIso V).hom).mp
      change ((algebra S r).gradeIso V).hom ≫ A.relProjι V ≫ θ'.hom ≫ _ =
        ((algebra S r).gradeIso V).hom ≫ A.relProjι V ≫ θ.hom ≫ _
      rw [← local_comparison_eq, ← local_comparison_eq, hl]
      obtain ⟨ψ, hψ, hi, he⟩ := hθ'.2.1 V
      rw [he]
      apply Proj.map_congr
      apply GradedRingHom.ext
      intro p
      exact DFunLike.congr_fun hψ p

end AlgebraicGeometry.RelativeProjectiveSpace
