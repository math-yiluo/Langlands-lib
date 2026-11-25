/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
import WeilConjectures.AlgebraicGeometry.Affine.AffineFreeResidueSectionsCohomology
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import all WeilConjectures.AlgebraicGeometry.Residue.ResidueRankModelDifferential

/-! # Minimality of affine models at a residue point
Source: Stacks Project, Tags 0BCD and 0BF2.
(blueprint: lem-sc-affine-betti-model-residue-minimality)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

/-- A free affine model whose term ranks are its residue Betti numbers is minimal at w.
Source: Stacks Project, Tags 0BCD and 0BF2, the minimal source complex.
(blueprint: lem-sc-affine-betti-model-residue-minimality)

Proof: Apply affineFree_residueSections_cohomologyLinearEquiv to the bounded free
model to compare the homology of its termwise scalar extension to kappa(w) with
its derived residue cohomology. The termwise free presentations give finite
vector spaces of the prescribed dimensions; their subquotient homology is finite.
The cycles inclusion is injective and the homology projection is surjective.
Equality of the term and homology finranks makes the cycles inclusion surjective,
so cancellation in iCycles_d makes every differential zero over kappa(w).
For each coordinate of a free basis of the target term, the scalar-extension
adjunction now shows that its value on the original differential evaluates to
zero. Such a coordinate belongs to p, the kernel of evaluation, and its image
under the algebra map to kappa(p) is zero. Base change the target free basis,
distribute tensor over its finite coordinate product, and apply the tensor right
unitor to see the differential is zero over kappa(p). This uses no properness
or coefficient trivialization and includes zero terms and arbitrary bounds. -/
theorem affine_betti_model_residue_minimality
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (w : W)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (K.X j))
    (hrank : ∀ j : ℤ, Nonempty (K.X j ≅ SheafOfModules.free
      (R := (moduleRings W.toRingedSpace).over U)
      (ULift.{v} (Fin (derivedFiberBetti W E j w)))))
    (he : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K)) :
    let p := RingHom.ker (W.evaluation U w hwU).hom
    letI : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
    ∀ j : ℤ,
      (show (K.X j).val.obj (.op (Over.mk (𝟙 U))) →ₗ[Γ(W, U)]
          (K.X (j + 1)).val.obj (.op (Over.mk (𝟙 U))) from
            ((K.d j (j + 1)).val.app (.op (Over.mk (𝟙 U)))).hom).baseChange p.ResidueField =
        0 := by
  classical
  let p := RingHom.ker (W.evaluation U w hwU).hom
  let : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
  let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      ModuleCat.{v} Γ(W, U) := SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
  have : F.Additive := inferInstanceAs
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
  let ρ := (W.evaluation U w hwU).hom
  let T := ModuleCat.extendScalars.{v, v, v} ρ
  have : T.Additive := (ModuleCat.extendRestrictScalarsAdj ρ).left_adjoint_additive
  let C := ((F ⋙ T).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have hC := affineFree_residueSections_cohomologyLinearEquiv W E w U hwU hU K hb
    (fun j ↦ derivedFiberBetti W E j w) hrank he
  have hterms (j : ℤ) : Module.Finite (W.residueField w) (C.X j) ∧
      Module.finrank (W.residueField w) (C.X j) = derivedFiberBetti W E j w := by
    exact finite_rank_scalarExtension ρ (F.obj (K.X j)) (derivedFiberBetti W E j w)
      (SheafOfModules.sectionsLinearEquivOfIsoFree (hrank j).some
        (.op (Over.mk (𝟙 U))))
  have hhomfinite (j : ℤ) : Module.Finite (W.residueField w) (C.homology j) := by
    have : Module.Finite (W.residueField w) (C.X j) := (hterms j).1
    have hi := (ModuleCat.mono_iff_injective (C.iCycles j)).mp inferInstance
    have : Module.Finite (W.residueField w) (C.cycles j) :=
      Module.Finite.of_injective (C.iCycles j).hom hi
    exact Module.Finite.of_surjective (C.homologyπ j).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  have hzero : ∀ i j : ℤ, C.d i j = 0 := differential_zero_of_equal_dimensions C
    (fun j ↦ (hterms j).1) hhomfinite
    (fun j ↦ (hC j).some.finrank_eq.symm.trans (hterms j).2.symm)
  dsimp only
  intro j
  let e : (F.obj (K.X (j + 1))) ≃ₗ[Γ(W, U)]
      (ULift.{v} (Fin (derivedFiberBetti W E (j + 1) w)) → Γ(W, U)) :=
    SheafOfModules.sectionsLinearEquivOfIsoFree (hrank (j + 1)).some
    (.op (Over.mk (𝟙 U)))
  have hcoords (x : F.obj (K.X j)) (i : ULift.{v} (Fin (derivedFiberBetti W E (j + 1) w))) :
      ρ (e ((F.map (K.d j (j + 1))).hom x) i) = 0 := by
    let q : F.obj (K.X (j + 1)) ⟶ (ModuleCat.restrictScalars ρ).obj
        (ModuleCat.of (W.residueField w) (W.residueField w)) :=
      ModuleCat.ofHom (X := F.obj (K.X (j + 1)))
        (Y := (ModuleCat.restrictScalars ρ).obj
          (ModuleCat.of (W.residueField w) (W.residueField w)))
        { toFun := fun y ↦ ρ (e y i)
          map_add' := by intro x y; simp
          map_smul' := by
            intro r y
            change ρ (e (r • y) i) = ρ r * ρ (e y i)
            simp [map_smul, Pi.smul_apply, smul_eq_mul] }
    let a := (ModuleCat.extendRestrictScalarsAdj ρ).homEquiv _ _ |>.symm q
    have ha := ((ModuleCat.extendRestrictScalarsAdj ρ).homEquiv _ _).apply_symm_apply q
    have hz : T.map (F.map (K.d j (j + 1))) ≫ a = 0 := by
      change C.d j (j + 1) ≫ a = 0
      rw [hzero, zero_comp]
    have hq : F.map (K.d j (j + 1)) ≫ q = 0 := by
      rw [← ha, ← (ModuleCat.extendRestrictScalarsAdj ρ).homEquiv_naturality_left]
      rw [hz]
      exact (ModuleCat.extendRestrictScalarsAdj ρ).homAddEquiv_zero _ _
    exact ConcreteCategory.congr_hom hq x
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r x =>
    simp only [LinearMap.baseChange_tmul, LinearMap.zero_apply]
    apply (e.baseChange Γ(W, U) p.ResidueField).injective
    rw [LinearEquiv.baseChange_tmul, map_zero]
    apply (TensorProduct.piRight Γ(W, U) p.ResidueField p.ResidueField
      (fun _ ↦ Γ(W, U))).injective
    ext i
    simp only [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
      LinearMap.map_zero, Pi.zero_apply]
    apply (TensorProduct.rid Γ(W, U) p.ResidueField).injective
    have hc : algebraMap Γ(W, U) p.ResidueField
        (e ((F.map (K.d j (j + 1))).hom x) i) = 0 :=
      Ideal.algebraMap_residueField_eq_zero.mpr (hcoords x i)
    simp only [TensorProduct.rid_tmul, map_zero]
    dsimp only [F, SheafOfModules.evaluation, SheafOfModules.forget,
      PresheafOfModules.evaluation, Functor.comp_map] at hc
    simp only [Algebra.smul_def]
    exact mul_eq_zero.mpr (Or.inl hc)
  | add x y hx hy =>
    simp [map_add, hx, hy]

end AlgebraicGeometry.Scheme
