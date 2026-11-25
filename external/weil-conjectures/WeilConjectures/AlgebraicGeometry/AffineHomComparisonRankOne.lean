/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineHomComparisonGeneratorExtension
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree

/-! # Rank-one affine Hom comparison

Source: Stacks Project, Tag 01HV (4)-(5), and Tag 0BQZ.
(blueprint: lem-sc-k4-affine-hom-comparison-rankone). -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

private noncomputable def rankOneModuleEvalIso {A : Type u} [CommRing A]
    (N : ModuleCat.{u} A) : ModuleCat.of A (ModuleCat.of A A ⟶ N) ≅ N :=
  (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf A A N)).toModuleIso

private theorem section_eval {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    {R : Sheaf J CommRingCat.{u}}
    {N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (h : SheafOfModules.unit _ ⟶ N) :
    affineHomSection _ N h ≫ (SheafOfModules.homObjUnitIso (R := R) N).hom = h := by
  apply N.unitHomEquiv.injective
  rw [SheafOfModules.unitHomEquiv_comp_apply]
  simp only [affineHomSection, Equiv.apply_symm_apply]
  rfl

/-- Generator normalization implies this affine comparison property.
Source: Stacks Project, Tag 01HV (4)-(5).
(blueprint: lem-sc-k4-affine-hom-comparison-rankone).

Proof: Evaluation at one identifies Hom_A(A,N) with N via
ModuleCat.homLinearEquiv and LinearMap.ringLmapEquivSelf. Identify T(A) with
the structure sheaf using tildeSelf and restrictUnitIso, and apply
SheafOfModules.homObjUnitIso to identify internalHom(T(A),T(N)) with T(N).
Precompose the comparison followed by this identification with the generator
h. Normalization, functoriality of internal-Hom sections, and evaluation at
one identify the result with the image of h(1). A-linear maps out of A are
determined by their value at one, so h is the element map for h(1).
Generator detection therefore equates the comparison followed by evaluation
with T of the module evaluation isomorphism. Both evaluation maps are
isomorphisms, hence so is the comparison. The same proof includes the zero
ring and zero coefficient module. -/
theorem affineHomComparison_chart_rankone {Y : Scheme.{u}} (U : Y.affineOpens) :
    ∀ N : ModuleCat.{u} Γ(Y, U.1),
      IsIso (affineHomComparison U (ModuleCat.of Γ(Y, U.1) Γ(Y, U.1)) N) := by
  intro N
  let A := (Γ(Y, U.1) : Type u)
  let T := affineHomComparisonFunctor U
  let e := affineHomComparisonUnitIso U
  let d := ((SheafOfModules.homFunctor U.1.toScheme.toRingedSpace.sheaf).flip.obj
    (T.obj N)).mapIso e.symm.op ≪≫
    SheafOfModules.homObjUnitIso (R := U.1.toScheme.toRingedSpace.sheaf) (T.obj N)
  have hd : affineHomComparison U (ModuleCat.of A A) N ≫ d.hom =
      T.map (rankOneModuleEvalIso N).hom := by
    apply affineHomGenerator_ext U (ModuleCat.of A (ModuleCat.of A A ⟶ N))
    intro h
    rw [← Category.assoc, affineHomComparison_generator]
    change affineHomSection (R := U.1.toScheme.toRingedSpace.sheaf)
      (T.obj (ModuleCat.of A A)) (T.obj N) (T.map h) ≫
      (SheafOfModules.homObjMap (R := U.1.toScheme.toRingedSpace.sheaf)
        (M := T.obj (ModuleCat.of A A)) (M' := SheafOfModules.unit U.1.toScheme.ringCatSheaf)
        (N := T.obj N) (N' := T.obj N) e.inv
        (𝟙 (T.obj N)) ≫
        (SheafOfModules.homObjUnitIso (R := U.1.toScheme.toRingedSpace.sheaf)
          (T.obj N)).hom) = _
    rw [← Category.assoc, affineHomSection_comp
      (R := U.1.toScheme.toRingedSpace.sheaf) (T.map h) e.inv (𝟙 (T.obj N))]
    rw [Category.comp_id, section_eval (R := U.1.toScheme.toRingedSpace.sheaf)
      (e.inv ≫ T.map h), affineHomGenerator_map]
    dsimp only [affineHomGenerator, comparisonGenerator]
    congr 1
    have hh : h = affineHomElement N (h.hom 1) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext_ring
      change h.hom 1 = (1 : A) • h.hom 1
      exact (one_smul A (h.hom 1)).symm
    exact congrArg T.map hh
  have : IsIso (affineHomComparison U (ModuleCat.of A A) N ≫ d.hom) := by
    rw [hd]
    infer_instance
  exact (isIso_comp_right_iff (affineHomComparison U (ModuleCat.of A A) N) d.hom).mp
    inferInstance

end AlgebraicGeometry
