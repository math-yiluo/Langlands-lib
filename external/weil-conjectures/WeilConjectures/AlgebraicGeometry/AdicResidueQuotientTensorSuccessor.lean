/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueQuotientTensorTower
public import WeilConjectures.CategoryTheory.RingedScalarTensorComparison
import all WeilConjectures.AlgebraicGeometry.AdicNormalizedScalarComposition
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import WeilConjectures.CategoryTheory.RingedScalarTensorSections
import all WeilConjectures.CategoryTheory.RingedScalarTensorUnit

/-! # One successor square for the explicit scalar tensor comparison

Source: Stacks Project, Tags 03CZ, 06YY and 099M.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.standard

attribute [local irreducible] completed derivedExtension
variable (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
  (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)

/-- The explicit level comparison: ordinary contraction, exact restriction, and
inverse of the universal K-flat scalar comparison. No isomorphism is postulated. -/
def adicResidueQuotientTensorLevelIso
    (P : Cx ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U))
    (hP : P.IsKFlatTensor) (M : AdicResidueLocalDerived.{u, v} X J U)
    (eP : (Q _).obj P ≅ M) (n : ℕ) :
    (Q _).obj ((adicResidueQuotientTensorTower X J U P).obj (op n)) ≅
      (adicResidueAdjointTower.{u, v} X J U M).obj (op n) := by
  let f := adicResidueLocalProjection.{u, v} X J U n
  have : IsIso ((extendComparison f).app P) := (derivedExtension f).computation P hP
  exact (Q _).mapIso (scalarTensorComplexIso f P) ≪≫
    (resFactors f).app (((change f).mapHomologicalComplex (.up ℤ)).obj P) ≪≫
    (dres f).mapIso (asIso ((extendComparison f).app P)).symm ≪≫
    (dres f).mapIso ((extend f).mapIso eP)

section Proofs

attribute [local implicit_reducible] SheafOfModules.restrictScalars change
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj
  ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'
  extend extendComparison
  SheafOfModules.unit PresheafOfModules.unit CategoryTheory.sheafCompose

private theorem scalar_inverse_pure
    {C : Type v} [SmallCategory C] {T : GrothendieckTopology C}
    {R S : Sheaf T CommRingCat.{v}} (f : R ⟶ S) (P : Cx R)
    (q : ℤ) (V : Cᵒᵖ) (s : S.obj.obj V) (x : (P.X q).val.obj V) :
    let := SheafOfModules.monoidalCategory R
    let := SheafOfModules.symmetricCategory R
    let := Classical.choice (SheafOfModules.tensorClosed R).1
    let := Classical.choice (SheafOfModules.tensorClosed R).2.1
    ((scalarTensorComplexIso f P).inv.f q).val.app V (tensorSection f (P.X q) V s x) =
      ((CochainComplex.mapBifunctorSingle₂Iso (MonoidalCategory.curriedTensor (Mod R))
        (scalarTensorModule f) P).inv.f q).val.app V
        (CochainPullback.moduleTmul (R := R) (P.X q) (scalarTensorModule f) V x s) := by
  dsimp only
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := Classical.choice (SheafOfModules.tensorClosed R).1
  let := Classical.choice (SheafOfModules.tensorClosed R).2.1
  have hi := congrArg
    (fun z ↦ z.val.app V
      (CochainPullback.moduleTmul (R := R) (P.X q) (scalarTensorModule f) V x s))
    (scalarTensorModuleIso f (P.X q)).hom_inv_id
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] at hi
  rw [scalarTensorModuleIso_pure] at hi
  change ((CochainComplex.mapBifunctorSingle₂Iso (MonoidalCategory.curriedTensor (Mod R))
      (scalarTensorModule f) P).inv.f q).val.app V
      ((scalarTensorModuleIso f (P.X q)).inv.val.app V
        (tensorSection f (P.X q) V s x)) = _
  rw [hi]

private theorem tensor_transition_scalar
    {C : Type v} [SmallCategory C] {T : GrothendieckTopology C}
    {R S V : Sheaf T CommRingCat.{v}} (f : R ⟶ S) (g : S ⟶ V) (h : R ⟶ V)
    (eh : f ≫ g = h) (P : Cx R) (a : scalarTensorModule f ⟶ scalarTensorModule h)
    (ha : ∀ W (s : S.obj.obj W), a.val.app W s = g.hom.app W s) :
    (((ringedKoszulTensor R).obj P).map
        ((HomologicalComplex.single _ (.up ℤ) 0).map a)) ≫ (scalarTensorComplexIso h P).hom =
      (scalarTensorComplexIso f P).hom ≫
        (NatTrans.mapHomologicalComplex (scalarTransition f g h eh) (.up ℤ)).app P := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := Classical.choice (SheafOfModules.tensorClosed R).1
  let := Classical.choice (SheafOfModules.tensorClosed R).2.1
  apply (cancel_epi (scalarTensorComplexIso f P).inv).mp
  apply (cancel_mono (scalarTensorComplexIso h P).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  apply HomologicalComplex.hom_ext
  intro q
  apply restrictedTensor_hom_ext f (P.X q)
  intro W s x
  change ((((ringedKoszulTensor R).obj P).map
      ((HomologicalComplex.single _ (.up ℤ) 0).map a)).f q).val.app W
      (((scalarTensorComplexIso f P).inv.f q).val.app W (tensorSection f (P.X q) W s x)) =
    ((scalarTensorComplexIso h P).inv.f q).val.app W
      (((scalarTransition f g h eh).app (P.X q)).val.app W
        (tensorSection f (P.X q) W s x))
  rw [scalarTransition_tmul, scalar_inverse_pure, scalar_inverse_pure]
  change (((CochainComplex.mapBifunctorSingle₂Iso
      (MonoidalCategory.curriedTensor (Mod R)) (scalarTensorModule f) P).inv.f q) ≫
      (((ringedKoszulTensor R).obj P).map
        ((HomologicalComplex.single _ (.up ℤ) 0).map a)).f q).val.app W
      (CochainPullback.moduleTmul (R := R) (P.X q) (scalarTensorModule f) W x s) = _
  rw [single_second]
  change ((CochainComplex.mapBifunctorSingle₂Iso
      (MonoidalCategory.curriedTensor (Mod R)) (scalarTensorModule h) P).inv.f q).val.app W
      ((MonoidalCategory.whiskerLeft (P.X q) a).val.app W
        (CochainPullback.moduleTmul (R := R) (P.X q) (scalarTensorModule f) W x s)) = _
  congr 1
  rw [← MonoidalCategory.id_tensorHom]
  have hm := CochainPullback.moduleTmul_map (R := R) (𝟙 (P.X q)) a W x s
  simp only [SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply, ha] at hm
  exact hm

attribute [local irreducible] ringedKoszulTensor

private theorem ordinary_tensor_successor
    (P : Cx ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U))
    (n : ℕ) :
    (adicResidueQuotientTensorTower X J U P).map (homOfLE n.le_succ).op ≫
        (scalarTensorComplexIso (adicResidueLocalProjection.{u, v} X J U n) P).hom =
      (scalarTensorComplexIso (adicResidueLocalProjection.{u, v} X J U (n + 1)) P).hom ≫
        (NatTrans.mapHomologicalComplex
          (scalarTransition (adicResidueLocalProjection.{u, v} X J U (n + 1))
            (((coefficientProEtaleModelTopology.{u, v} X).overPullback CommRingCat U).map
              (transition (coefficientProEtaleModelTopology.{u, v} X) A J n))
            (adicResidueLocalProjection.{u, v} X J U n)
            (adicResidueQuotientProjection_step X J U n)) (.up ℤ)).app P := by
  let f := adicResidueLocalProjection.{u, v} X J U (n + 1)
  let h := adicResidueLocalProjection.{u, v} X J U n
  let g := ((coefficientProEtaleModelTopology.{u, v} X).overPullback CommRingCat U).map
    (transition (coefficientProEtaleModelTopology.{u, v} X) A J n)
  have ho := tensor_transition_scalar f g h (adicResidueQuotientProjection_step X J U n)
    P (adicResidueQuotientModuleStep X J U n) (by intros; rfl)
  dsimp only [adicResidueQuotientTensorTower, CategoryTheory.Functor.comp_map,
    adicResidueQuotientCoefficientTower]
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  exact ho

end Proofs

attribute [local irreducible] ringedKoszulTensor

/-- The explicit level comparisons commute with one actual quotient successor.
This is an equality of specified maps; it asserts no existence of a tower isomorphism
and contains no unit assertion.

Source: Stacks Project, Cohomology on Sites, Tag 06YY, derived scalar extension;
proetale.tex, Tag 099M (lemma-naive-completion), the quotient coefficient transitions.
(auxiliary; not a blueprint node).

Proof: on ordinary pure tensors the quotient successor replaces s by its image.
Factor this scalar transition as insertion of one, restriction composition and
ordinary balancing. The normalized units identify the derived Hom equivalence
on K-flat complexes with its ordinary counterpart followed by resFactors.
Applying this twice, using preservation of K-flatness and the factorization
formula for exact restriction composition, identifies the specified derived
balancing with uniqueness of left adjoints. The triangle identity then computes
the transpose of the reduced preceding counit as derived insertion, restriction
composition and balancing. The K-flat comparison formulas identify this composite
with localization of the ordinary scalar transition. Finally naturality transports
the equality along eP, and the pure-tensor successor square gives the result. -/
theorem adicResidueQuotientTensorLevelIso_successor
    (P : Cx ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U))
    (hP : P.IsKFlatTensor) (M : AdicResidueLocalDerived.{u, v} X J U)
    (eP : (Q _).obj P ≅ M) (n : ℕ) :
    (Q _).map ((adicResidueQuotientTensorTower X J U P).map
        (homOfLE (Nat.le_succ n)).op) ≫
      (adicResidueQuotientTensorLevelIso X J U P hP M eP n).hom =
    (adicResidueQuotientTensorLevelIso X J U P hP M eP (n + 1)).hom ≫
      adicResidueAdjointStep.{u, v} X J U M n := by
  let f := adicResidueLocalProjection.{u, v} X J U (n + 1)
  let g := ((coefficientProEtaleModelTopology.{u, v} X).overPullback CommRingCat U).map
    (transition (coefficientProEtaleModelTopology.{u, v} X) A J n)
  let h := adicResidueLocalProjection.{u, v} X J U n
  let eh : h = f ≫ g := (adicResidueQuotientProjection_step X J U n).symm
  let af : extend f ⊣ dres f := adicResidueScalarAdjunction.{u, v} X J U (n + 1)
  let ag := (adicResidueScalarAdjunction_existsUnique g).exists.choose
  let ah : extend h ⊣ dres h := adicResidueScalarAdjunction.{u, v} X J U n
  have hf : af.unit = adicFiniteUnit f :=
    (adicResidueScalarAdjunction_existsUnique f).exists.choose_spec
  have hg : ag.unit = adicFiniteUnit g :=
    (adicResidueScalarAdjunction_existsUnique g).exists.choose_spec
  have hh : ah.unit = adicFiniteUnit h :=
    (adicResidueScalarAdjunction_existsUnique h).exists.choose_spec
  have hpf : IsIso ((extendComparison f).app P) := (derivedExtension f).computation P hP
  have hph : IsIso ((extendComparison h).app P) := (derivedExtension h).computation P hP
  have ht := scalar_transition_adjoint f g h eh af ag ah hf hg hh P hP M eP
  let R := (completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U
  have ho := congrArg (fun a ↦ (Q R).map a) (ordinary_tensor_successor X J U P n)
  simp only [CategoryTheory.Functor.map_comp] at ho
  change (Q R).map ((adicResidueQuotientTensorTower X J U P).map
      (homOfLE (Nat.le_succ n)).op) ≫
      ((Q R).map (scalarTensorComplexIso h P).hom ≫
        (resFactors h).hom.app (((change h).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (dres h).map (inv ((extendComparison h).app P)) ≫
        (dres h).map ((extend h).map eP.hom)) =
    ((Q R).map (scalarTensorComplexIso f P).hom ≫
      (resFactors f).hom.app (((change f).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (dres f).map (inv ((extendComparison f).app P)) ≫
      (dres f).map ((extend f).map eP.hom)) ≫ adicResidueAdjointStep X J U M n
  simp only [Category.assoc]
  rw [← Category.assoc, ho]
  simp only [Category.assoc]
  rw [ht]
  rfl

end AlgebraicGeometry.Scheme
