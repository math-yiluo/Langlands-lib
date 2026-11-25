/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueQuotientTensorTower
import WeilConjectures.AlgebraicGeometry.AdicResidueQuotientTensorSuccessor
import WeilConjectures.CategoryTheory.RingedScalarTensorUnit

/-! # The actual quotient coefficient tower and its tensor model

Source: Stacks Project, proetale.tex, lemma-naive-completion (099M).
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

variable (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
  (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)

private theorem quotientTensorLevel_unit
    (M : AdicResidueLocalDerived.{u, v} X J U)
    (P : Cx ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U))
    (hP : P.IsKFlatTensor) (eP : (Q _).obj P ≅ M) (n : ℕ) :
    (Q _).map (adicResidueQuotientTensorUnit X J U P n) ≫
        (adicResidueQuotientTensorLevelIso X J U P hP M eP n).hom =
      eP.hom ≫ (adicResidueScalarAdjunction.{u, v} X J U n).unit.app M := by
  let f := adicResidueLocalProjection.{u, v} X J U n
  have : IsIso ((extendComparison f).app P) := (derivedExtension f).computation P hP
  have ha : (adicResidueScalarAdjunction.{u, v} X J U n).unit = adicFiniteUnit f :=
    (adicResidueScalarAdjunction_existsUnique f).exists.choose_spec
  have hu := (adicFiniteUnit_existsUnique f).exists.choose_spec P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mpr hP)
  have ho : (Q _).map (adicResidueQuotientTensorUnit X J U P n) ≫
      (Q _).map (scalarTensorComplexIso f P).hom =
        (Q _).map (adicFiniteOrdinaryUnitComplex f P) := by
    rw [← Functor.map_comp]
    congr 1
    exact scalarTensorComplexIso_unit f P
  rw [ha]
  change (Q _).map (adicResidueQuotientTensorUnit X J U P n) ≫
      (Q _).map (scalarTensorComplexIso f P).hom ≫
        (resFactors f).hom.app (((change f).mapHomologicalComplex (.up ℤ)).obj P) ≫
          (dres f).map (inv ((extendComparison f).app P)) ≫
            (dres f).map ((extend f).map eP.hom) =
      eP.hom ≫ (adicFiniteUnit f).app M
  rw [← Category.assoc, ho]
  erw [← reassoc_of% hu]
  simp only [← Functor.map_comp, IsIso.hom_inv_id_assoc]
  simpa only [adicFiniteUnit, Functor.comp_map, Functor.id_map] using
    ((adicFiniteUnit f).naturality eP.hom).symm

/-- The strict quotient tensor model computes the normalized scalar-adjoint tower.
No Koszul system, generating list, Noetherian hypothesis, or limit occurs here.

Source: Stacks Project, proetale.tex, lemma-naive-completion (099M), and
sites-cohomology.tex, derived change of rings (06YY).
(auxiliary; not a blueprint node).

Proof: the sheaf tensor symmetry and balancing identify P tensor_R B_n[0] with
restriction of the termwise scalar extension of P to B_n. K-flatness of P makes
its universal derived scalar comparison invertible. Compose its inverse with
resFactors to obtain the level isomorphisms for Q(P). The ordinary map x to
x tensor 1 is the scalar adjunction unit, by the normalization defining
adicFiniteUnit and adicResidueScalarAdjunction. The quotient successor sends
x tensor s to x tensor bar(s). Under scalar adjunction it is the reduction of
the preceding counit: both send a balanced tensor to the product of its scalar
factors. Thus the level isomorphisms commute with successors, and hence all tower
maps. Finally apply naturality of the adjunction unit to eP. This gives e and the
displayed equations. All formulas work for zero rings and zero complexes, and do
not require the quotient to be flat or perfect over R. -/
theorem adicResidue_quotient_tensor_model
    (M : AdicResidueLocalDerived.{u, v} X J U)
    (P : Cx ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U))
    (hP : P.IsKFlatTensor) (eP : (Q _).obj P ≅ M) :
    ∃ e : (adicResidueQuotientTensorComplex X J U P).asFunctor ⋙ Q _ ≅
        adicResidueAdjointTower.{u, v} X J U M,
      ∀ n : ℕ, (Q _).map (adicResidueQuotientTensorUnit X J U P n) ≫
        e.hom.app (op n) = eP.hom ≫
          (adicResidueScalarAdjunction.{u, v} X J U n).unit.app M := by
  let F := (adicResidueQuotientTensorComplex X J U P).asFunctor ⋙ Q _
  let G := adicResidueAdjointTower.{u, v} X J U M
  let a : F ⟶ G := NatTrans.ofOpSequence
    (fun n ↦ (adicResidueQuotientTensorLevelIso X J U P hP M eP n).hom) (by
      intro n
      change (Q _).map ((adicResidueQuotientTensorTower X J U P).map
          (homOfLE (Nat.le_succ n)).op) ≫ _ =
        _ ≫ (adicResidueAdjointTower.{u, v} X J U M).map
          (homOfLE (Nat.le_succ n)).op
      simpa only [adicResidueAdjointTower, Functor.ofOpSequence_map_homOfLE_succ] using
        adicResidueQuotientTensorLevelIso_successor X J U P hP M eP n)
  let e : F ≅ G := NatIso.ofComponents
    (fun k ↦ adicResidueQuotientTensorLevelIso X J U P hP M eP k.unop)
    (fun g ↦ a.naturality g)
  refine ⟨e, ?_⟩
  intro n
  exact quotientTensorLevel_unit X J U M P hP eP n

end AlgebraicGeometry.Scheme
