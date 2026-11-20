import Langlands.GroupScheme.Torus.OrderedProjectorComparison
import Langlands.GroupScheme.Torus.OrderedProjectorSubgroup
import Langlands.GroupScheme.Torus.DiagonalizableAutomorphismLocality
import Langlands.GroupScheme.Torus.DiagonalizablePower

/-! # Relabelling actual ordered projector subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OrderedProjectorScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : CommRingCat.{u}} {Λ Λ' : Type u} [AddCommGroup Λ] [AddCommGroup Λ']
variable {J K n : Type} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype n] [DecidableEq n]

private theorem restrictMap_id (A : CommRingCat.{u}) (Λ : Type u) [AddCommGroup Λ] :
    Diagonalizable.restrictMap A (AddMonoidHom.id Λ) = 𝟙 (Diagonalizable.groupScheme A Λ).toGrp := by
  simpa only [one_smul, powerHom, pow_one] using
    (Diagonalizable.restrictMap_nsmul_id A (A := Λ) 1)

/-- The group-scheme isomorphism induced by a matching of the two character groups. -/
def WeightEquivalence.groupIso {w : J → Λ} {v : K → Λ'} (e : WeightEquivalence w v)
    (R : CommRingCat.{u}) : (Diagonalizable.groupScheme R Λ).toGrp ≅
      (Diagonalizable.groupScheme R Λ').toGrp where
  hom := Diagonalizable.restrictMap R e.lattice.toAddMonoidHom
  inv := Diagonalizable.restrictMap R e.lattice.symm.toAddMonoidHom
  hom_inv_id := by
    rw [Diagonalizable.restrictMap_comp]
    rw [show e.lattice.toAddMonoidHom.comp e.lattice.symm.toAddMonoidHom = AddMonoidHom.id Λ by
      ext m
      exact e.lattice.apply_symm_apply m, restrictMap_id]
  inv_hom_id := by
    rw [Diagonalizable.restrictMap_comp]
    rw [show e.lattice.symm.toAddMonoidHom.comp e.lattice.toAddMonoidHom = AddMonoidHom.id Λ' by
      ext m
      exact e.lattice.symm_apply_apply m, restrictMap_id]

private theorem sourcePoints_restrictMap (T : Over (Spec R)) (U : Over T.left) (g : Λ' →+ Λ)
    (x : U ⟶ ((baseChange T.hom).obj (Diagonalizable.groupScheme R Λ).toGrp).X) (m : Λ') :
    sourcePoints T Λ' U (x ≫ ((baseChange T.hom).map (Diagonalizable.restrictMap R g)).hom.hom)
        (.ofAdd m) = sourcePoints T Λ U x (.ofAdd (g m)) := by
  simp only [sourcePoints, MulEquiv.trans_apply, baseChangePointsEquiv_comp]
  exact Diagonalizable.pointsEquiv_restrictMap R g _ m

/-- Matched weights and relabelled projectors give the same subgroup homomorphism after
precomposition with the character restriction. -/
theorem subgroupHom_eq_of_relabel (T : Over (Spec R)) {w : J → Λ} {v : K → Λ'}
    (e : WeightEquivalence w v) (Q : Family K n Γ(T.left, ⊤)) :
    subgroupHom w T (Q.relabel e.labels) =
      (baseChange T.hom).map (e.groupIso R).hom ≫ subgroupHom v T Q := by
  refine hom_ext_points fun U x => (targetPoints T n U).injective ?_
  rw [Grp.comp_hom_hom, ← Category.assoc, targetPoints_subgroupHom, targetPoints_subgroupHom]
  change _ = weightedUnit (Q.map U.hom.appTop.hom)
    (fun i => sourcePoints T Λ' U
      (x ≫ ((baseChange T.hom).map (Diagonalizable.restrictMap R e.lattice.toAddMonoidHom)).hom.hom)
      (.ofAdd (v i)))
  simp only [sourcePoints_restrictMap]
  have h : (fun i => sourcePoints T Λ U x (.ofAdd (w i))) =
      (fun i => sourcePoints T Λ U x (.ofAdd (e.lattice (v i)))) ∘ e.labels := by
    funext i
    rw [Function.comp_apply, e.weight_eq]
  rw [h]
  have hP : (Q.relabel e.labels).map U.hom.appTop.hom =
      (Q.map U.hom.appTop.hom).relabel e.labels := Family.ext rfl
  rw [hP, weightedUnit_relabel]
  rfl

/-- Matched weights with the same relabelled projectors determine the same subgroup functor. -/
theorem range_subgroupHom_eq_of_relabel (T : Over (Spec R)) {w : J → Λ} {v : K → Λ'}
    (e : WeightEquivalence w v) (Q : Family K n Γ(T.left, ⊤)) :
    SubgroupFunctor.range (subgroupHom w T (Q.relabel e.labels)) =
      SubgroupFunctor.range (subgroupHom v T Q) := by
  rw [subgroupHom_eq_of_relabel T e Q]
  exact SubgroupFunctor.range_iso_comp ((baseChange T.hom).mapIso (e.groupIso R)) _

section Affine

variable {A : CommRingCat.{u}} (b : Spec A ⟶ Spec R) {w : J → Λ} {v : K → Λ'}

private theorem restrictMap_comp_representation (g : Λ' →+ Λ) (Q : Family K n A) :
    Diagonalizable.restrictMap A g ≫ representation v Q = representation (g ∘ v) Q := by
  refine hom_ext_points fun U x => (GeneralLinear.pointsEquiv n A U).injective ?_
  rw [Grp.comp_hom_hom, ← Category.assoc, representation_points, representation_points]
  congr 1
  funext i
  exact Diagonalizable.pointsEquiv_restrictMap A g x (v i)

private theorem characterMatrix_eq_of_representation_eq (P : Family J n A)
    (v' : K → Λ) (Q : Family K n A) (h : representation w P = representation v' Q) :
    characterMatrix w P = characterMatrix v' Q := by
  have hl := congrArg (fun f => f.hom.hom.left) h
  rw [representation_left, representation_left] at hl
  have hf := Spec.map_injective hl
  apply (GeneralLinear.homEquiv (n := n) (R := A) (S := AddMonoidAlgebra A Λ)).symm.injective
  apply AlgHom.ext
  intro a
  exact ConcreteCategory.congr_hom hf a

/-- Over a nonzero affine base, equality after a fixed character equivalence recovers the
weight matching and the relabelled projectors. -/
theorem exists_weightEquivalence_of_subgroupHom_comp [Nontrivial A] (g : Λ' ≃+ Λ)
    (P : Family J n Γ(Spec A, ⊤)) (Q : Family K n Γ(Spec A, ⊤))
    (hw : Function.Injective w) (hv : Function.Injective v)
    (h : subgroupHom w (Over.mk b) P =
      (baseChange b).map (Diagonalizable.restrictMap R g.toAddMonoidHom) ≫
        subgroupHom v (Over.mk b) Q) :
    ∃ e : WeightEquivalence w v, e.lattice = g ∧ P = Q.relabel e.labels := by
  let PA := P.map (Scheme.ΓSpecIso A).hom.hom
  let QA := Q.map (Scheme.ΓSpecIso A).hom.hom
  let d := Diagonalizable.baseChangeIso b Λ
  let d' := Diagonalizable.baseChangeIso b Λ'
  let gL := GeneralLinear.baseChangeIso n b
  have hh : d.hom ≫ representation w PA ≫ gL.inv =
      (baseChange b).map (Diagonalizable.restrictMap R g.toAddMonoidHom) ≫
        d'.hom ≫ representation v QA ≫ gL.inv := by
    simpa only [subgroupHom_spec] using h
  rw [← Category.assoc ((baseChange b).map (Diagonalizable.restrictMap R g.toAddMonoidHom)),
    Diagonalizable.baseChangeIso_restrictMap] at hh
  have hh' : representation w PA = Diagonalizable.restrictMap A g.toAddMonoidHom ≫
      representation v QA := by
    apply (cancel_epi d.hom).mp
    apply (cancel_mono gL.inv).mp
    simpa only [Category.assoc] using hh
  rw [restrictMap_comp_representation] at hh'
  obtain ⟨e, he, hp⟩ := exists_relabel_of_characterMatrix_eq w PA (g ∘ v) QA hw
    (g.injective.comp hv) (characterMatrix_eq_of_representation_eq PA _ QA hh')
  refine ⟨⟨g, e, he⟩, rfl, ?_⟩
  apply Family.ext
  funext i
  ext a c
  apply (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv.injective
  exact congrArg (fun F : Family J n A => F.matrix i a c) hp

end Affine

end Langlands.GroupScheme.OrderedProjectorScheme
