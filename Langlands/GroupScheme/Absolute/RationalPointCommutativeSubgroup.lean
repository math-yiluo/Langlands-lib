import Langlands.GroupScheme.Absolute.RationalPointClosureProof
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-! # Commutative closed subgroups containing rational points -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace RationalPointClosure

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section Core

variable {k : Type u} [Field k] {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  (Γ : Subgroup (F.obj (baseAlgebra k)))

/-- Evaluation of the left universal point at a pair of rational subgroup points. -/
theorem map_pairLift_left (a : Γ × Γ) :
    F.map (pairLift a) (F.map (inclLeft e Γ) (universalPoint e Γ)) = a.1.1 := by
  rw [map_map]
  have hl : inclLeft e Γ ≫ pairLift a = lift a.1.1 (mem_cutSet_of_mem a.1.2) := by
    apply CommAlgCat.hom_ext
    rw [CommAlgCat.hom_comp, pairLift, CommAlgCat.hom_ofHom, CommAlgCat.hom_ofHom]
    exact Algebra.TensorProduct.lift_comp_includeLeft _ _ _
  rw [hl, map_lift_universalPoint]

/-- Evaluation of the right universal point at a pair of rational subgroup points. -/
theorem map_pairLift_right (a : Γ × Γ) :
    F.map (pairLift a) (F.map (inclRight e Γ) (universalPoint e Γ)) = a.2.1 := by
  rw [map_map]
  have hr : inclRight e Γ ≫ pairLift a = lift a.2.1 (mem_cutSet_of_mem a.2.2) := by
    apply CommAlgCat.hom_ext
    rw [CommAlgCat.hom_comp, pairLift, CommAlgCat.hom_ofHom, CommAlgCat.hom_ofHom]
    exact Algebra.TensorProduct.lift_comp_includeRight' _ _ _
  rw [hr, map_lift_universalPoint]

variable [IsMulCommutative Γ]

/-- When the rational subgroup is abelian, the two universal points commute over the
tensor square of its quotient coordinate algebra. -/
theorem universal_mul_comm :
    F.map (inclLeft e Γ) (universalPoint e Γ) * F.map (inclRight e Γ) (universalPoint e Γ) =
      F.map (inclRight e Γ) (universalPoint e Γ) * F.map (inclLeft e Γ) (universalPoint e Γ) := by
  let : Field (CommRingCat.of k) := inferInstanceAs (Field k)
  apply e.homEquiv.symm.injective
  apply CommAlgCat.hom_ext
  ext b
  apply sub_eq_zero.mp
  apply tensor_eq_zero_of_separating
    (fun a : Γ => (lift a.1 (mem_cutSet_of_mem a.2)).hom) eq_zero_of_forall_lift
  intro a a'
  change (pairLift (a, a')).hom _ = 0
  rw [map_sub, sub_eq_zero, ← AlgHom.comp_apply, ← AlgHom.comp_apply,
    ← CommAlgCat.hom_comp, ← CommAlgCat.hom_comp, ← homEquiv_symm_map, ← homEquiv_symm_map]
  apply congrArg (fun z => (e.homEquiv.symm z).hom b)
  rw [map_mul, map_mul, map_pairLift_left, map_pairLift_right]
  exact congrArg Subtype.val (mul_comm' a a')

/-- All algebra points of the rational closure commute when its defining rational subgroup
is abelian. This also applies to nonreduced test algebras. -/
theorem mul_comm_of_mem_cutSet {A : CommAlgCat.{u} (CommRingCat.of k)} {x y : F.obj A}
    (hx : x ∈ cutSet e Γ A) (hy : y ∈ cutSet e Γ A) : x * y = y * x := by
  obtain ⟨ψ, rfl⟩ := (mem_cutSet_iff x).1 hx
  obtain ⟨ψ', rfl⟩ := (mem_cutSet_iff y).1 hy
  let L : tensorSquare e Γ ⟶ A := CommAlgCat.ofHom
    (Algebra.TensorProduct.lift ψ.hom ψ'.hom fun _ _ => Commute.all _ _)
  have hl : inclLeft e Γ ≫ L = ψ := by
    apply CommAlgCat.hom_ext
    rw [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom, CommAlgCat.hom_ofHom]
    exact Algebra.TensorProduct.lift_comp_includeLeft _ _ _
  have hr : inclRight e Γ ≫ L = ψ' := by
    apply CommAlgCat.hom_ext
    rw [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom, CommAlgCat.hom_ofHom]
    exact Algebra.TensorProduct.lift_comp_includeRight' _ _ _
  have h := congrArg (F.map L) (universal_mul_comm e Γ)
  simpa only [map_mul, map_map, hl, hr] using h

/-- The closed group scheme of the closure of an abelian rational subgroup is commutative
on every test scheme. -/
theorem isCommMonObj_closure :
    IsCommMonObj (Corepresented.cutGroupScheme (isCutOutBy_closureSubgroup e Γ)).X := by
  apply (isCommMonObj_iff_isMulCommutative _).2
  intro T
  refine ⟨⟨fun x y => ?_⟩⟩
  let E := Corepresented.pointsEquiv _
    (Corepresented.cutCorepresentableBy (isCutOutBy_closureSubgroup e Γ)) T
  apply E.injective
  rw [map_mul, map_mul]
  apply Subtype.ext
  exact mul_comm_of_mem_cutSet e Γ (E x).property (E y).property

end Core

end RationalPointClosure

/-- Every rational point of an affine group scheme over a field belongs to an actual
commutative closed subgroup. No finite type, smoothness or connectedness is assumed. -/
def RationalPointCommutativeSubgroupStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffine G.X.left] (x : Lie.AffinePoints G k),
    ∃ (C : CommGroupScheme (Spec (CommRingCat.of k))) (z : C.toGrp ⟶ G)
      (y : Lie.AffinePoints C.toGrp k),
      IsClosedSubgroup z ∧ y ≫ z.hom.hom = x

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
open RationalPointClosure in
/-- Take the reduced closed subgroup defined by the functions vanishing on the integer
powers of the point. The tensor-separation argument makes this subgroup commutative. -/
theorem rationalPointCommutativeSubgroup : RationalPointCommutativeSubgroupStatement.{u} := by
  intro k _ G _ x
  obtain ⟨⟨B⟩, ⟨j⟩⟩ := (essImage_algSpec (G := G.X)).mpr inferInstance
  let e := AffineLinearEmbedding.corepresentableBy G j
  let Γ : Subgroup (G.affinePointFunctor.obj (baseAlgebra k)) := Subgroup.zpowers x
  let : IsMulCommutative Γ := Subgroup.zpowers_isMulCommutative x
  have hI := isCutOutBy_closureSubgroup e Γ
  let C : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { toGrp := Corepresented.cutGroupScheme hI
      comm := isCommMonObj_closure e Γ }
  let z : C.toGrp ⟶ G :=
    Corepresented.cutHom hI ≫ (AffineLinearEmbedding.modelIso G j).hom
  have hj : IsIso j.hom.left := inferInstanceAs (IsIso ((Over.forget _).map j.hom))
  have hz : IsClosedSubgroup z := by
    have : IsClosedImmersion (Corepresented.cutHom hI).hom.hom.left :=
      Corepresented.isClosedImmersion_cutHom hI
    change IsClosedImmersion
      ((Corepresented.cutHom hI).hom.hom.left ≫
        (AffineLinearEmbedding.modelIso G j).hom.hom.hom.left)
    rw [modelIso_hom_hom_hom]
    infer_instance
  have hx : x ∈ cutSet e Γ (baseAlgebra k) :=
    mem_cutSet_of_mem (Subgroup.mem_zpowers x)
  let y : Lie.AffinePoints C.toGrp k := by
    change (algSpec (CommRingCat.of k)).obj (op (baseAlgebra k)) ⟶
      (algSpec (CommRingCat.of k)).obj (op (quotient e Γ))
    exact (algSpec (CommRingCat.of k)).map (lift (e := e) (Γ := Γ) x hx).op
  refine ⟨C, z, y, hz, ?_⟩
  have hc : (Corepresented.cutHom hI).hom.hom =
      (algSpec _).map (Corepresented.quotientMap (vanishingIdeal e Γ)).op := by
    apply Over.OverMorphism.ext
    exact Corepresented.cutHom_left hI
  change (algSpec _).map (lift (e := e) (Γ := Γ) x hx).op ≫
    ((Corepresented.cutHom hI).hom.hom ≫
      (AffineLinearEmbedding.modelIso G j).hom.hom.hom) = x
  rw [hc, modelIso_hom_hom_hom, ← Category.assoc, ← Functor.map_comp, ← op_comp,
    quotientMap_comp_lift]
  exact e.homEquiv.apply_symm_apply x

end Langlands.GroupScheme
