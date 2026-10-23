import Langlands.Galois.Local.InertiaFixedFieldBaseChangeStatement
import Langlands.Weil.Local.ExtensionWeil

/-! # Full inertia fixed-field comparison under finite base change -/

noncomputable section

namespace Langlands.PadicField

open Langlands.Weil.Local

universe u

private theorem extensionGaloisMap_mem_absoluteInertia
    {p : ℕ} [Fact p.Prime] (F E : PadicField.{u} p)
    (f : F.Carrier →ₐ[Padic p] E.Carrier)
    (τ : Field.absoluteGaloisGroup E.Carrier) :
    extensionGaloisMap F E f τ ∈ F.absoluteInertia F.canonicalTopologicalData ↔
      τ ∈ E.absoluteInertia E.canonicalTopologicalData := by
  rw [← F.absoluteResidueHom_ker F.canonicalTopologicalData,
    ← E.absoluteResidueHom_ker E.canonicalTopologicalData]
  change localResidueMap F (extensionGaloisMap F E f τ) = 1 ↔
    localResidueMap E τ = 1
  rw [localResidueMap_extensionGaloisMap, ← map_one (extensionResidueGaloisMap F E f)]
  exact (extensionResidueGaloisMap_injective F E f).eq_iff

/-- The exact published full fixed-field equality, for every compatible closure map. -/
theorem inertiaFixedFieldBaseChange : InertiaFixedFieldBaseChange.{u} := by
  intro p hp F D
  let : Algebra F.Carrier (AlgebraicClosure D.field) :=
    ((algebraMap D.field (AlgebraicClosure D.field)).comp
      (algebraMap F.Carrier D.field)).toAlgebra
  let : SMul F.Carrier (AlgebraicClosure D.field) :=
    (inferInstance : Algebra F.Carrier (AlgebraicClosure D.field)).toSMul
  let : SMul D.field (AlgebraicClosure D.field) :=
    (inferInstance : Algebra D.field (AlgebraicClosure D.field)).toSMul
  let : IsScalarTower F.Carrier D.field (AlgebraicClosure D.field) :=
    IsScalarTower.of_algebraMap_eq' rfl
  dsimp only
  intro j _hj
  let E := D.asPadicField (p := p)
  let : Algebra (Padic p) D.field := E.algebra
  let f : F.Carrier →ₐ[Padic p] E.Carrier :=
    { toRingHom := algebraMap F.Carrier D.field
      commutes' := fun _ => rfl }
  let q := extensionClosureEquiv F E f
  have : Algebra.IsAlgebraic F.Carrier (AlgebraicClosure D.field) :=
    Algebra.IsAlgebraic.trans F.Carrier D.field (AlgebraicClosure D.field)
  have hjbij : Function.Bijective j :=
    (Algebra.IsAlgebraic.algHom_bijective₂ j
      (IsAlgClosed.lift : AlgebraicClosure D.field →ₐ[F.Carrier]
        AlgebraicClosure F.Carrier)).1
  let e := AlgEquiv.ofBijective j hjbij
  let c : AlgebraicClosure F.Carrier ≃ₐ[F.Carrier] AlgebraicClosure F.Carrier := AlgEquiv.ofRingEquiv
    (f := e.toRingEquiv.trans q.symm) (fun a => by
      apply q.injective
      change q (q.symm (j (algebraMap F.Carrier (AlgebraicClosure F.Carrier) a))) = _
      rw [q.apply_symm_apply, j.commutes]
      exact (extensionClosureLift_algebraMap F E f a).symm)
  have hjq (x : AlgebraicClosure F.Carrier) : j x = q (c x) :=
    (q.apply_symm_apply (j x)).symm
  let IF : Subgroup Gal(AlgebraicClosure F.Carrier/F.Carrier) := F.absoluteInertia F.canonicalTopologicalData
  let ID : Subgroup Gal(AlgebraicClosure D.field/D.field) := E.absoluteInertia E.canonicalTopologicalData
  have hnormal : IF.Normal := F.absoluteInertia_normal F.canonicalTopologicalData
  let UF := IntermediateField.fixedField IF
  have : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  have : CharZero D.field := inferInstance
  have hIF : UF.fixingSubgroup = IF :=
    InfiniteGalois.fixingSubgroup_fixedField
      ⟨IF, F.absoluteInertia_isClosed F.canonicalTopologicalData⟩
  let S := IntermediateField.adjoin D.field
    (j '' (UF : Set (AlgebraicClosure F.Carrier)))
  have hS : S.fixingSubgroup = ID := by
    ext τ
    let t : Gal(AlgebraicClosure F.Carrier/F.Carrier) := extensionGaloisMap F E f τ
    let g : AlgebraicClosure F.Carrier ≃ₐ[F.Carrier] AlgebraicClosure F.Carrier :=
      c⁻¹ * t * c
    have hg (x : AlgebraicClosure F.Carrier) : j (g x) = τ (j x) := by
      rw [hjq, hjq x]
      change q (c (c.symm (AlgEquiv.toAlgHom (extensionGaloisMap F E f τ) (c x)))) = _
      rw [c.apply_symm_apply]
      exact extensionClosureLift_galoisMap F E f τ (c x)
    have hmem : g ∈ IF ↔ τ ∈ ID := by
      change c⁻¹ * t * c ∈ IF ↔ _
      rw [hnormal.mem_comm_iff]
      simp only [mul_inv_cancel_left]
      exact extensionGaloisMap_mem_absoluteInertia F E f τ
    calc
      τ ∈ S.fixingSubgroup ↔ ∀ x ∈ j '' (UF : Set _), τ x = x :=
        (IntermediateField.mem_fixingSubgroup_iff S τ).trans
          (IntermediateField.forall_mem_adjoin_smul_eq_self_iff D.field τ)
      _ ↔ ∀ x ∈ UF, g x = x := by
        simp only [Set.forall_mem_image]
        exact forall₂_congr fun x _ => by rw [← hg]; exact j.injective.eq_iff
      _ ↔ g ∈ UF.fixingSubgroup := (IntermediateField.mem_fixingSubgroup_iff UF g).symm
      _ ↔ g ∈ IF := by rw [hIF]
      _ ↔ τ ∈ ID := hmem
  calc
    IntermediateField.fixedField ID = IntermediateField.fixedField S.fixingSubgroup :=
      congrArg IntermediateField.fixedField hS.symm
    _ = S := InfiniteGalois.fixedField_fixingSubgroup S

end Langlands.PadicField
