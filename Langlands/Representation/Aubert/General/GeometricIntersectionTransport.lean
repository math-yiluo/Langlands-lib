import Langlands.Representation.Aubert.General.GeometricK0Target
import Langlands.Representation.Geometric.GeneralIntersections

/-! # Transport between the two actual geometric-intersection conventions -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uG uV

variable {G : Type uG} [Group G]

@[simp]
theorem mem_geometricSourceIntersection (A B : Subgroup G) (n x : G) :
    x ∈ geometricSourceIntersection A B n ↔ x ∈ B ∧ n * x * n⁻¹ ∈ A := by
  change (x ∈ B ∧ x ∈ A.map (MulAut.conj n⁻¹).toMonoidHom) ↔ _
  rw [Subgroup.mem_map_equiv]
  simp

@[simp]
theorem mem_geometricTargetIntersection (A B : Subgroup G) (n x : G) :
    x ∈ geometricTargetIntersection A B n ↔ x ∈ A ∧ n⁻¹ * x * n ∈ B := by
  change (x ∈ A ∧ x ∈ B.map (MulAut.conj n).toMonoidHom) ↔ _
  rw [Subgroup.mem_map_equiv]
  rfl

/-- The general BZ source and the actual Aubert source are the same subgroup. -/
theorem geometricSourceIntersection_eq_intersectionSource
    (A B : Subgroup G) (n : G) :
    geometricSourceIntersection A B n = Geometric.intersectionSource B A n := by
  ext x
  exact mem_geometricSourceIntersection A B n x

/-- The general BZ target and the actual Aubert target are the same subgroup. -/
theorem geometricTargetIntersection_eq_intersectionTarget
    (A B : Subgroup G) (n : G) :
    geometricTargetIntersection A B n = Geometric.intersectionTarget B A n := by
  ext x
  simpa only [Geometric.intersectionTarget, Subgroup.mem_inf, Subgroup.mem_comap,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      mem_geometricTargetIntersection A B n x

private theorem mem_intersectionIn_inv (A B : Subgroup G) (n : G) (x : A) :
    x ∈ Geometric.General.intersectionIn A B n⁻¹ ↔ n⁻¹ * (x : G) * n ∈ B := by
  rw [Geometric.General.mem_intersectionIn, inv_inv]

/-- The source subgroup inside `B` is literally the published `subgroupOf`. -/
theorem intersectionIn_eq_geometricSource_subgroupOf
    (A B : Subgroup G) (n : G) :
    Geometric.General.intersectionIn B A n =
      (geometricSourceIntersection A B n).subgroupOf B := by
  ext x
  simp only [Geometric.General.mem_intersectionIn, Subgroup.mem_subgroupOf,
    mem_geometricSourceIntersection]
  exact (and_iff_right x.property).symm

/-- The inverse representative gives the target subgroup inside `A`. -/
theorem intersectionIn_inv_eq_geometricTarget_subgroupOf
    (A B : Subgroup G) (n : G) :
    Geometric.General.intersectionIn A B n⁻¹ =
      (geometricTargetIntersection A B n).subgroupOf A := by
  ext x
  simp only [Geometric.General.mem_intersectionIn, Subgroup.mem_subgroupOf,
    mem_geometricTargetIntersection, inv_inv]
  exact (and_iff_right x.property).symm

section Topology

variable [TopologicalSpace G]

/-- Reassociate the source subgroup subtypes, preserving their induced topology. -/
def geometricSourceIntersectionEquiv (A B : Subgroup G) (n : G) :
    Geometric.General.intersectionIn B A n ≃ₜ* geometricSourceIntersection A B n where
  toFun x := ⟨x.val.val, (mem_geometricSourceIntersection A B n _).mpr
    ⟨x.val.property, x.property⟩⟩
  invFun x := ⟨⟨x.val, ((mem_geometricSourceIntersection A B n _).mp x.property).1⟩,
    ((mem_geometricSourceIntersection A B n _).mp x.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _

@[simp]
theorem geometricSourceIntersectionEquiv_apply (A B : Subgroup G) (n : G)
    (x : Geometric.General.intersectionIn B A n) :
    (geometricSourceIntersectionEquiv A B n x : G) = x.val.val := rfl

@[simp]
theorem geometricSourceIntersectionEquiv_symm_apply (A B : Subgroup G) (n : G)
    (x : geometricSourceIntersection A B n) :
    ((geometricSourceIntersectionEquiv A B n).symm x).val.val = (x : G) := rfl

/-- Reassociate the target subtypes, with `n⁻¹` in the BZ intersection. -/
def geometricTargetIntersectionEquiv (A B : Subgroup G) (n : G) :
    Geometric.General.intersectionIn A B n⁻¹ ≃ₜ* geometricTargetIntersection A B n where
  toFun x := ⟨x.val.val, (mem_geometricTargetIntersection A B n _).mpr
    ⟨x.val.property, (mem_intersectionIn_inv A B n _).mp x.property⟩⟩
  invFun x := ⟨⟨x.val, ((mem_geometricTargetIntersection A B n _).mp x.property).1⟩,
    (mem_intersectionIn_inv A B n _).mpr
      ((mem_geometricTargetIntersection A B n _).mp x.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _

@[simp]
theorem geometricTargetIntersectionEquiv_apply (A B : Subgroup G) (n : G)
    (x : Geometric.General.intersectionIn A B n⁻¹) :
    (geometricTargetIntersectionEquiv A B n x : G) = x.val.val := rfl

@[simp]
theorem geometricTargetIntersectionEquiv_symm_apply (A B : Subgroup G) (n : G)
    (x : geometricTargetIntersection A B n) :
    ((geometricTargetIntersectionEquiv A B n).symm x).val.val = (x : G) := rfl

variable [IsTopologicalGroup G]

/-- Reassociation carries the inverse of the BZ forward conjugation to the
actual inverse-conjugation map used by Aubert's representation functor. -/
theorem geometricIntersection_conjugationEquiv (A B : Subgroup G) (n : G) :
    ((geometricTargetIntersectionEquiv A B n).symm.trans
      (Geometric.General.intersectionEquivContinuous B A n).symm).trans
        (geometricSourceIntersectionEquiv A B n) =
      conjugationEquiv n (geometricIntersectionMembership A B n) := by
  ext x
  exact Geometric.General.intersectionEquiv_symm_apply B A n
    ((geometricTargetIntersectionEquiv A B n).symm x)

/-- The actual action after the three subtype/conjugation transports is
`σ(n⁻¹ x n)`. No normalizer or structural realization is assumed. -/
theorem geometricIntersection_transport_apply (A B : Subgroup G) (n : G)
    (σ : SmoothRep.{0, uG, uV} ℂ (geometricSourceIntersection A B n))
    (x : geometricTargetIntersection A B n) (v : σ) :
    ((SmoothRep.pullbackFunctor (geometricTargetIntersectionEquiv A B n).symm).obj
      ((SmoothRep.pullbackFunctor
        (Geometric.General.intersectionEquivContinuous B A n).symm).obj
        ((SmoothRep.pullbackFunctor (geometricSourceIntersectionEquiv A B n)).obj σ)
      )).representation x v =
      σ.representation (conjugationEquiv n (geometricIntersectionMembership A B n) x) v := by
  change σ.representation
    (((((geometricTargetIntersectionEquiv A B n).symm.trans
      (Geometric.General.intersectionEquivContinuous B A n).symm).trans
        (geometricSourceIntersectionEquiv A B n))) x) v = _
  rw [geometricIntersection_conjugationEquiv]

/-- Natural comparison of the BZ intersection transport with the actual
Aubert conjugation functor, with identity linear maps on every carrier. -/
def geometricIntersectionTransportIso (A B : Subgroup G) (n : G) :
    SmoothRep.pullbackFunctor (geometricSourceIntersectionEquiv A B n) ⋙
      SmoothRep.pullbackFunctor
        (Geometric.General.intersectionEquivContinuous B A n).symm ⋙
      SmoothRep.pullbackFunctor (geometricTargetIntersectionEquiv A B n).symm ≅
        conjugationFunctor.{uG, uV} n (geometricIntersectionMembership A B n) :=
  NatIso.ofComponents (fun σ =>
    SmoothRep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ σ) fun x => by
      ext v
      exact geometricIntersection_transport_apply A B n σ x v)) (fun f => by
        ext v
        rfl)

/-- The same comparison on exact finite-length K0, using the three actual
continuous equivalences and the actual Aubert conjugation map. -/
theorem geometricIntersection_conjugationK0 (A B : Subgroup G) (n : G) :
    (SmoothRep.FiniteLengthGrothendieckGroup.pullback.{uG, uG, uV}
      (geometricTargetIntersectionEquiv A B n).symm).comp
      ((SmoothRep.FiniteLengthGrothendieckGroup.pullback
        (Geometric.General.intersectionEquivContinuous B A n).symm).comp
        (SmoothRep.FiniteLengthGrothendieckGroup.pullback
          (geometricSourceIntersectionEquiv A B n))) =
      conjugationK0.{uG, uV} n (geometricIntersectionMembership A B n) := by
  rw [← SmoothRep.FiniteLengthGrothendieckGroup.pullback_trans,
    ← SmoothRep.FiniteLengthGrothendieckGroup.pullback_trans]
  change SmoothRep.FiniteLengthGrothendieckGroup.pullback
    (((geometricTargetIntersectionEquiv A B n).symm.trans
      (Geometric.General.intersectionEquivContinuous B A n).symm).trans
        (geometricSourceIntersectionEquiv A B n)) = _
  rw [geometricIntersection_conjugationEquiv]
  rfl

end Topology

end Langlands.Aubert.General
