import Langlands.GroupScheme.SimplyConnected.AlmostSimpleSubproducts
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorGaloisAction
import Langlands.GroupScheme.Descent.GaloisInvariantClosedSubgroups
import Langlands.GroupScheme.Rational.UnipotentRadicalProperties

/-! # Canonical Galois transport and descent of actual subproducts -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
    (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Canonical Galois transport preserves inclusion on every test scheme. -/
theorem galoisTransport_monotone (σ : L ≃ₐ[k] L) :
    Monotone (galoisTransport k L G σ) := by
  intro F F' h T x hx
  exact h _ hx

/-- Galois transport and inverse transport cancel on all subgroup functors. -/
@[simp] theorem galoisTransport_inv_apply (σ : L ≃ₐ[k] L)
    (F : SubgroupFunctor ((GroupScheme.baseChange (algebraBaseMap k L)).obj G)) :
    galoisTransport k L G σ⁻¹ (galoisTransport k L G σ F) = F := by
  calc
    _ = galoisTransport k L G (σ⁻¹ * σ) F :=
      (congrFun (map_mul (galoisTransport k L G) σ⁻¹ σ) F).symm
    _ = F := by rw [inv_mul_cancel, map_one]; rfl

/-- Canonical Galois transport is an order isomorphism on all-test subgroups. -/
def galoisTransportOrderIso (σ : L ≃ₐ[k] L) :
    SubgroupFunctor ((GroupScheme.baseChange (algebraBaseMap k L)).obj G) ≃o
      SubgroupFunctor ((GroupScheme.baseChange (algebraBaseMap k L)).obj G) :=
  Equiv.toOrderIso
    { toFun := galoisTransport k L G σ
      invFun := galoisTransport k L G σ⁻¹
      left_inv := galoisTransport_inv_apply k L G σ
      right_inv := by
        intro F
        simpa only [inv_inv] using galoisTransport_inv_apply k L G σ⁻¹ F }
    (galoisTransport_monotone k L G σ)
    (galoisTransport_monotone k L G σ⁻¹)

end SubgroupFunctor

namespace SimplyConnectedAlmostSimpleProduct

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
    [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
    (D : SimplyConnectedAlmostSimpleProduct
      ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))

/-- Transport of a subproduct is the actual subproduct on transported indices. -/
theorem galoisTransport_range_subproductInclusion
    (σ : L ≃ₐ[k] L) (s : Set D.Index) :
    SubgroupFunctor.galoisTransport k L G σ
        (SubgroupFunctor.range (D.subproductInclusion s)) =
      SubgroupFunctor.range (D.subproductInclusion (D.galoisFactorIndex σ '' s)) := by
  let e := SubgroupFunctor.galoisTransportOrderIso k L G σ
  apply le_antisymm
  · apply e.le_symm_apply.mp
    apply (D.range_subproductInclusion_le_iff s _).mpr
    intro i hi
    apply e.le_symm_apply.mpr
    change SubgroupFunctor.galoisTransport k L G σ
      (SubgroupFunctor.range (D.inclusion i)) ≤ _
    rw [← D.range_inclusion_galoisFactorIndex σ i]
    exact (D.range_subproductInclusion_le_iff _ _).mp le_rfl _ ⟨i, hi, rfl⟩
  · apply (D.range_subproductInclusion_le_iff _ _).mpr
    rintro j ⟨i, hi, rfl⟩
    rw [D.range_inclusion_galoisFactorIndex σ i]
    exact SubgroupFunctor.galoisTransport_monotone k L G σ
      ((D.range_subproductInclusion_le_iff s _).mp le_rfl i hi)

/-- An invariant index subset defines a canonically invariant actual subgroup. -/
theorem galoisTransport_range_subproductInclusion_eq_self
    (s : Set D.Index) (hs : ∀ σ : L ≃ₐ[k] L, D.galoisFactorIndex σ '' s = s)
    (σ : L ≃ₐ[k] L) :
    SubgroupFunctor.galoisTransport k L G σ
        (SubgroupFunctor.range (D.subproductInclusion s)) =
      SubgroupFunctor.range (D.subproductInclusion s) := by
  rw [D.galoisTransport_range_subproductInclusion, hs σ]

/-- An invariant subset of factors has an actual affine closed-subgroup
model over the original field, with exact recovery of its inclusion. -/
theorem exists_subproduct_descent [IsAffineHom G.X.hom] [IsGalois k L]
    (s : Set D.Index) (hs : ∀ σ : L ≃ₐ[k] L, D.galoisFactorIndex σ '' s = s) :
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G)
      (r : (GroupScheme.baseChange (algebraBaseMap k L)).obj H ≅ D.subproduct s),
      IsAffine H.X.left ∧ IsClosedSubgroup j ∧
        (GroupScheme.baseChange (algebraBaseMap k L)).map j =
          r.hom ≫ D.subproductInclusion s := by
  apply Descent.GaloisInvariantClosedSubgroup.exists_descent
    (D.isClosedSubgroup_subproductInclusion s)
  intro σ
  have h := D.galoisTransport_range_subproductInclusion_eq_self s hs σ
  change SubgroupFunctor.descentTransport _ _ _ _ _ = _ at h
  rwa [SubgroupFunctor.descentTransport_range] at h

/-- The descended subproduct retains smoothness, connectedness and normality
in the original group. -/
theorem exists_smoothConnectedNormal_subproduct_descent
    [IsAffineHom G.X.hom] [IsGalois k L]
    (s : Set D.Index) (hs : ∀ σ : L ≃ₐ[k] L, D.galoisFactorIndex σ '' s = s) :
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G)
      (r : (GroupScheme.baseChange (algebraBaseMap k L)).obj H ≅ D.subproduct s),
      IsAffine H.X.left ∧ IsClosedSubgroup j ∧ Smooth H.X.hom ∧
        ConnectedSpace H.X.left ∧ (SubgroupFunctor.range j).IsNormal ∧
        (GroupScheme.baseChange (algebraBaseMap k L)).map j =
          r.hom ≫ D.subproductInclusion s := by
  obtain ⟨H, j, r, hA, hj, hr⟩ := D.exists_subproduct_descent s hs
  let b := algebraBaseMap k L
  let : Surjective b := (fieldExtension_fpqc k L).1
  let : Flat b := (fieldExtension_fpqc k L).2.1
  let : QuasiCompact b := (fieldExtension_fpqc k L).2.2
  let : Smooth (D.subproduct s).X.hom := D.smooth_subproduct s
  let : ConnectedSpace (D.subproduct s).X.left := D.connectedSpace_subproduct s
  have hsm : Smooth ((GroupScheme.baseChange b).obj H).X.hom := by
    rw [← r.hom.hom.hom.w]
    infer_instance
  have hc : ConnectedSpace ((GroupScheme.baseChange b).obj H).X.left :=
    r.hom.hom.hom.left.homeomorph.connectedSpace_iff.mpr inferInstance
  have he : (SubgroupFunctor.range j).baseChange b =
      SubgroupFunctor.range (D.subproductInclusion s) := by
    rw [← SubgroupFunctor.range_baseChangeHom, hr, SubgroupFunctor.range_iso_comp]
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  refine ⟨H, j, r, hA, hj, smooth_of_baseChange b H hsm,
    connectedSpace_of_baseChange b H hc, ?_, hr⟩
  apply SubgroupFunctor.isNormal_range_of_baseChange b j
  rw [he]
  exact D.isNormal_range_subproductInclusion s

end SimplyConnectedAlmostSimpleProduct

end Langlands.GroupScheme
