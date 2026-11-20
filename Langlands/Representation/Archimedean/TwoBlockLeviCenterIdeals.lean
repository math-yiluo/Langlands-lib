import Langlands.Representation.Archimedean.TwoBlockLeviCenterFinite
import Langlands.Algebra.EnvelopingCenterQuotients

/-! # Transfer of cofinite center ideals for one complex matrix algebra -/

noncomputable section

open scoped Classical TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.TwoBlockEnveloping

open Langlands.Algebra

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "M" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ
local notation "Z" => VermaGL.center
local notation "U" => VermaGL.glU

/-- The span of products of a member of the center ideal on the left and an arbitrary operator
on the right, for one complex matrix Lie algebra. -/
def complexMatrixCentralIdealSpan (n : ℕ) (J : Ideal (Z n)) : Submodule ℂ (U n) :=
  Submodule.span ℂ (Set.range fun p : J × U n => p.1.val.val * p.2)

private theorem complexMatrixCentralIdealSpan_mul (n : ℕ) (J : Ideal (Z n))
    {x : U n} (hx : x ∈ complexMatrixCentralIdealSpan n J) (y : U n) :
    x * y ∈ complexMatrixCentralIdealSpan n J := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨z, u⟩, rfl⟩ := hx
    rw [mul_assoc]
    exact Submodule.subset_span ⟨(z, u * y), rfl⟩
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x x' _ _ hx hx' => rw [add_mul]; exact Submodule.add_mem _ hx hx'
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx

variable (a b : ℕ)

local notation "L" => blockLevi (a + b) a
local notation "UL" => UniversalEnvelopingAlgebra ℂ L
local notation "ZL" => Subalgebra.center ℂ UL

private def productCenterToLevi :
    (Z a ⊗[ℂ] Z b) →ₐ[ℂ] ZL :=
  (LieEnvelopingEquiv.center (LieEnvelopingEquiv.enveloping (blockLeviLieEquiv a b))).toAlgHom.comp
    (LieEnvelopingEquiv.envelopingProductCenter ℂ (M a) (M b)).symm.toAlgHom

/-- Include the center of the first block into the Levi center. -/
def firstComplexBlockCenter : Z a →ₐ[ℂ] ZL :=
  (productCenterToLevi a b).comp Algebra.TensorProduct.includeLeft

/-- Include the center of the second block into the Levi center. -/
def secondComplexBlockCenter : Z b →ₐ[ℂ] ZL :=
  (productCenterToLevi a b).comp Algebra.TensorProduct.includeRight

private theorem firstComplexBlockCenter_inclusion (z : Z a) :
    leviInclusion (a + b) a (firstComplexBlockCenter a b z).val =
      firstComplexMatrixBlockEnveloping a b z.val := by
  change leviInclusion (a + b) a
    (LieEnvelopingEquiv.enveloping (blockLeviLieEquiv a b)
      ((LieEnvelopingEquiv.envelopingProductCenter ℂ (M a) (M b)).symm (z ⊗ₜ[ℂ] 1)).val) = _
  rw [LieEnvelopingEquiv.envelopingProductCenter_symm_left_val]
  change ((LieEnvelopingEquiv.map (L).incl).comp
    ((LieEnvelopingEquiv.map (blockLeviLieEquiv a b).toLieHom).comp
      (LieEnvelopingEquiv.map (LieHom.inl ℂ (M a) (M b))))) z.val = _
  rw [LieEnvelopingEquiv.map_comp, LieEnvelopingEquiv.map_comp]
  rfl

private theorem secondComplexBlockCenter_inclusion (z : Z b) :
    leviInclusion (a + b) a (secondComplexBlockCenter a b z).val =
      secondComplexMatrixBlockEnveloping a b z.val := by
  change leviInclusion (a + b) a
    (LieEnvelopingEquiv.enveloping (blockLeviLieEquiv a b)
      ((LieEnvelopingEquiv.envelopingProductCenter ℂ (M a) (M b)).symm (1 ⊗ₜ[ℂ] z)).val) = _
  rw [LieEnvelopingEquiv.envelopingProductCenter_symm_right_val]
  change ((LieEnvelopingEquiv.map (L).incl).comp
    ((LieEnvelopingEquiv.map (blockLeviLieEquiv a b).toLieHom).comp
      (LieEnvelopingEquiv.map (LieHom.inr ℂ (M a) (M b))))) z.val = _
  rw [LieEnvelopingEquiv.map_comp, LieEnvelopingEquiv.map_comp]
  rfl

private theorem blockCenter_projection_ideal (J : Ideal (Z (a + b))) (z : ZL)
    (hz : z ∈ J.map (blockLeviCenterProjection (a + b) a).toRingHom) :
    leviInclusion (a + b) a z.val ∈
      complexMatrixCentralIdealSpan (a + b) J ⊔ upperRadicalRightSpan (a + b) a := by
  let S := complexMatrixCentralIdealSpan (a + b) J ⊔ upperRadicalRightSpan (a + b) a
  have hS {x : U (a + b)} (hx : x ∈ S) (u : U (a + b)) : x * u ∈ S := by
    obtain ⟨x₁, h₁, x₂, h₂, rfl⟩ := Submodule.mem_sup.mp hx
    rw [add_mul]
    exact Submodule.mem_sup.mpr ⟨_, complexMatrixCentralIdealSpan_mul (a + b) J h₁ u,
      _, upperRadicalRightSpan_mul (a + b) a h₂ u, rfl⟩
  change leviInclusion (a + b) a z.val ∈ S
  rw [Ideal.map] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    change leviInclusion (a + b) a (blockLeviCenterProjection (a + b) a x).val ∈ S
    have h1 : x.val ∈ complexMatrixCentralIdealSpan (a + b) J :=
      Submodule.subset_span ⟨(⟨x, hx⟩, 1), mul_one _⟩
    have h2 := sub_leviInclusion_centerProjection_mem_upperSpan (a + b) a x
    rw [← sub_sub_cancel x.val (leviInclusion (a + b) a (blockLeviCenterProjection (a + b) a x).val)]
    exact S.sub_mem (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subalgebra.coe_add, map_add]
    exact S.add_mem hx hy
  | smul c x _ hx =>
    change leviInclusion (a + b) a (c * x).val ∈ S
    rw [mul_comm c x, Subalgebra.coe_mul, map_mul]
    exact hS hx _

/-- A cofinite ambient center ideal supplies a cofinite ideal in the first block center.
The embedded lower-rank ideal belongs to the sum of the original ideal span and the radical span. -/
theorem exists_firstComplexBlock_cofinite_ideal (J : Ideal (Z (a + b)))
    (hJ : Module.Finite ℂ (Z (a + b) ⧸ J)) :
    ∃ I : Ideal (Z a), Module.Finite ℂ (Z a ⧸ I) ∧
      ∀ z ∈ I, firstComplexMatrixBlockEnveloping a b z.val ∈
        complexMatrixCentralIdealSpan (a + b) J ⊔ upperRadicalRightSpan (a + b) a := by
  let JL := J.map (blockLeviCenterProjection (a + b) a).toRingHom
  have : Module.Finite ℂ (ZL ⧸ JL) :=
    quotientFinite_map _ (blockLeviCenterProjection_finite a b) J
  refine ⟨JL.comap (firstComplexBlockCenter a b).toRingHom, quotientFinite_comap _ JL, ?_⟩
  intro z hz
  rw [← firstComplexBlockCenter_inclusion]
  exact blockCenter_projection_ideal a b J _ hz

/-- The corresponding cofinite ideal and operator congruence for the second block. -/
theorem exists_secondComplexBlock_cofinite_ideal (J : Ideal (Z (a + b)))
    (hJ : Module.Finite ℂ (Z (a + b) ⧸ J)) :
    ∃ I : Ideal (Z b), Module.Finite ℂ (Z b ⧸ I) ∧
      ∀ z ∈ I, secondComplexMatrixBlockEnveloping a b z.val ∈
        complexMatrixCentralIdealSpan (a + b) J ⊔ upperRadicalRightSpan (a + b) a := by
  let JL := J.map (blockLeviCenterProjection (a + b) a).toRingHom
  have : Module.Finite ℂ (ZL ⧸ JL) :=
    quotientFinite_map _ (blockLeviCenterProjection_finite a b) J
  refine ⟨JL.comap (secondComplexBlockCenter a b).toRingHom, quotientFinite_comap _ JL, ?_⟩
  intro z hz
  rw [← secondComplexBlockCenter_inclusion]
  exact blockCenter_projection_ideal a b J _ hz

end Langlands.Archimedean.TwoBlockEnveloping
