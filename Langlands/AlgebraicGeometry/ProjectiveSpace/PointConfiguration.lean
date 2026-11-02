import Langlands.AlgebraicGeometry.ProjectiveSpace.PointLinearAction
import Langlands.AbelianScheme.PolarizedFiniteLevel.FiniteConfiguration

/-! # Fixed configurations of actual rational points -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

universe u v

variable {K : Type u} [Field K] (n : ℕ) {I : Type v}

/-- Count actual rational-point incidences with each nonzero linear polynomial. -/
def RationalPointHyperplaneBound
    (p : I → {p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n //
      p ≫ projectiveSpaceToSpec K n = 𝟙 _}) (q : ℕ) : Prop :=
  ∀ ℓ : (Fin (n + 1) → K) →ₗ[K] K, ℓ ≠ 0 →
    Nat.card {i : I //
      (linearFormPolynomialEquiv K n ℓ : ProjectiveCoordinateRing K n) ∈
        ((p i).1 (IsLocalRing.closedPoint K)).asHomogeneousIdeal} ≤ q

/-- The actual incidence bound is precisely the vector-space bound on coordinate lines. -/
theorem rationalPointHyperplaneBound_iff
    (p : I → {p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n //
      p ≫ projectiveSpaceToSpec K n = 𝟙 _}) (q : ℕ) :
    RationalPointHyperplaneBound n p q ↔
      Langlands.AbelianScheme.PolarizedFiniteLevel.HyperplaneBound
        (K := K) (fun i => (pointLineEmbedding n (p i)).rep) q := by
  unfold RationalPointHyperplaneBound
    Langlands.AbelianScheme.PolarizedFiniteLevel.HyperplaneBound
  have hinc (ℓ : (Fin (n + 1) → K) →ₗ[K] K) (i : I) :
      (linearFormPolynomialEquiv K n ℓ : ProjectiveCoordinateRing K n) ∈
        ((p i).1 (IsLocalRing.closedPoint K)).asHomogeneousIdeal ↔
      ℓ (pointLineEmbedding n (p i)).rep = 0 :=
    pointLine_linearForm_mem_iff n (p i).1 (p i).2 ℓ
  simp only [hinc]

/-- A sufficiently large configuration of fixed actual points forces a linear map to be scalar. -/
theorem scalar_of_fixes_rationalPointConfiguration [Fintype I]
    (p : I → {p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n //
      p ≫ projectiveSpaceToSpec K n = 𝟙 _}) {q : ℕ}
    (h : RationalPointHyperplaneBound n p q)
    (hsize : (n + 1) * q < Fintype.card I)
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (he : ∀ i, (p i).1 ≫ linearAction K n e = (p i).1) :
    ∃ a : K, e.toLinearMap = a • LinearMap.id := by
  have hbound := (rationalPointHyperplaneBound_iff n p q).mp h
  have hdim : 0 < Module.finrank K (Fin (n + 1) → K) := by simp
  have hsize' : Module.finrank K (Fin (n + 1) → K) * q < Fintype.card I := by
    simpa using hsize
  apply hbound.scalar_of_preserves_lines hdim hsize' e.toLinearMap
  intro i
  let v := pointLineEmbedding n (p i)
  have hline : Projectivization.map e.toLinearMap e.injective v = v := by
    rw [← pointLineEmbedding_linearActionPointEquiv]
    exact congrArg (pointLineEmbedding n) (Subtype.ext (he i))
  have hne : e v.rep ≠ 0 := by
    intro hz
    exact v.rep_nonzero (e.injective (by simpa using hz))
  have hmk : Projectivization.mk K (e v.rep) hne =
      Projectivization.mk K v.rep v.rep_nonzero := by
    have hmap : Projectivization.map e.toLinearMap e.injective v =
        Projectivization.mk K (e v.rep) hne := by
      simpa only [Projectivization.mk_rep, LinearEquiv.coe_coe] using
        Projectivization.map_mk e.toLinearMap e.injective v.rep v.rep_nonzero
    exact hmap.symm.trans (hline.trans (Projectivization.mk_rep v).symm)
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp hmk
  exact ⟨a, ha.symm⟩

/-- The scalar forced by a fixed configuration is a unit. -/
theorem unit_scalar_of_fixes_rationalPointConfiguration [Fintype I]
    (p : I → {p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n //
      p ≫ projectiveSpaceToSpec K n = 𝟙 _}) {q : ℕ}
    (h : RationalPointHyperplaneBound n p q)
    (hsize : (n + 1) * q < Fintype.card I)
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (he : ∀ i, (p i).1 ≫ linearAction K n e = (p i).1) :
    ∃ a : Kˣ, e = LinearEquiv.smulOfUnit a := by
  obtain ⟨a, ha⟩ := scalar_of_fixes_rationalPointConfiguration n p h hsize e he
  have hne : a ≠ 0 := by
    intro hz
    have hev : e (fun _ => 1) = 0 := by
      simpa [hz] using LinearMap.congr_fun ha (fun _ => 1)
    have hv : (fun _ : Fin (n + 1) => (1 : K)) = 0 :=
      e.injective (by simpa using hev)
    have h01 := congrFun hv 0
    simp at h01
  refine ⟨Units.mk0 a hne, LinearEquiv.toLinearMap_injective ?_⟩
  rw [smulOfUnit_toLinearMap]
  exact ha

/-- Under the incidence and size bounds, fixing the configuration fixes the actual scheme. -/
theorem linearAction_eq_id_of_fixes_rationalPointConfiguration [Fintype I]
    (p : I → {p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n //
      p ≫ projectiveSpaceToSpec K n = 𝟙 _}) {q : ℕ}
    (h : RationalPointHyperplaneBound n p q)
    (hsize : (n + 1) * q < Fintype.card I)
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (he : ∀ i, (p i).1 ≫ linearAction K n e = (p i).1) :
    linearAction K n e = 𝟙 (ProjectiveSpace K n) := by
  obtain ⟨a, rfl⟩ := unit_scalar_of_fixes_rationalPointConfiguration n p h hsize e he
  exact linearAction_smulOfUnit K n a

/-- An equivariant monomorphism transfers fixed-configuration rigidity to its source. -/
theorem eq_id_of_fixes_embedded_rationalPointConfiguration [Fintype I]
    {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of K))
    (i : X ⟶ ProjectiveSpace K n) [Mono i]
    (hi : i ≫ projectiveSpaceToSpec K n = π)
    (p : I → {p : Spec (CommRingCat.of K) ⟶ X // p ≫ π = 𝟙 _})
    {q : ℕ}
    (h : RationalPointHyperplaneBound n
      (fun j => ⟨(p j).1 ≫ i, by rw [Category.assoc, hi, (p j).2]⟩) q)
    (hsize : (n + 1) * q < Fintype.card I)
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (f : X ⟶ X) (he : f ≫ i = i ≫ linearAction K n e)
    (hf : ∀ j, (p j).1 ≫ f = (p j).1) :
    f = 𝟙 X := by
  have haction : linearAction K n e = 𝟙 (ProjectiveSpace K n) := by
    apply linearAction_eq_id_of_fixes_rationalPointConfiguration n _ h hsize e
    intro j
    change ((p j).1 ≫ i) ≫ linearAction K n e = (p j).1 ≫ i
    rw [Category.assoc, ← he, ← Category.assoc, hf]
  apply (cancel_mono i).mp
  rw [he, haction, Category.comp_id, Category.id_comp]

end Langlands.AlgebraicGeometry.ProjectiveSpace
