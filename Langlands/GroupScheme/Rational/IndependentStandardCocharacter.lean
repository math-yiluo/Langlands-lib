import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Torus.LatticeGalois
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Data.Rat.Cast.Order

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

private theorem exists_integer_dot_product_multiple {I : Type*} [Finite I]
    (f : (I → ℚ) →ₗ[ℚ] ℚ) :
    ∃ d : ℤ, 0 < d ∧ ∃ z : I → ℤ,
      ∀ x : I → ℤ, (∑ᶠ i, x i * z i : ℤ) = (d : ℚ) * f (fun i => (x i : ℚ)) := by
  classical
  let := Fintype.ofFinite I
  let q : I → ℚ := fun i => f (Pi.single i 1)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) q
  choose a ha using hb
  have hb0 : (b : ℤ) ≠ 0 := nonZeroDivisors.ne_zero b.property
  refine ⟨(b : ℤ) ^ 2, sq_pos_of_ne_zero hb0, fun i => (b : ℤ) * a i, ?_⟩
  intro x
  have hf : f (fun i => (x i : ℚ)) = ∑ i, (x i : ℚ) * q i := by
    conv_lhs => rw [← Finset.univ_sum_single (fun i => (x i : ℚ))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show Pi.single i (x i : ℚ) = (x i : ℚ) • Pi.single i (1 : ℚ) by
      ext j
      by_cases h : j = i <;> simp [h]]
    simp [q]
  have ha' (i : I) : (a i : ℚ) = (b : ℤ) * q i := by
    simpa [Algebra.smul_def, algebraMap_int_eq] using ha i
  rw [finsum_eq_sum_of_fintype, Int.cast_sum, hf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  rw [ha']
  ring

/-- A rational functional on the character lattice of a split torus is an
integer cocharacter pairing after multiplication by a positive integer. -/
theorem IsSplitTorus.exists_positive_multiple_pairing
    {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp)
    (f : (ℚ ⊗[ℤ] characterLattice T) →ₗ[ℚ] ℚ) :
    ∃ d : ℤ, 0 < d ∧ ∃ zeta : cocharacterLattice T,
      ∀ α : characterLattice T,
        (latticePairing T α zeta : ℚ) = (d : ℚ) * f (toRat α) := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := hI
  let := Fintype.ofFinite I
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  let eM := (characterLattice.congr eC).trans (splitTorus.characterLatticeEquiv k I)
  let eN := (cocharacterLattice.congr eC).trans (splitTorus.cocharacterLatticeEquiv k I)
  let eQ := tensorEquivPi eM
  obtain ⟨d, hd, z, hz⟩ := exists_integer_dot_product_multiple
    (f.comp eQ.symm.toLinearMap)
  refine ⟨d, hd, eN.symm z, fun α => ?_⟩
  have hpair : latticePairing T α (eN.symm z) = ∑ i, eM α i * z i := by
    rw [← latticePairing_congr eC, splitTorus.latticePairing_eq_sum]
    change (∑ i, eM α i * eN (eN.symm z) i) = _
    rw [AddEquiv.apply_symm_apply]
  rw [hpair]
  have h := hz (eM α)
  rw [finsum_eq_sum_of_fintype] at h
  convert h using 1
  change (d : ℚ) * f (toRat α) =
    (d : ℚ) * f (eQ.symm (fun i => (eM α i : ℚ)))
  congr 2
  rw [← tensorEquivPi_toRat eM, LinearEquiv.symm_apply_apply]

/-- Independent rationalized characters admit a cocharacter whose pairings are
any prescribed integer values multiplied by one positive integer. -/
theorem IsSplitTorus.exists_scaled_pairings
    {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) {A : Type v} (α : A → characterLattice T)
    (hα : LinearIndependent ℚ (fun a => toRat (α a))) (w : A → ℤ) :
    ∃ d : ℤ, 0 < d ∧ ∃ zeta : cocharacterLattice T,
      ∀ a, latticePairing T (α a) zeta = d * w a := by
  let V := ℚ ⊗[ℤ] characterLattice T
  let W : Submodule ℚ V := Submodule.span ℚ (Set.range (fun a => toRat (α a)))
  let f : V →ₗ[ℚ] ℚ :=
    Subspace.dualLift W ((Module.Basis.span hα).constr ℚ (fun a => (w a : ℚ)))
  have hf (a : A) : f (toRat (α a)) = w a := by
    dsimp only [f]
    rw [← Module.Basis.coe_span_apply hα a, Subspace.dualLift_of_subtype,
      Module.Basis.constr_basis]
  obtain ⟨d, hd, zeta, hzeta⟩ := hT.exists_positive_multiple_pairing f
  refine ⟨d, hd, zeta, fun a => ?_⟩
  have h := hzeta (α a)
  rw [hf] at h
  exact_mod_cast h

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Standard cocharacters exist if the rationalized simple relative roots are
independent. This is an intermediate result with its root hypothesis explicit. -/
theorem exists_standardCocharacter_of_linearIndependent
    (hT : IsSplitTorus T.toGrp)
    (hΔ : LinearIndependent ℚ
      (fun α : simpleRelativeRoots i ν => toRat (α : characterLattice T)))
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν) :
    ∃ zeta : cocharacterLattice T, IsStandardCocharacter i ν J zeta := by
  classical
  obtain ⟨d, hd, zeta, hzeta⟩ := hT.exists_scaled_pairings
    (fun α : simpleRelativeRoots i ν => (α : characterLattice T)) hΔ
    (fun α => if (α : characterLattice T) ∈ J then 0 else 1)
  refine ⟨zeta, hJ, ?_, ?_⟩
  · intro α hα
    simpa [hα] using hzeta ⟨α, hJ hα⟩
  · intro α hα hn
    have h := hzeta ⟨α, hα⟩
    simpa [hn, h] using hd

/-- A choice of standard cocharacter from independent rationalized simple roots. -/
def standardCocharacterOfIndependentRoots
    (hT : IsSplitTorus T.toGrp)
    (hΔ : LinearIndependent ℚ
      (fun α : simpleRelativeRoots i ν => toRat (α : characterLattice T)))
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν) :
    cocharacterLattice T :=
  (exists_standardCocharacter_of_linearIndependent i ν hT hΔ J hJ).choose

theorem standardCocharacterOfIndependentRoots_spec
    (hT : IsSplitTorus T.toGrp)
    (hΔ : LinearIndependent ℚ
      (fun α : simpleRelativeRoots i ν => toRat (α : characterLattice T)))
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν) :
    IsStandardCocharacter i ν J (standardCocharacterOfIndependentRoots i ν hT hΔ J hJ) :=
  (exists_standardCocharacter_of_linearIndependent i ν hT hΔ J hJ).choose_spec

end Langlands.GroupScheme
