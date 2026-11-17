import Langlands.GroupScheme.Rational.CrossTorusLieTransport
import Langlands.GroupScheme.Torus.ExponentCharacters

/-! # Unit discrepancies between aligned actual weight lines -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Algebra

variable {R : Type u} [CommRing R]

/-- A linear automorphism of the coefficient ring is multiplication by a unit. -/
def linearAutUnit (e : R ≃ₗ[R] R) : Rˣ where
  val := e 1
  inv := e.symm 1
  val_inv := by
    rw [mul_comm, ← smul_eq_mul, ← e.map_smul]
    simp
  inv_val := by
    rw [← smul_eq_mul, ← e.map_smul]
    simp

@[simp] theorem linearAutUnit_coe (e : R ≃ₗ[R] R) :
    (linearAutUnit e : R) = e 1 := rfl

/-- The chosen unit computes the automorphism at every coefficient. -/
theorem linearAutUnit_apply (e : R ≃ₗ[R] R) (a : R) :
    e a = (linearAutUnit e : R) * a := by
  rw [linearAutUnit_coe, mul_comm, ← smul_eq_mul, ← e.map_smul]
  simp

/-- Two chosen generators of a line, compared by a linear isomorphism, differ
by a unique unit, without a local-ring or nonzero-ring assumption. -/
theorem existsUnique_unit_smul_of_lineEquiv
    {L K : Type u} [AddCommGroup L] [Module R L] [AddCommGroup K] [Module R K]
    (X : R ≃ₗ[R] L) (Y : R ≃ₗ[R] K) (E : L ≃ₗ[R] K) :
    ∃! c : Rˣ, E (X 1) = (c : R) • Y 1 := by
  let e := (X.trans E).trans Y.symm
  refine ⟨linearAutUnit e, ?_, ?_⟩
  · apply Y.symm.injective
    rw [Y.symm.map_smul, Y.symm_apply_apply, smul_eq_mul, mul_one]
    rfl
  · intro c hc
    apply Units.ext
    have h := congrArg Y.symm hc
    rw [Y.symm.map_smul, Y.symm_apply_apply, smul_eq_mul, mul_one] at h
    exact h.symm

end Langlands.Algebra

namespace Langlands.GroupScheme.splitTorus

variable {R : Type u} [CommRing R]
  {I J : Type u} [Fintype I] [Fintype J]
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {j : splitTorus (Spec (CommRingCat.of R)) J ⟶ H}
  (τ : commGroupScheme (Spec (CommRingCat.of R)) I ≅
    commGroupScheme (Spec (CommRingCat.of R)) J)
  (Φ : G ≅ H) (h : i ≫ Φ.hom = CommGroupScheme.groupHom τ.hom ≫ j)
  (m : I → ℤ) (n : J → ℤ)
  (hχ : characterLattice.congr τ (exponentCharacter (Spec (CommRingCat.of R)) I m) =
    exponentCharacter (Spec (CommRingCat.of R)) J n)

/-- An actual torus square and actual character alignment give a linear
isomorphism of the corresponding exponent weight modules over any ring. -/
def exponentWeightTransportEquiv :
    exponentWeightSpace I G i m ≃ₗ[R] exponentWeightSpace J H j n where
  toFun x := ⟨Lie.targetMapLinear Φ.hom R x.val, by
    rw [exponentWeightSpace_eq_weightSpace_exponentCharacter, ← hχ]
    apply lieKernelHomLinear_mem_weightSpace_of_transport τ Φ.hom h
    rw [← exponentWeightSpace_eq_weightSpace_exponentCharacter]
    exact x.property⟩
  invFun y := ⟨Lie.targetMapLinear Φ.inv R y.val, by
    rw [exponentWeightSpace_eq_weightSpace_exponentCharacter]
    apply (lieKernelHomLinear_mem_weightSpace_transport_iff τ Φ h _ _).mp
    rw [Lie.targetMapLinear_inv_hom, hχ, ← exponentWeightSpace_eq_weightSpace_exponentCharacter]
    exact y.property⟩
  left_inv x := Subtype.ext (Lie.targetMapLinear_hom_inv Φ R x.val)
  right_inv y := Subtype.ext (Lie.targetMapLinear_inv_hom Φ R y.val)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_smul' a x := Subtype.ext (map_smul _ a x.val)

@[simp] theorem exponentWeightTransportEquiv_apply
    (x : exponentWeightSpace I G i m) :
    (exponentWeightTransportEquiv τ Φ h m n hχ x : Additive (lieKernel H R)) =
      Lie.targetMapLinear Φ.hom R x.val := rfl

include h hχ in
/-- Aligned trivialized actual weight lines have a unique unit discrepancy
under the actual differential, over every commutative coefficient ring. -/
theorem existsUnique_unit_smul_of_aligned_weightLines
    (X : R ≃ₗ[R] exponentWeightSpace I G i m)
    (Y : R ≃ₗ[R] exponentWeightSpace J H j n) :
    ∃! c : Rˣ, Lie.targetMapLinear Φ.hom R (X 1).val = (c : R) • (Y 1).val := by
  obtain ⟨c, hc, huniq⟩ := Langlands.Algebra.existsUnique_unit_smul_of_lineEquiv X Y
    (exponentWeightTransportEquiv τ Φ h m n hχ)
  refine ⟨c, congrArg Subtype.val hc, fun d hd => huniq d ?_⟩
  exact Subtype.ext hd

end Langlands.GroupScheme.splitTorus
