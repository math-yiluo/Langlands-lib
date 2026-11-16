import Langlands.GroupScheme.Reductive.LocalRootParametrizationRigidity
import Mathlib.RingTheory.Ideal.Nonunits

/-! # Prescribed-power rigidity over arbitrary coefficient rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.NaturalLine

variable {R : CommRingCat.{u}}

/-- The value of a natural operation at one Laurent monomial has degree `d*q`. -/
def Operation.HasLaurentPower (F : Operation R) (d q : ℕ) : Prop :=
  F.app (CommAlgCat.of R (LaurentPolynomial R)) (LaurentPolynomial.T (d : ℤ)) =
    LaurentPolynomial.T ((d : ℤ) * (q : ℤ)) *
      LaurentPolynomial.C (F.app (CommAlgCat.of R R) 1)

/-- One positive Laurent substitution determines a prescribed power formula. -/
theorem Operation.eq_mul_pow_of_laurent {d q : ℕ} (hd : 0 < d) (F : Operation R)
    (hweight : F.HasLaurentPower d q) (A : CommAlgCat.{u} R) (a : A) :
    F.app A a = algebraMap R A (F.app (CommAlgCat.of R R) 1) * a ^ q := by
  let P := F.app (CommAlgCat.of R R[X]) Polynomial.X
  have hP : P = Polynomial.C (F.app (CommAlgCat.of R R) 1) * Polynomial.X ^ q := by
    apply powerEvaluation_injective hd
    have h := F.naturality (CommAlgCat.ofHom (powerEvaluation (R := R) d)) Polynomial.X
    change F.app (CommAlgCat.of R (LaurentPolynomial R))
      (powerEvaluation d Polynomial.X) = powerEvaluation d P at h
    rw [powerEvaluation, Polynomial.aeval_X] at h
    rw [Operation.HasLaurentPower] at hweight
    rw [hweight] at h
    unfold powerEvaluation
    rw [← h]
    simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
      LaurentPolynomial.T_pow]
    rw [mul_comm (q : ℤ) (d : ℤ)]
    exact mul_comm _ _
  have h := F.naturality (CommAlgCat.ofHom (Polynomial.aeval a : R[X] →ₐ[R] A)) Polynomial.X
  change F.app A ((Polynomial.aeval a) Polynomial.X) = (Polynomial.aeval a) P at h
  rw [Polynomial.aeval_X, hP, map_mul, map_pow, Polynomial.aeval_C,
    Polynomial.aeval_X] at h
  exact h

/-- Within a fixed positive Laurent weight and power, the value at one determines
the operation on every algebra. -/
theorem Operation.eq_of_laurent_value_one {d q : ℕ} (hd : 0 < d)
    {F H : Operation R} (hF : F.HasLaurentPower d q) (hH : H.HasLaurentPower d q)
    (h1 : F.app (CommAlgCat.of R R) 1 = H.app (CommAlgCat.of R R) 1)
    (A : CommAlgCat.{u} R) (a : A) : F.app A a = H.app A a := by
  rw [F.eq_mul_pow_of_laurent hd hF, H.eq_mul_pow_of_laurent hd hH, h1]

/-- Nonvanishing at one on every field algebra makes the base coefficient a unit.
This does not claim that field points detect equality of operations. -/
theorem Operation.isUnit_value_one_of_fields (F : Operation R)
    (hF : ∀ (K : Type u) [Field K] [Algebra R K],
      F.app (CommAlgCat.of R K) 1 ≠ 0) :
    IsUnit (F.app (CommAlgCat.of R R) 1) := by
  by_contra hc
  obtain ⟨m, hm, hcm⟩ := exists_max_ideal_of_mem_nonunits hc
  let : m.IsMaximal := hm
  let K := R ⧸ m
  let : Field K := Ideal.Quotient.field m
  have hn := F.naturality
    (CommAlgCat.ofHom (Algebra.ofId R K)) (1 : R)
  change F.app (CommAlgCat.of R K) (algebraMap R K 1) =
    algebraMap R K (F.app (CommAlgCat.of R R) 1) at hn
  rw [map_one] at hn
  apply hF K
  rw [hn]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hcm

end Langlands.GroupScheme.NaturalLine

namespace Langlands.GroupScheme.LocalSplitCell

open Corepresented.RingCoordinates

variable {R : Type u} [CommRing R]

/-- The coefficient operations on all algebras detect equality of actual maps. -/
theorem scalarOperation_ext {f F : Ga R ⟶ Ga R}
    (h : ∀ (A : CommAlgCat.{u} (CommRingCat.of R)) (a : A),
      (scalarOperation f).app A a = (scalarOperation F).app A a) : f = F := by
  have H : f.hom.hom = F.hom.hom := by
    let A : CommAlgCat.{u} (CommRingCat.of R) :=
      CommAlgCat.of R (MvPolynomial (Fin 1) R)
    let Z := specOver (CommRingCat.of R) A
    have hZ : Z = (Ga R).X := rfl
    let a := (Scheme.ΓSpecIso (CommRingCat.of A)).hom (gaCoord (𝟙 (Ga R).X))
    have ha : VectorGroup.scalarPoint (CommRingCat.of R) Z
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) = 𝟙 (Ga R).X := by
      rw [show (Scheme.ΓSpecIso (CommRingCat.of A)).inv a = gaCoord (𝟙 (Ga R).X)
        from Iso.hom_inv_id_apply _ _]
      exact VectorGroup.scalarPoint_coordinate _ _
    have hf := h A a
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (gaCoord (VectorGroup.scalarPoint (CommRingCat.of R) Z
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) ≫ f.hom.hom)) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (gaCoord (VectorGroup.scalarPoint (CommRingCat.of R) Z
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) ≫ F.hom.hom)) at hf
    rw [ha] at hf
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (gaCoord ((𝟙 (Ga R).X) ≫ f.hom.hom)) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (gaCoord ((𝟙 (Ga R).X) ≫ F.hom.hom)) at hf
    rw [Category.id_comp, Category.id_comp] at hf
    apply VectorGroup.points_ext
    intro j
    rw [Subsingleton.elim j 0]
    exact (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective hf
  apply hom_ext_points
  intro Z a
  rw [H]

/-- Postcomposition with scaling multiplies the coefficient operation. -/
theorem scalarOperation_comp_scaleHom (f : Ga R ⟶ Ga R) (c : R)
    (A : CommAlgCat.{u} (CommRingCat.of R)) (a : A) :
    (scalarOperation (f ≫ scaleHom c)).app A a =
      algebraMap R A c * (scalarOperation f).app A a := by
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    (gaCoord (VectorGroup.scalarPoint (CommRingCat.of R)
      (specOver (CommRingCat.of R) A)
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) ≫
      (f ≫ scaleHom c).hom.hom)) = _
  rw [Grp.comp_hom_hom, ← Category.assoc]
  rw [comp_scaleHom, gaCoord, VectorGroup.coordinates_scalarPoint, map_mul,
    gamma_baseScalar]
  rfl

section Weight

variable {I : Type u} [Fintype I]

/-- A character action of prescribed degree forces a power formula for the
actual additive-group map on every coefficient algebra. -/
theorem hasLaurentPower_of_weight (m ν : I → ℤ) {d : ℕ} {q : ℕ}
    (hpair : ∑ j, m j * ν j = (d : ℤ)) (f : Ga R ⟶ Ga R)
    (hf : ∀ (Z : Over (Spec (CommRingCat.of R)))
      (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (c : Γ(Z.left, ⊤)),
      rootPoint f Z (VectorGroup.charValue
        (splitTorus.exponentCharacter _ I m) Z t * c) =
      VectorGroup.scalarPoint _ Z (VectorGroup.charValue
        (splitTorus.exponentCharacter _ I m) Z t ^ q * gaCoord (rootPoint f Z c))) :
    (scalarOperation f).HasLaurentPower d q := by
  let F := scalarOperation f
  let A : CommAlgCat.{u} (CommRingCat.of R) :=
    CommAlgCat.of R (LaurentPolynomial R)
  let t : specOver (CommRingCat.of R) A ⟶
      (splitTorus (Spec (CommRingCat.of R)) I).X :=
    Corepresented.torusPt I A (fun j =>
      unitOfInvertible (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial R) ^ ν j)
  have ht : (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (VectorGroup.charValue (splitTorus.exponentCharacter _ I m)
        (specOver (CommRingCat.of R) A) t) =
      LaurentPolynomial.T (d : ℤ) := by
    rw [Corepresented.charValue_torusPt, exponentValue_laurent, hpair]
  have hx : VectorGroup.charValue (splitTorus.exponentCharacter _ I m)
      (specOver (CommRingCat.of R) A) t =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (LaurentPolynomial.T (d : ℤ)) := by
    apply (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom _ =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom _
    rw [ht, Iso.inv_hom_id_apply]
  have hw := hf (specOver (CommRingCat.of R) A) t 1
  rw [mul_one, hx] at hw
  have H := congrArg (fun a => (Scheme.ΓSpecIso (CommRingCat.of A)).hom (gaCoord a)) hw
  simp only [gaCoord, VectorGroup.coordinates_scalarPoint, map_mul, map_pow,
    Iso.inv_hom_id_apply] at H
  have H' : F.app A (LaurentPolynomial.T (d : ℤ)) =
      (LaurentPolynomial.T (d : ℤ) : LaurentPolynomial R) ^ q * F.app A 1 := by
    simpa only [F, scalarOperation, rootPoint, gaCoord, map_one] using H
  rw [LaurentPolynomial.T_pow, mul_comm (q : ℤ) (d : ℤ)] at H'
  have hn := F.naturality
    (CommAlgCat.ofHom (Algebra.ofId R (LaurentPolynomial R))) (1 : R)
  change F.app A (algebraMap R A 1) =
    algebraMap R A (F.app (CommAlgCat.of R R) 1) at hn
  rw [map_one] at hn
  rw [hn] at H'
  exact H'

end Weight

/-- Two prescribed-power maps with unit coefficients differ by a unique
postcomposition scaling. Both hypotheses concern every coefficient algebra. -/
theorem existsUnique_unit_scale_of_power {f F : Ga R ⟶ Ga R} {q : ℕ}
    (c c' : Rˣ)
    (hf : ∀ (A : CommAlgCat.{u} (CommRingCat.of R)) (a : A),
      (scalarOperation f).app A a = algebraMap R A (c : R) * a ^ q)
    (hF : ∀ (A : CommAlgCat.{u} (CommRingCat.of R)) (a : A),
      (scalarOperation F).app A a = algebraMap R A (c' : R) * a ^ q) :
    ∃! b : Rˣ, f = F ≫ scaleHom (b : R) := by
  refine ⟨c * c'⁻¹, ?_, ?_⟩
  · apply scalarOperation_ext
    intro A a
    rw [hf, scalarOperation_comp_scaleHom, hF]
    simp only [Units.val_mul, map_mul]
    have hi : algebraMap R A (↑c'⁻¹ : R) * algebraMap R A (c' : R) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    calc
      algebraMap R A (c : R) * a ^ q =
          algebraMap R A (c : R) * (1 * a ^ q) := by rw [one_mul]
      _ = (algebraMap R A (c : R) * algebraMap R A (↑c'⁻¹ : R)) *
          (algebraMap R A (c' : R) * a ^ q) := by rw [← hi]; ring
  · intro b hb
    have h := congrArg (fun h => (scalarOperation h).app (CommAlgCat.of R R) 1) hb
    rw [hf, scalarOperation_comp_scaleHom, hF] at h
    simp only [Algebra.algebraMap_self, RingHom.id_apply, one_pow, mul_one] at h
    apply Units.ext
    change (b : R) = (c : R) * (↑c'⁻¹ : R)
    calc
      (b : R) = ((b : R) * (c' : R)) * (↑c'⁻¹ : R) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
      _ = (c : R) * (↑c'⁻¹ : R) := by rw [← h]

end Langlands.GroupScheme.LocalSplitCell
