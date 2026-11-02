import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.LinearAction

/-! # Coefficient base change for actual projective linear actions -/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K R A : Type u} [CommRing K] [CommRing R] [CommRing A] (n : ℕ)

/-- The existing polynomial-Proj coefficient map, with its ring homomorphism explicit. -/
def coefficientMap (φ : K →+* R) : ProjectiveSpace R n ⟶ ProjectiveSpace K n :=
  letI := φ.toAlgebra
  ProjSpace.map K R n

@[simp]
lemma coefficientMap_id :
    coefficientMap n (RingHom.id K) = 𝟙 (ProjectiveSpace K n) := by
  unfold coefficientMap ProjSpace.map
  have h : @ProjSpace.mvMapGraded K _ K _ (RingHom.id K).toAlgebra n =
      GradedRingHom.id (projectiveSpaceGrading K n) := by
    apply GradedRingHom.ext
    intro x
    change MvPolynomial.map (RingHom.id K) x = x
    rw [MvPolynomial.map_id]
  change Proj.map _ _ = 𝟙 (Proj (projectiveSpaceGrading K n))
  simpa only [h] using (Proj.map_id (𝒜 := projectiveSpaceGrading K n))

/-- Coefficient maps compose contravariantly in their ring homomorphisms. -/
lemma coefficientMap_comp (φ : K →+* R) (ψ : R →+* A) :
    coefficientMap n (ψ.comp φ) = coefficientMap n ψ ≫ coefficientMap n φ := by
  unfold coefficientMap ProjSpace.map
  rw [← Proj.map_comp]
  congr 1
  apply GradedRingHom.ext
  intro x
  change MvPolynomial.map (ψ.comp φ) x = MvPolynomial.map ψ (MvPolynomial.map φ x)
  rw [MvPolynomial.map_map]

@[reassoc (attr := simp)]
lemma coefficientMap_toSpec (φ : K →+* R) :
    coefficientMap n φ ≫ projectiveSpaceToSpec K n =
      projectiveSpaceToSpec R n ≫ Spec.map (CommRingCat.ofHom φ) := by
  let := φ.toAlgebra
  exact (ProjSpace.isPullback_map K R n).w

@[reassoc (attr := simp)]
lemma coefficientMap_toIntegral (φ : K →+* R) :
    coefficientMap n φ ≫ RelativeProjectiveSpace.polynomialToIntegral K n =
      RelativeProjectiveSpace.polynomialToIntegral R n := by
  change coefficientMap n φ ≫
      coefficientMap n ((Int.castRingHom K).comp ULift.ringEquiv.toRingHom) =
    coefficientMap n ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom)
  rw [← coefficientMap_comp]
  congr 1
  ext z
  simp

/-- Projective linear actions commute with coefficient maps whenever the
specified linear equivalences have matching matrix coefficients. -/
lemma coefficientMap_linearAction (φ : K →+* R)
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (e' : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R))
    (hcoeff : ∀ i j, φ (e (Pi.single j 1) i) = e' (Pi.single j 1) i) :
    coefficientMap n φ ≫ linearAction K n e =
      linearAction R n e' ≫ coefficientMap n φ := by
  let := φ.toAlgebra
  have hring : (MvPolynomial.map φ).comp (linearSubstitution K n e.toLinearMap).toRingHom =
      (linearSubstitution R n e'.toLinearMap).toRingHom.comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp [linearFormPolynomialEquiv_coe, MvPolynomial.smul_eq_C_mul, hcoeff]
  have hgraded :
      (ProjSpace.mvMapGraded K R n).comp (gradedLinearSubstitution K n e.toLinearMap) =
        (gradedLinearSubstitution R n e'.toLinearMap).comp (ProjSpace.mvMapGraded K R n) := by
    apply GradedRingHom.ext
    intro x
    exact DFunLike.congr_fun hring x
  unfold coefficientMap ProjSpace.map linearAction
  rw [← Proj.map_comp, ← Proj.map_comp]
  congr 1

end Langlands.AlgebraicGeometry.ProjectiveSpace

namespace Langlands.AlgebraicGeometry.RelativeProjectiveSpace

set_option backward.isDefEq.respectTransparency false

variable {K R : Type u} [CommRing K] [CommRing R]
  {S T : Scheme.{u}} {n : ℕ}

/-- The polynomial projections for two coefficient rings agree through their
coefficient map whenever the base maps do. -/
lemma toPolynomial_coefficientMap (a : S ⟶ Spec (CommRingCat.of K))
    (b : S ⟶ Spec (CommRingCat.of R)) (φ : K →+* R)
    (w : b ≫ Spec.map (CommRingCat.ofHom φ) = a) :
    toPolynomial n b ≫ ProjectiveSpace.coefficientMap n φ = toPolynomial n a := by
  apply (cancel_mono (affineComparisonIso K n).hom).mp
  apply hom_ext
  · simp [w]
  · simp

/-- Relative actions agree after changing coefficient rings and mapping every
matrix coefficient by the specified ring homomorphism. -/
lemma linearAction_coefficientMap (a : S ⟶ Spec (CommRingCat.of K))
    (b : S ⟶ Spec (CommRingCat.of R)) (φ : K →+* R)
    (w : b ≫ Spec.map (CommRingCat.ofHom φ) = a)
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (e' : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R))
    (hcoeff : ∀ i j, φ (e (Pi.single j 1) i) = e' (Pi.single j 1) i) :
    linearAction a e = linearAction b e' := by
  have hp := toPolynomial_coefficientMap (n := n) a b φ w
  apply hom_ext_toPolynomial a
  · simp
  · calc
      linearAction a e ≫ toPolynomial n a =
          toPolynomial n a ≫ ProjectiveSpace.linearAction K n e := by simp
      _ = toPolynomial n b ≫ ProjectiveSpace.coefficientMap n φ ≫
          ProjectiveSpace.linearAction K n e := by rw [← hp, Category.assoc]
      _ = toPolynomial n b ≫ ProjectiveSpace.linearAction R n e' ≫
          ProjectiveSpace.coefficientMap n φ := by
        rw [ProjectiveSpace.coefficientMap_linearAction n φ e e' hcoeff]
      _ = linearAction b e' ≫ toPolynomial n a := by
        rw [← hp, linearAction_toPolynomial_assoc]

/-- The actual relative action commutes with a scheme-base morphism and a
simultaneous coefficient-ring change. -/
lemma map_linearAction_coefficientMap (a : S ⟶ Spec (CommRingCat.of K))
    (b : T ⟶ Spec (CommRingCat.of R)) (f : T ⟶ S) (φ : K →+* R)
    (w : b ≫ Spec.map (CommRingCat.ofHom φ) = f ≫ a)
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (e' : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R))
    (hcoeff : ∀ i j, φ (e (Pi.single j 1) i) = e' (Pi.single j 1) i) :
    map n f ≫ linearAction a e = linearAction b e' ≫ map n f := by
  rw [map_linearAction,
    linearAction_coefficientMap (f ≫ a) b φ w e e' hcoeff]

end Langlands.AlgebraicGeometry.RelativeProjectiveSpace
