import Langlands.AlgebraicGeometry.ProjectiveSpace.Charts
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Flatness of polynomial projective space over its base

Each standard chart algebra of `ProjectiveSpace R n` is a polynomial algebra over `R` in the
ratios `X k / X j`, `k ≠ j`. Hence the structure morphism is flat and locally of finite
presentation.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (n : ℕ) (j : Fin (n + 1))

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- The polynomial map sending the variable `Y k` to the ratio `X k / X j`. -/
def chartPolynomialMap :
    MvPolynomial {k : Fin (n + 1) // k ≠ j} R →ₐ[R] Away 𝒜 (MvPolynomial.X j) :=
  MvPolynomial.aeval fun k => _root_.AlgebraicGeometry.ProjSpace.ratio R n j k.1

/-- Dehomogenisation at `X j = 1`, on all polynomials. -/
def dehomogenize :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial {k : Fin (n + 1) // k ≠ j} R :=
  MvPolynomial.aeval fun k => if h : k = j then 1 else MvPolynomial.X ⟨k, h⟩

lemma dehomogenize_X_self : dehomogenize R n j (MvPolynomial.X j) = 1 := by
  simp [dehomogenize]

lemma isUnit_dehomogenize_X_self :
    IsUnit ((dehomogenize R n j).toRingHom (MvPolynomial.X j)) := by
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, dehomogenize_X_self]
  exact isUnit_one

/-- Dehomogenisation, on the localization away from `X j`. -/
def dehomogenizeLoc :
    Localization.Away (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) →+*
      MvPolynomial {k : Fin (n + 1) // k ≠ j} R :=
  IsLocalization.Away.lift (R := MvPolynomial (Fin (n + 1)) R)
    (S := Localization.Away (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R))
    (MvPolynomial.X j) (isUnit_dehomogenize_X_self R n j)

/-- Dehomogenisation, on the degree-zero localization away from `X j`. -/
def chartInverse :
    Away 𝒜 (MvPolynomial.X j) →+* MvPolynomial {k : Fin (n + 1) // k ≠ j} R :=
  (dehomogenizeLoc R n j).comp
    (algebraMap (Away 𝒜 (MvPolynomial.X j)) (Localization.Away (MvPolynomial.X j)))

lemma chartInverse_apply (z : Away 𝒜 (MvPolynomial.X j)) :
    chartInverse R n j z = dehomogenizeLoc R n j z.val := rfl

lemma dehomogenizeLoc_algebraMap (a : MvPolynomial (Fin (n + 1)) R) :
    dehomogenizeLoc R n j (algebraMap _ _ a) = dehomogenize R n j a := by
  rw [dehomogenizeLoc, IsLocalization.Away.lift_eq]
  rfl

lemma chartInverse_comp :
    (chartInverse R n j).comp (chartPolynomialMap R n j).toRingHom = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← MvPolynomial.algebraMap_eq,
      AlgHom.commutes, RingHom.id_apply, chartInverse_apply,
      _root_.AlgebraicGeometry.ProjSpace.val_algebraMap, dehomogenizeLoc_algebraMap]
    simp [dehomogenize]
  · intro k
    rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.id_apply,
      chartPolynomialMap, MvPolynomial.aeval_X, chartInverse_apply,
      _root_.AlgebraicGeometry.ProjSpace.ratio, Away.val_mk, Localization.mk_eq_mk',
      dehomogenizeLoc, IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]
    simp [dehomogenize, k.2]

lemma chartPolynomialMap_bijective : Function.Bijective (chartPolynomialMap R n j) := by
  constructor
  · refine Function.LeftInverse.injective (g := chartInverse R n j) fun a => ?_
    exact congrArg (fun F => F a) (chartInverse_comp R n j)
  · rw [← AlgHom.range_eq_top, eq_top_iff]
    intro z _
    have hz : z ∈ Algebra.adjoin R
        (Set.range (_root_.AlgebraicGeometry.ProjSpace.ratio R n j)) := by
      rw [_root_.AlgebraicGeometry.ProjSpace.adjoin_range_ratio R n j]
      trivial
    refine (Algebra.adjoin_le ?_ : Algebra.adjoin R _ ≤ (chartPolynomialMap R n j).range) hz
    rintro _ ⟨k, rfl⟩
    by_cases hk : k = j
    · subst hk
      rw [_root_.AlgebraicGeometry.ProjSpace.ratio_self]
      exact Subalgebra.one_mem _
    · exact ⟨MvPolynomial.X ⟨k, hk⟩, by simp [chartPolynomialMap]⟩

/-- The standard chart algebra is the polynomial algebra in the ratios `X k / X j`. -/
def chartEquiv :
    MvPolynomial {k : Fin (n + 1) // k ≠ j} R ≃ₐ[R] Away 𝒜 (MvPolynomial.X j) :=
  AlgEquiv.ofBijective _ (chartPolynomialMap_bijective R n j)

instance flat_away : Module.Flat R (Away 𝒜 (MvPolynomial.X j)) :=
  Module.Flat.of_linearEquiv (chartEquiv R n j).symm.toLinearEquiv

instance finitePresentation_away :
    Algebra.FinitePresentation R (Away 𝒜 (MvPolynomial.X j)) :=
  Algebra.FinitePresentation.equiv (chartEquiv R n j)

instance flat_projectiveSpaceToSpec : Flat (projectiveSpaceToSpec R n) := by
  show Flat (_root_.AlgebraicGeometry.ProjSpace.π R n)
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat.{u})
  refine IsZariskiLocalAtSource.of_openCover (P := @Flat.{u})
    (_root_.AlgebraicGeometry.ProjSpace.affineOpenCover R n).openCover fun (j : Fin (n + 1)) => ?_
  have hf : Flat (Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜 (MvPolynomial.X j))))) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  rw [← _root_.AlgebraicGeometry.ProjSpace.awayι_comp_π R n j] at hf
  exact hf

instance locallyOfFinitePresentation_projectiveSpaceToSpec :
    LocallyOfFinitePresentation (projectiveSpaceToSpec R n) := by
  show LocallyOfFinitePresentation (_root_.AlgebraicGeometry.ProjSpace.π R n)
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation.{u})
  refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation.{u})
    (_root_.AlgebraicGeometry.ProjSpace.affineOpenCover R n).openCover fun (j : Fin (n + 1)) => ?_
  have hf : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜 (MvPolynomial.X j))))) := by
    rw [LocallyOfFinitePresentation.SpecMap_iff]
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  rw [← _root_.AlgebraicGeometry.ProjSpace.awayι_comp_π R n j] at hf
  exact hf

end Langlands.AlgebraicGeometry.ProjectiveSpace
