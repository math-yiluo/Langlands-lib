import Langlands.AlgebraicGeometry.FiniteTypeDomainDimension
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.FiniteType

/-! # Noether normalization of a fibre with coordinates in the original algebra -/

universe u v

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

open Algebra TensorProduct
open P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen

private noncomputable def scalePolynomialVariables {k : Type u} [Field k]
    {ι : Type v} (a : ι → k) (ha : ∀ i, a i ≠ 0) :
    MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun i => a i • MvPolynomial.X i)
    (MvPolynomial.aeval fun i => (a i)⁻¹ • MvPolynomial.X i)
    (by ext i; simp [smul_smul, ha i])
    (by ext i; simp [smul_smul, ha i])

private theorem scalePolynomialVariables_X {k : Type u} [Field k]
    {ι : Type v} (a : ι → k) (ha : ∀ i, a i ≠ 0) (i : ι) :
    scalePolynomialVariables a ha (MvPolynomial.X i) = a i • MvPolynomial.X i := by
  simp [scalePolynomialVariables]

/-- A nonzero finite-type fibre admits finite injective normalization whose
coordinates are images of elements of the original algebra. -/
theorem exists_finite_injective_fiber_aeval
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime] [Nontrivial (p.Fiber S)] :
    ∃ n : ℕ, ∃ s : Fin n → S,
      let g := MvPolynomial.aeval (R := p.ResidueField) (fun i => (1 : p.ResidueField) ⊗ₜ[R] s i)
      Function.Injective g ∧ g.Finite ∧ ringKrullDim (p.Fiber S) = (n : WithBot ℕ∞) := by
  classical
  obtain ⟨n, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg p.ResidueField (p.Fiber S)
  choose r hr s hs using fun i : Fin n =>
    Ideal.Fiber.exists_smul_eq_one_tmul p (g (MvPolynomial.X i))
  let a : Fin n → p.ResidueField := fun i => algebraMap R p.ResidueField (r i)
  have ha (i : Fin n) : a i ≠ 0 := by
    exact fun h => hr i (Ideal.algebraMap_residueField_eq_zero.mp h)
  let e := scalePolynomialVariables a ha
  have he : g.comp e.toAlgHom =
      MvPolynomial.aeval (R := p.ResidueField) (fun i => (1 : p.ResidueField) ⊗ₜ[R] s i) := by
    ext i
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, MvPolynomial.aeval_X]
    rw [scalePolynomialVariables_X, map_smul]
    simpa only [a, algebraMap_smul] using hs i
  refine ⟨n, s, ?_⟩
  dsimp only
  rw [← he]
  have hfin' : (g.comp e.toAlgHom).Finite :=
    hfin.comp (RingHom.Finite.of_surjective _ e.surjective)
  have hinj' : Function.Injective (g.comp e.toAlgHom) := hinj.comp e.injective
  refine ⟨hinj', hfin', ?_⟩
  exact (ringKrullDim_eq_of_ringHom_isIntegral_of_injective
    (g.comp e.toAlgHom).toRingHom hfin'.to_isIntegral hinj').symm.trans
    (ringKrullDim_mvPolynomial_fin p.ResidueField n)

/-- Normalization coordinates in the original algebra, with their actual
finite injective residue-field polynomial map and dimension comparison. -/
structure FiberNormalizationCoordinates
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] where
  rank : ℕ
  coordinates : Fin rank → S
  injective : Function.Injective
    (MvPolynomial.aeval (R := p.ResidueField)
      (fun i => (1 : p.ResidueField) ⊗ₜ[R] coordinates i))
  finite : (MvPolynomial.aeval (R := p.ResidueField)
    (fun i => (1 : p.ResidueField) ⊗ₜ[R] coordinates i)).Finite
  dimension_eq : ringKrullDim (p.Fiber S) = (rank : WithBot ℕ∞)

/-- Choose proved normalization data for the actual nonzero finite-type fibre. -/
noncomputable def fiberNormalizationCoordinates
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime] [Nontrivial (p.Fiber S)] :
    FiberNormalizationCoordinates R S p :=
  Classical.choice <| by
    obtain ⟨n, s, hinj, hfin, hdim⟩ := exists_finite_injective_fiber_aeval R S p
    exact ⟨⟨n, s, hinj, hfin, hdim⟩⟩

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
