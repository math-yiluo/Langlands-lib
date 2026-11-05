import Langlands.GroupScheme.Rational.AnisotropicTorusCompactness
import Mathlib.RingTheory.Norm.Transitivity

/-! # Spectral valuations of anisotropic torus character values -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.LocalGalois

variable {F : Type u} [NontriviallyNormedField F] [IsUltrametricDist F]
  [CompleteSpace F] {E : Type v} [Field E] [Algebra F E]
  [FiniteDimensional F E] [IsGalois F E]

/-- Galois invariance of the spectral norm turns the field norm into a power. -/
theorem spectralNorm_pow_card_galois (x : E) :
    spectralNorm F E x ^ Fintype.card (E ≃ₐ[F] E) = ‖Algebra.norm F x‖ := by
  classical
  calc
    spectralNorm F E x ^ Fintype.card (E ≃ₐ[F] E) =
        ∏ σ : E ≃ₐ[F] E, spectralMulAlgNorm F E (σ x) := by
          simp only [spectralMulAlgNorm_def, ← spectralNorm_eq_of_equiv, Finset.prod_const,
            Finset.card_univ]
    _ = spectralMulAlgNorm F E (∏ σ : E ≃ₐ[F] E, σ x) := (map_prod _ _ _).symm
    _ = ‖Algebra.norm F x‖ := by
          rw [← Algebra.norm_eq_prod_automorphisms, spectralMulAlgNorm_def,
            spectralNorm_extends]

/-- A field-norm-one element in a finite Galois extension has spectral norm one. -/
theorem spectralNorm_eq_one_of_algebraNorm_eq_one {x : E}
    (hx : Algebra.norm F x = 1) : spectralNorm F E x = 1 := by
  apply (pow_eq_one_iff_of_nonneg (spectralNorm_nonneg x)
    (Fintype.card_ne_zero (α := E ≃ₐ[F] E))).mp
  rw [spectralNorm_pow_card_galois, hx, norm_one]

end Langlands.LocalGalois

namespace Langlands.GroupScheme

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The spectral valuation over the canonical local-field norm extends the original
valuative relation, in either characteristic and in arbitrary extension universe. -/
theorem localField_spectralValuation_valuativeExtension
    (E : Type v) [Field E] [Algebra F E] [Algebra.IsAlgebraic F E] :
    letI := LocalGalois.localNormedField F
    letI := LocalGalois.localNormedField_ultrametric F
    letI := LocalGalois.localNormedField_complete F
    letI := ValuativeRel.ofValuation (LocalGalois.spectralValuation F E)
    ValuativeExtension F E := by
  let := LocalGalois.localNormedField F
  let := LocalGalois.localNormedField_ultrametric F
  let := LocalGalois.localNormedField_complete F
  let := ValuativeRel.ofValuation (LocalGalois.spectralValuation F E)
  constructor
  intro a b
  change spectralNorm F E (algebraMap F E a) ≤ spectralNorm F E (algebraMap F E b) ↔
    a ≤ᵥ b
  rw [spectralNorm_extends, spectralNorm_extends]
  exact (LocalGalois.localNormedField_le F a b).trans
    (ValuativeRel.valuation F).vle_iff_le.symm

/-- Every character value over a finite Galois extension has spectral valuation one
on a closed torus inside an anisotropic local-field group. -/
theorem IsAnisotropic.spectralValuation_characterEval_eq_one_of_closedTorus
    (E : Type u) [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (hG : IsAnisotropic G) (hT : IsTorus T.toGrp)
    {j : T.toGrp ⟶ G} (hj : IsClosedSubgroup j)
    (χ : rationalCharacters (GaloisPointComparison.baseChanged F E T.toGrp))
    (t : rationalPoints T.toGrp) :
    letI := LocalGalois.localNormedField F
    letI := LocalGalois.localNormedField_ultrametric F
    letI := LocalGalois.localNormedField_complete F
    LocalGalois.spectralValuation F E (rationalCharacterEval χ
      (GaloisPointComparison.rationalExtend F E T.toGrp t) : E) = 1 := by
  let := LocalGalois.localNormedField F
  let := LocalGalois.localNormedField_ultrametric F
  let := LocalGalois.localNormedField_complete F
  apply NNReal.eq
  exact LocalGalois.spectralNorm_eq_one_of_algebraNorm_eq_one
    (hG.algebraNorm_characterEval_eq_one_of_closedTorus E hT hj χ t)

/-- The finite-Galois spectral unit conclusion for actual anisotropic tori. -/
def AnisotropicTorusSpectralUnitsStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (E : Type u) [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom],
    IsTorus T.toGrp → IsAnisotropic T.toGrp →
      ∀ (χ : rationalCharacters (GaloisPointComparison.baseChanged F E T.toGrp))
        (t : rationalPoints T.toGrp),
      letI := LocalGalois.localNormedField F
      letI := LocalGalois.localNormedField_ultrametric F
      letI := LocalGalois.localNormedField_complete F
      LocalGalois.spectralValuation F E (rationalCharacterEval χ
        (GaloisPointComparison.rationalExtend F E T.toGrp t) : E) = 1

/-- The torus-only spectral unit statement follows by taking the identity closed
subgroup of the anisotropic torus. -/
theorem anisotropicTorusSpectralUnits_proof :
    AnisotropicTorusSpectralUnitsStatement.{u} := by
  intro F _ _ _ _ E _ _ _ _ T _ _ hT hA χ t
  exact hA.spectralValuation_characterEval_eq_one_of_closedTorus E hT
    (IsClosedSubgroup.of_iso (Iso.refl T.toGrp)) χ t

end Langlands.GroupScheme
