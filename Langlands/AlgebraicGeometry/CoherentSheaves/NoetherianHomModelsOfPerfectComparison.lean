import Langlands.AlgebraicGeometry.CoherentSheaves.NoetherianHomPerfectComparisonStatement
import Langlands.AlgebraicGeometry.TensorSectionsBaseChange
import Langlands.AlgebraicGeometry.TensorHomologyMatrix
import Langlands.Cohomology.ConnectiveFreeChart

/-! # Finite linear models from a universally connective perfect comparison -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

namespace TensorSections

variable {R : CommRingCat.{u}}

/-- The principal finite free chart at a prime, for a strictly perfect complex whose negative
homology vanishes after every scalar extension. -/
def perfectChart (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : Cohomology.ModuleComplex.IsStrictlyPerfect K)
    (hneg : ∀ (S : CommRingCat.{u}) (φ : R ⟶ S) (n : ℤ), n < 0 →
      IsZero (((Cohomology.ModuleComplex.baseChange φ.hom).obj K).homology n))
    (P : PrimeSpectrum R) : Cohomology.ModuleComplex.ConnectiveFreeChart K P.asIdeal :=
  Cohomology.ModuleComplex.connectiveFreeChart K hK P.asIdeal
    (fun i hi ↦ hneg (CommRingCat.of P.asIdeal.ResidueField)
      (CommRingCat.ofHom (algebraMap R P.asIdeal.ResidueField)) i hi)

/-- On the principal chart of a prime, degree-zero tensor homology restricted to the slice over
the chart is the solution presheaf of the chart's actual degree-zero differential matrix. -/
def chartSolutionsIso (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : Cohomology.ModuleComplex.IsStrictlyPerfect K)
    (hneg : ∀ (S : CommRingCat.{u}) (φ : R ⟶ S) (n : ℤ), n < 0 →
      IsZero (((Cohomology.ModuleComplex.baseChange φ.hom).obj K).homology n))
    (P : PrimeSpectrum R) :
    (Over.map (Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away (perfectChart K hK hneg P).parameter))))).op ⋙
        homologyPresheaf K 0 ≅
      FiniteLinearEquations.solutionsPresheaf
        (FiniteLinearEquations.TensorKernel.matrix
          ((perfectChart K hK hneg P).complex.d 0 1).hom
          ((perfectChart K hK hneg P).coordinates 0)
          ((perfectChart K hK hneg P).coordinates 1)) :=
  homologyPresheafBaseChangeIso (R := R)
      (S := CommRingCat.of (Localization.Away (perfectChart K hK hneg P).parameter)) K 0 ≪≫
    (homologyPresheafIsoOfHomotopyEquiv
      (R := CommRingCat.of (Localization.Away (perfectChart K hK hneg P).parameter))
      (perfectChart K hK hneg P).equivalence 0).symm ≪≫
    homologyZeroSolutionsPresheafIso
      (R := CommRingCat.of (Localization.Away (perfectChart K hK hneg P).parameter))
      (perfectChart K hK hneg P).complex
      (perfectChart K hK hneg P).d_neg_one_zero
      ((perfectChart K hK hneg P).coordinates 0) ((perfectChart K hK hneg P).coordinates 1)

/-- Degree-zero tensor homology of a strictly perfect complex whose negative homology
vanishes after every scalar extension has finite linear models on principal open charts. -/
theorem homologyZero_hasLocalModels (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : Cohomology.ModuleComplex.IsStrictlyPerfect K)
    (hneg : ∀ (S : CommRingCat.{u}) (φ : R ⟶ S) (n : ℤ), n < 0 →
      IsZero (((Cohomology.ModuleComplex.baseChange φ.hom).obj K).homology n)) :
    FiniteLinearEquations.HasLocalModels (homologyPresheaf K 0) := by
  refine ⟨PrimeSpectrum R,
    fun P ↦ CommRingCat.of (Localization.Away (perfectChart K hK hneg P).parameter),
    fun P ↦ Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization.Away (perfectChart K hK hneg P).parameter))),
    fun P ↦ inferInstance, ?_, fun P ↦ ⟨_, _, _, ⟨chartSolutionsIso K hK hneg P⟩⟩⟩
  intro b
  let P : PrimeSpectrum R := b
  refine ⟨P, ?_⟩
  have hmem : b ∈ (Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization.Away (perfectChart K hK hneg P).parameter)))).opensRange := by
    rw [Scheme.Hom.opensRange_localizationAway]
    exact (PrimeSpectrum.mem_basicOpen _ P).2 (perfectChart K hK hneg P).not_mem
  exact Scheme.Hom.mem_opensRange.1 hmem

end TensorSections

namespace CoherentSheaves

/-- The universally connective perfect comparison implies local finite linear models for
proper module Hom over a noetherian affine base. -/
theorem noetherianHomFiniteLinearModels_of_perfectComparison
    (h : NoetherianHomPerfectComparisonStatement.{u}) :
    NoetherianHomFiniteLinearModelsStatement.{u} := by
  intro R hR Y p hp hfp M N hM hN hflat
  obtain ⟨K, hK, hneg, ⟨e⟩⟩ := h R hR Y p hp hfp M N hM hN hflat
  exact (TensorSections.homologyZero_hasLocalModels K hK hneg).of_iso e.symm

end CoherentSheaves

end Langlands.AlgebraicGeometry
