import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Finite étale algebras over Noetherian rings with discrete spectrum -/

universe u v

namespace Langlands.AlgebraicGeometry

namespace GroupoidCoactionFiniteAlgebra

variable (B : Type u) [CommRing B]

/-- A Noetherian ring with discrete prime spectrum is Artinian. -/
theorem isArtinianRing_of_discrete [IsNoetherianRing B]
    [DiscreteTopology (PrimeSpectrum B)] : IsArtinianRing B := by
  let : Ring.KrullDimLE 0 B :=
    (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp
      (inferInstance : DiscreteTopology (PrimeSpectrum B))).2
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

/-- A reduced Noetherian ring with discrete spectrum is the product of its
maximal-ideal residue fields. The indexing type is finite by Artinianity. -/
noncomputable def equivPiOfDiscrete [IsNoetherianRing B] [IsReduced B]
    [DiscreteTopology (PrimeSpectrum B)] :
    B ≃ₐ[B] ∀ I : MaximalSpectrum B, B ⧸ I.asIdeal := by
  let := isArtinianRing_of_discrete B
  exact IsArtinianRing.equivPi B

theorem finite_maximalSpectrum_of_discrete [IsNoetherianRing B]
    [DiscreteTopology (PrimeSpectrum B)] : Finite (MaximalSpectrum B) := by
  let := isArtinianRing_of_discrete B
  infer_instance

variable (C : Type v) [CommRing C] [Algebra B C]

/-- Étale algebras over an Artinian ring are finite and projective. -/
theorem finite_projective_of_artinian [IsArtinianRing B] [Algebra.Etale B C] :
    Module.Finite B C ∧ Module.Projective B C := by
  let : Module.Finite B C := Module.Finite.of_quasiFinite
  let : Module.FinitePresentation B C := Module.finitePresentation_of_finite B C
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

/-- The algebraic input for restricting an affine étale relation to a finite
discrete closed subset. Reducedness is unnecessary for this conclusion. -/
theorem finite_projective_of_discrete [IsNoetherianRing B]
    [DiscreteTopology (PrimeSpectrum B)] [Algebra.Etale B C] :
    Module.Finite B C ∧ Module.Projective B C := by
  let := isArtinianRing_of_discrete B
  exact finite_projective_of_artinian B C

omit [Algebra B C] in
/-- A ring-map version, with its induced source algebra structure explicit. -/
theorem finite_projective_of_etale_hom [IsNoetherianRing B]
    [DiscreteTopology (PrimeSpectrum B)] (f : B →+* C) (hf : f.Etale) :
    let := f.toAlgebra
    Module.Finite B C ∧ Module.Projective B C := by
  let := f.toAlgebra
  let := hf.toAlgebra
  exact finite_projective_of_discrete B C

end GroupoidCoactionFiniteAlgebra

end Langlands.AlgebraicGeometry
