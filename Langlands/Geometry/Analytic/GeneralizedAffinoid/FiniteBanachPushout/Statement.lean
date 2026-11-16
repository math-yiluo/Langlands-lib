import Langlands.Geometry.Analytic.GeneralizedAffinoid.AdmissiblePushout
import Langlands.Geometry.Analytic.FullRecognitionFiniteMorphisms
import Langlands.Geometry.Analytic.FiniteMorphismFibres
import Mathlib.Logic.Small.Basic

/-! # Finite Banach pushout and the size of its spectrum -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

namespace BoundedAlgHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {R : Type v} {S : Type w} [NormedCommRing R] [NormedCommRing S]
  [NormedAlgebra K R] [NormedAlgebra K S]

/-- A finite spectrum map has a small source whenever its target is small.
The smallness universe is independent of both algebra universes. -/
theorem small_spectrum_of_finite (f : BoundedAlgHom K R S)
    (hf : f.toAlgHom.toRingHom.Finite) [Small.{z} (BanachSpectrum R)] :
    Small.{z} (BanachSpectrum S) := by
  classical
  have hfib : ∀ t : BanachSpectrum R, Small.{z} (f.fibre t) := by
    intro t
    let : Fintype (f.fibre t) := (f.finite_fibre hf t).fintype
    exact small_map (Fintype.equivFin (f.fibre t))
  let := hfib
  let j : BanachSpectrum S → Σ t : BanachSpectrum R, f.fibre t :=
    fun s => ⟨BanachSpectrum.comap f.toBoundedRingHom s, ⟨s, rfl⟩⟩
  exact small_of_injective (f := j) fun s s' h =>
    congrArg (fun p : Σ t : BanachSpectrum R, f.fibre t => p.2.1) h

end BoundedAlgHom

namespace PresentedAffinoidAlgebra.AffinoidPushout

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The original finite Banach map remains finite Banach after arbitrary
bounded base change in the actual closed-quotient affinoid pushout. -/
def FiniteBanachPushoutStatement (K : Type u) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ (A B C : PresentedAffinoidAlgebra K)
    (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C),
    f.IsFiniteBanach → (rightMap f g).IsFiniteBanach

variable {K} {A B C : PresentedAffinoidAlgebra K}
  (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)

/-- The admissible epimorphism case already follows from the published
admissible pushout theorem, with the single generator `1`. -/
theorem rightMap_isFiniteBanach_of_isAdmissibleEpi (hf : f.IsAdmissibleEpi) :
    (rightMap f g).IsFiniteBanach := by
  obtain ⟨M, hM, hlift⟩ :=
    (rightMap f g).isAdmissibleEpi_iff_normControlledLifts.mp
      (rightMap_isAdmissibleEpi f g hf)
  refine ⟨1, fun _ => 1, M, hM, fun y => ?_⟩
  obtain ⟨c, hc, hcn⟩ := hlift y
  refine ⟨fun _ => c, ?_, ?_⟩
  · simpa only [BoundedAlgHom.coefficientMap_apply, Fin.sum_univ_one, mul_one] using hc
  · exact (pi_norm_le_iff_of_nonneg (mul_nonneg hM.le (norm_nonneg y))).2
      fun _ => hcn

/-- Finite Banach base change gives finite ordinary fibres of the actual
pushout spectrum map. -/
theorem finite_fibre_rightMap_of_finiteBanachPushout
    (h : FiniteBanachPushoutStatement K) (hf : f.IsFiniteBanach)
    (t : BanachSpectrum C) : ((rightMap f g).fibre t).Finite :=
  (rightMap f g).finite_fibre (h A B C f g hf).finite t

/-- Finite Banach base change preserves any supplied smallness universe of
the spectrum of the changed base algebra. -/
theorem small_spectrum_of_finiteBanachPushout
    (h : FiniteBanachPushoutStatement K) (hf : f.IsFiniteBanach)
    [Small.{v} (BanachSpectrum C)] : Small.{v} (BanachSpectrum (algebra f g)) :=
  (rightMap f g).small_spectrum_of_finite (h A B C f g hf).finite

end PresentedAffinoidAlgebra.AffinoidPushout

end Langlands.Analytic
