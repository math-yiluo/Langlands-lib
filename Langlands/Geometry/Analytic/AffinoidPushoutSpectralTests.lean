import Langlands.Geometry.Analytic.GeneralizedAffinoid.AffinoidPushout
import Langlands.Geometry.Analytic.GeneralizedAffinoid.CoordinateContinuity
import Langlands.Geometry.Analytic.StrictTestDomain.SpectralDisplacement

/-! # Spectral displacement on affinoid pushouts -/

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open BanachSpectrum Filter

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A B : PresentedAffinoidAlgebra K} {T : Type v}

/-- The spectral displacement of a section tends uniformly to zero on
the target spectrum along the given filter. -/
def SpectralConvergesOn (l : Filter T) (φ : T → BoundedAlgHom K A B)
    (ψ : BoundedAlgHom K A B) (a : A) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ t in l, SpectralBound (φ t a - ψ a) ε

variable {l : Filter T} {φ : T → BoundedAlgHom K A B} {ψ : BoundedAlgHom K A B}

private theorem spectralBound_apply (f : BoundedAlgHom K A B) (a : A) :
    SpectralBound (f a) ‖a‖ :=
  fun x => (BanachSpectrum.comap f.toBoundedRingHom x).le_norm a

theorem SpectralConvergesOn.add {a b : A}
    (ha : SpectralConvergesOn l φ ψ a) (hb : SpectralConvergesOn l φ ψ b) :
    SpectralConvergesOn l φ ψ (a + b) := by
  intro ε hε
  filter_upwards [ha ε hε, hb ε hε] with t hta htb
  rw [map_add, map_add, add_sub_add_comm]
  exact hta.add (K := K) htb

theorem SpectralConvergesOn.mul {a b : A}
    (ha : SpectralConvergesOn l φ ψ a) (hb : SpectralConvergesOn l φ ψ b) :
    SpectralConvergesOn l φ ψ (a * b) := by
  intro ε hε
  let M := ‖a‖ + ‖b‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let δ := ε / M
  have hδ : 0 < δ := div_pos hε hM
  have hδM : δ * M = ε := div_mul_cancel₀ ε hM.ne'
  have haM : ‖a‖ ≤ M := by dsimp [M]; linarith [norm_nonneg b]
  have hbM : ‖b‖ ≤ M := by dsimp [M]; linarith [norm_nonneg a]
  filter_upwards [ha δ hδ, hb δ hδ] with t hta htb
  have hleft : SpectralBound ((φ t a - ψ a) * φ t b) ε := by
    intro x
    rw [map_mul]
    calc
      _ ≤ δ * ‖b‖ := mul_le_mul (hta x) (spectralBound_apply (φ t) b x)
        (apply_nonneg _ _) hδ.le
      _ ≤ δ * M := mul_le_mul_of_nonneg_left hbM hδ.le
      _ = ε := hδM
  have hright : SpectralBound (ψ a * (φ t b - ψ b)) ε := by
    intro x
    rw [map_mul]
    calc
      _ ≤ ‖a‖ * δ := mul_le_mul (spectralBound_apply ψ a x) (htb x)
        (apply_nonneg _ _) (norm_nonneg a)
      _ ≤ M * δ := mul_le_mul_of_nonneg_right haM hδ.le
      _ = ε := (mul_comm M δ).trans hδM
  rw [map_mul, map_mul]
  convert hleft.add (K := K) hright using 1
  ring

theorem spectralConvergesOn_algebraMap (c : K) :
    SpectralConvergesOn l φ ψ (algebraMap K A c) := by
  intro ε hε
  apply Filter.Eventually.of_forall
  intro t
  simpa only [AlgHom.commutes, sub_self] using spectralBound_zero (A := B) hε.le

/-- Finite affinoid coordinates control displacement on every element in
the actual weighted quotient. -/
theorem spectralConvergesOn_of_coordinates
    (h : ∀ i, SpectralConvergesOn l φ ψ (coordinate K A i)) (a : A) :
    SpectralConvergesOn l φ ψ a := by
  let S : Subalgebra K A :=
    { carrier := {b | SpectralConvergesOn l φ ψ b}
      zero_mem' := by
        change SpectralConvergesOn l φ ψ 0
        simpa only [map_zero] using
          (spectralConvergesOn_algebraMap (l := l) (φ := φ) (ψ := ψ) (0 : K))
      add_mem' := fun ha hb => SpectralConvergesOn.add ha hb
      one_mem' := by
        change SpectralConvergesOn l φ ψ 1
        simpa only [map_one] using
          (spectralConvergesOn_algebraMap (l := l) (φ := φ) (ψ := ψ) (1 : K))
      mul_mem' := fun ha hb => SpectralConvergesOn.mul ha hb
      algebraMap_mem' := spectralConvergesOn_algebraMap }
  intro ε hε
  obtain ⟨f, s, hs⟩ := exists_partial_sum_approx A a hε
  let q := presentationMap K A (∑ d ∈ s, GeneralizedTateAlgebra.monomial A.polyradius K d
    (MvPowerSeries.coeff d (GeneralizedTateAlgebra.series A.polyradius K f)))
  have hq : q ∈ S := by
    dsimp only [q]
    rw [map_sum]
    apply Subalgebra.sum_mem
    intro d hd
    rw [GeneralizedTateAlgebra.map_monomial]
    apply S.mul_mem (S.algebraMap_mem _)
    unfold StrictTateAlgebra.monomialValue Finsupp.prod
    apply Subalgebra.prod_mem
    intro i hi
    exact S.pow_mem (h i) _
  have hadd : SpectralConvergesOn l φ ψ q := hq
  filter_upwards [hadd ε hε] with t ht
  have hleft : SpectralBound (φ t (a - q)) ε := (spectralBound_apply _ _).mono hs.le
  have hright : SpectralBound (-ψ (a - q)) ε := ((spectralBound_apply _ _).mono hs.le).neg
  convert (hleft.add (K := K) ht).add (K := K) hright using 1
  rw [map_sub, map_sub]
  abel

namespace AffinoidPushout

variable {R C : PresentedAffinoidAlgebra K} (f : BoundedAlgHom K R A) (g : BoundedAlgHom K R C)
  {φ' : T → BoundedAlgHom K (algebra f g) B} {ψ' : BoundedAlgHom K (algebra f g) B}

/-- The functions pulled back from each factor control every spectral test
on the affinoid pushout algebra. -/
theorem spectralConvergesOn_of_factors
    (hl : ∀ a : A, SpectralConvergesOn l φ' ψ' (leftMap f g a))
    (hr : ∀ c : C, SpectralConvergesOn l φ' ψ' (rightMap f g c))
    (b : algebra f g) : SpectralConvergesOn l φ' ψ' b := by
  apply spectralConvergesOn_of_coordinates _ b
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [← leftMap_coordinate]
    exact hl _
  · rw [← rightMap_coordinate]
    exact hr _

end AffinoidPushout

end Langlands.Analytic.PresentedAffinoidAlgebra
