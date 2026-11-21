import Langlands.Geometry.Analytic.FiniteAffinoidLocalizedHomDescent
import Langlands.Geometry.Analytic.FlatTargetDescent
import Mathlib.LinearAlgebra.Unimodular
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # Finite étale descent on affinoid algebra triangles -/

noncomputable section

universe u

namespace Langlands.Analytic.BoundedAlgHom

open PresentedAffinoidAlgebra
open scoped TensorProduct

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : PresentedAffinoidAlgebra K}

private theorem exists_linear_apply_one {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Projective R S] [Module.FaithfullyFlat R S]
    {n : ℕ} (b : Fin n → S)
    (h : Function.Surjective (Fintype.linearCombination R b)) :
    ∃ r : S →ₗ[R] R, r 1 = 1 := by
  classical
  let c := Fintype.linearCombination R b
  obtain ⟨s, hs⟩ := c.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr h)
  let I := Ideal.span (Set.range (s (1 : S)))
  have hOne : (1 : S) ∈ I • (⊤ : Submodule R S) := by
    have hc : c (s 1) = 1 := LinearMap.congr_fun hs 1
    rw [← hc, Fintype.linearCombination_apply]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_range_self i)) (Submodule.mem_top)
  have hTop : I • (⊤ : Submodule R S) = ⊤ := by
    rw [Ideal.smul_top_eq_map] at hOne ⊢
    have hMap : Ideal.map (algebraMap R S) I = ⊤ := (Ideal.eq_top_iff_one _).mpr hOne
    rw [hMap, Submodule.restrictScalars_top]
  have hI :=
    (Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top R S).mp inferInstance |>.2 I hTop
  obtain ⟨l, hl⟩ : Module.IsUnimodular R (s (1 : S)) := by
    apply (Pi.basisFun R (Fin n)).isUnimodular_iff_span_repr_eq_top.mpr
    have hRange : Set.range (((Pi.basisFun R (Fin n)).repr (s (1 : S))) : Fin n → R) =
        Set.range (s (1 : S)) := by
      congr 1
    rw [hRange]
    exact hI
  exact ⟨l.comp s, hl⟩

private theorem exists_bounded_module_retraction (g : BoundedAlgHom K B C)
    (hg : g.IsFiniteBanach) (hff : g.toAlgHom.toRingHom.FaithfullyFlat) :
    ∃ r : C →L[K] B, Function.LeftInverse r g ∧
      ∀ b : B, ∀ x : C, r (g b * x) = b * r x := by
  let : Algebra B C := g.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower K B C := IsScalarTower.of_algebraMap_eq' g.toAlgHom.comp_algebraMap.symm
  let : Module.FaithfullyFlat B C := hff
  let : Module.Finite B C := hg.finite
  let : Module.FinitePresentation B C := Module.finitePresentation_of_finite B C
  let : Module.Projective B C := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, b, L, _, hc⟩ := hg
  have hd : Function.Surjective (Fintype.linearCombination B b) := by
    intro x
    obtain ⟨c, h, _⟩ := hc x
    exact ⟨c, h⟩
  obtain ⟨r, hr⟩ := exists_linear_apply_one b hd
  let rK : C →ₗ[K] B := r.restrictScalars K
  let M : ℝ := ∑ i : Fin n, ‖r (b i)‖
  have hBound (x : C) : ‖rK x‖ ≤ (L * M) * ‖x‖ := by
    obtain ⟨c, h, hn⟩ := hc x
    have hx : (∑ i, c i • b i) = x := h
    change ‖r x‖ ≤ _
    calc
      ‖r x‖ = ‖∑ i, c i * r (b i)‖ := by
        rw [← hx, map_sum]
        simp only [map_smul, smul_eq_mul]
      _ ≤ ∑ i, ‖c i * r (b i)‖ := norm_sum_le _ _
      _ ≤ ∑ i, (L * ‖x‖) * ‖r (b i)‖ := Finset.sum_le_sum fun i _ =>
        (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right ((norm_le_pi_norm c i).trans hn) (norm_nonneg _))
      _ = (L * M) * ‖x‖ := by rw [← Finset.mul_sum, mul_right_comm]
  refine ⟨rK.mkContinuous (L * M) hBound, ?_, ?_⟩
  · intro a
    change r (g a) = a
    calc
      r (g a) = r (a • (1 : C)) := by rw [Algebra.smul_def, mul_one]; rfl
      _ = a := by rw [map_smul, hr, smul_eq_mul, mul_one]
  · intro a x
    change r (a • x) = a • r x
    exact r.map_smul a x

/-- A finite Banach faithfully flat map has a bounded retraction linear
over the source algebra. -/
def finiteFaithfullyFlatRetraction (g : BoundedAlgHom K B C)
    (hg : g.IsFiniteBanach) (hff : g.toAlgHom.toRingHom.FaithfullyFlat) :
    {r : C →L[K] B // Function.LeftInverse r g ∧
      ∀ b : B, ∀ x : C, r (g b * x) = b * r x} :=
  Classical.indefiniteDescription _ (exists_bounded_module_retraction g hg hff)

/-- Banach finiteness descends across a finite faithfully flat Banach map
on the coefficient algebras. -/
theorem IsFiniteBanach.of_faithfullyFlat_comp
    {f : BoundedAlgHom K A B} {g : BoundedAlgHom K B C}
    (hComp : (g.comp f).IsFiniteBanach) (hg : g.IsFiniteBanach)
    (hff : g.toAlgHom.toRingHom.FaithfullyFlat) : f.IsFiniteBanach := by
  let r := finiteFaithfullyFlatRetraction g hg hff
  obtain ⟨n, b, D, hD, hCoeff⟩ := hComp
  obtain ⟨L, hL, hBound⟩ := g.bounded
  refine ⟨n, fun i => r.val (b i), D * L, mul_pos hD hL, fun y => ?_⟩
  obtain ⟨c, hc, hn⟩ := hCoeff (g y)
  refine ⟨c, ?_, ?_⟩
  · rw [coefficientMap_apply] at hc ⊢
    have h := congrArg r.val hc
    change r.val _ = r.val (g y) at h
    simpa only [BoundedAlgHom.comp_apply, map_sum, r.property.2, r.property.1 y] using h
  · calc
      ‖c‖ ≤ D * ‖g y‖ := hn
      _ ≤ D * (L * ‖y‖) := mul_le_mul_of_nonneg_left (hBound y) hD.le
      _ = (D * L) * ‖y‖ := (mul_assoc _ _ _).symm

/-- Étaleness and Banach finiteness descend when the last algebra map is
finite étale and surjective on bounded spectra. -/
theorem finiteBanach_etale_of_finiteEtale_comp
    {f : BoundedAlgHom K A B} {g : BoundedAlgHom K B C}
    (hg : g.IsFiniteBanach ∧ g.AlgebraicallyFiniteEtale)
    (hsurj : Function.Surjective (BanachSpectrum.comap g.toBoundedRingHom))
    (hComp : (g.comp f).IsFiniteBanach ∧ (g.comp f).AlgebraicallyFiniteEtale) :
    f.IsFiniteBanach ∧ f.AlgebraicallyFiniteEtale := by
  have hff := SmallAffinoidSpectrum.faithfullyFlat_of_flat_of_spectrum_surjective
    g ((RingHom.Etale.iff_flat_and_formallyUnramified.mp hg.2.2).1) hsurj
  have hFin := hComp.1.of_faithfullyFlat_comp hg.1 hff
  refine ⟨hFin, hFin.finite, ?_⟩
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  let : Algebra B C := g.toAlgHom.toRingHom.toAlgebra
  let : Algebra A C := (g.comp f).toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.FaithfullyFlat B C := hff
  let : Algebra.Etale B C := hg.2.2
  let : Algebra.Etale A C := hComp.2.2
  let : Module.Flat A B := flat_of_faithfullyFlat_target A B C
  let : Algebra.FormallyUnramified A B := by
    constructor
    have : Subsingleton (C ⊗[B] Ω[B⁄A]) :=
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A B C).subsingleton
    exact Module.FaithfullyFlat.lTensor_reflects_triviality B C _
  have : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finiteType.mp hFin.finite.finiteType
  exact Algebra.Etale.of_formallyUnramified_of_flat

end Langlands.Analytic.BoundedAlgHom
