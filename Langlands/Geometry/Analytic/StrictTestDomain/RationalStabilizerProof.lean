import Langlands.Geometry.Analytic.StrictTestDomain.RationalStabilizerStatement
import Langlands.Geometry.Analytic.StrictTestDomain.RationalStabilizerAction
import Langlands.Geometry.Analytic.StrictTestDomain.ContinuousActionProof
import Langlands.Geometry.Analytic.Spectrum.Nonarchimedean
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Open setwise stabilizers of actual rational loci -/

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism

open CategoryTheory Filter
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {P : PresentedStrictAffinoidAlgebra K}

/-- A rational denominator has a positive uniform lower bound on its locus,
including when the locus is empty. -/
theorem exists_pos_le_denominator (d : RationalData K P) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ d.locus, ε ≤ x d.denominator := by
  have hc : IsClosed d.locus := by
    change IsClosed {x : BanachSpectrum P | ∀ j, x (d.numerator j) ≤ x d.denominator}
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_le
      (BanachSpectrum.evaluation (d.numerator j)).continuous
      (BanachSpectrum.evaluation d.denominator).continuous
  apply hc.isCompact.exists_forall_le'
    (BanachSpectrum.evaluation d.denominator).continuous.continuousOn
  intro x hx
  have hn : x d.denominator ≠ 0 := by
    intro hz
    rcases d.no_common_zero x with hb | ⟨j, hj⟩
    · exact hb hz
    · exact hj (le_antisymm (by simpa only [hz] using hx j)
        (apply_nonneg x.toMulRingSeminorm _))
  exact lt_of_le_of_ne (apply_nonneg x.toMulRingSeminorm _) hn.symm

/-- A bounded algebra map whose displacement of the rational inputs is smaller
than a denominator lower bound pulls every locus point back into the locus. -/
theorem comap_mem_locus_of_displacement_lt (d : RationalData K P) {ε : ℝ}
    (hε : ∀ x ∈ d.locus, ε ≤ x d.denominator)
    (φ : BoundedAlgHom K P P)
    (hb : ‖φ.toAlgHom d.denominator - d.denominator‖ < ε)
    (hf : ∀ j, ‖φ.toAlgHom (d.numerator j) - d.numerator j‖ < ε)
    {x : BanachSpectrum P} (hx : x ∈ d.locus) :
    BanachSpectrum.comap φ.toBoundedRingHom x ∈ d.locus := by
  have hsmall : x.toMulRingSeminorm (φ.toAlgHom d.denominator - d.denominator) <
      x.toMulRingSeminorm d.denominator :=
    (x.le_norm _).trans_lt (hb.trans_le (hε x hx))
  have heq : x (φ.toAlgHom d.denominator) = x d.denominator := by
    simpa only [sub_add_cancel] using
      (x.isNonarchimedean (K := K)).add_eq_right_of_lt
        (map_neg_eq_map x.toMulRingSeminorm) hsmall
  intro j
  change x (φ.toAlgHom (d.numerator j)) ≤ x (φ.toAlgHom d.denominator)
  rw [heq]
  have hnum := x.isNonarchimedean (K := K)
    (φ.toAlgHom (d.numerator j) - d.numerator j) (d.numerator j)
  simpa only [sub_add_cancel] using hnum.trans
    (max_le ((x.le_norm _).trans ((hf j).le.trans (hε x hx))) (hx j))

/-- Reusable perturbation criterion for an automorphism to preserve the actual
rational subset: control the finitely many forward and inverse input displacements. -/
theorem locus_image_eq_of_displacement_lt (d : RationalData K P) {ε : ℝ}
    (hε : ∀ x ∈ d.locus, ε ≤ x d.denominator) (g : Aut P)
    (hb : ‖g.hom.toAlgHom d.denominator - d.denominator‖ < ε)
    (hf : ∀ j, ‖g.hom.toAlgHom (d.numerator j) - d.numerator j‖ < ε)
    (hib : ‖g.inv.toAlgHom d.denominator - d.denominator‖ < ε)
    (hif : ∀ j, ‖g.inv.toAlgHom (d.numerator j) - d.numerator j‖ < ε) :
    (fun x : BanachSpectrum P => g • x) '' d.locus = d.locus := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact comap_mem_locus_of_displacement_lt d hε g.inv hib hif hx
  · intro x hx
    refine ⟨g⁻¹ • x, ?_, smul_inv_smul g x⟩
    exact comap_mem_locus_of_displacement_lt d hε g.hom hb hf hx

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Norm-continuous algebra-element orbits make the actual rational-locus
stabilizer open in any topological parameter group. -/
theorem isOpen_rationalLocusStabilizer (ρ : G →* Aut P)
    (hρ : ∀ a : P, Continuous (fun g : G => (ρ g).hom.toAlgHom a))
    (d : RationalData K P) :
    IsOpen {g : G |
      (fun x : BanachSpectrum P => (ρ g) • x) '' d.locus = d.locus} := by
  obtain ⟨ε, hε, hbound⟩ := exists_pos_le_denominator d
  have hf (a : P) : ∀ᶠ g in 𝓝 (1 : G), ‖(ρ g).hom.toAlgHom a - a‖ < ε := by
    have hc : Continuous (fun g : G => ‖(ρ g).hom.toAlgHom a - a‖) :=
      ((hρ a).sub continuous_const).norm
    have hz : ‖(ρ (1 : G)).hom.toAlgHom a - a‖ < ε := by
      rw [map_one]
      change ‖a - a‖ < ε
      simpa only [sub_self, norm_zero] using hε
    exact hc.continuousAt.eventually (gt_mem_nhds hz)
  have hi (a : P) : ∀ᶠ g in 𝓝 (1 : G), ‖(ρ g).inv.toAlgHom a - a‖ < ε := by
    have hc : Continuous (fun g : G => ‖(ρ g).inv.toAlgHom a - a‖) :=
      ((continuous_inv_apply ρ hρ a).sub continuous_const).norm
    have hz : ‖(ρ (1 : G)).inv.toAlgHom a - a‖ < ε := by
      rw [map_one]
      change ‖a - a‖ < ε
      simpa only [sub_self, norm_zero] using hε
    exact hc.continuousAt.eventually (gt_mem_nhds hz)
  change IsOpen (((locusStabilizer d).comap ρ : Subgroup G) : Set G)
  apply Subgroup.isOpen_of_mem_nhds
  filter_upwards [hf d.denominator, Filter.eventually_all.mpr (fun j => hf (d.numerator j)),
    hi d.denominator, Filter.eventually_all.mpr (fun j => hi (d.numerator j))]
    with g hb hnum hib hinum
  exact locus_image_eq_of_displacement_lt d hbound (ρ g) hb hnum hib hinum

/-- The exact published target, with independent field and group universes. -/
theorem rationalLocusStabilizerOpen : RationalLocusStabilizerOpenStatement.{u, v} := by
  intro K _ _ P G _ _ _ ρ hρ d
  exact isOpen_rationalLocusStabilizer ρ hρ d

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism
