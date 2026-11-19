import Langlands.Geometry.Analytic.AffinoidPushoutSpectralTests
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCovering
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainLocalization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSpectralCover
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormSectionContinuity

/-! # Spectral convergence on represented affinoid domains -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open BanachSpectrum CategoryTheory Filter
open scoped Pointwise

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A B : PresentedAffinoidAlgebra K} {T : Type v} {l : Filter T}

private theorem SpectralConvergesOn.unit_inv {φ : T → BoundedAlgHom K A B}
    {ψ : BoundedAlgHom K A B} (a : Aˣ) (h : SpectralConvergesOn l φ ψ (a : A)) :
    SpectralConvergesOn l φ ψ (↑a⁻¹ : A) := by
  intro ε hε
  let z : A := ↑a⁻¹
  let c := ‖z‖ + 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hnorm : ‖z‖ ≤ c := by dsimp [c]; linarith
  let δ := ε / (c * c)
  have hδ : 0 < δ := div_pos hε (mul_pos hc hc)
  filter_upwards [h δ hδ] with t ht
  have hφ : φ t z * φ t (a : A) = 1 := by rw [← map_mul, a.inv_mul, map_one]
  have hψ : ψ (a : A) * ψ z = 1 := by rw [← map_mul, a.mul_inv, map_one]
  have heq : φ t z - ψ z = -(φ t z * (φ t (a : A) - ψ (a : A)) * ψ z) := by
    calc
      _ = φ t z * (ψ (a : A) * ψ z) - (φ t z * φ t (a : A)) * ψ z := by
        rw [hψ, hφ, mul_one, one_mul]
      _ = _ := by ring
  change SpectralBound (φ t z - ψ z) ε
  rw [heq]
  apply SpectralBound.neg
  intro x
  rw [map_mul, map_mul]
  have hleft : x (φ t z) ≤ c :=
    ((comap (φ t).toBoundedRingHom x).le_norm z).trans hnorm
  have hright : x (ψ z) ≤ c :=
    ((comap ψ.toBoundedRingHom x).le_norm z).trans hnorm
  calc
    _ ≤ (c * δ) * c :=
      mul_le_mul (mul_le_mul hleft (ht x) (apply_nonneg _ _) hc.le)
        hright (apply_nonneg _ _) (mul_nonneg hc.le hδ.le)
    _ = δ * (c * c) := by ring
    _ = ε := div_mul_cancel₀ ε (mul_pos hc hc).ne'

namespace DomainAutomorphism

variable [CompleteSpace K]

/-- The section map of a locus-preserving automorphism, extended by the
identity to permit convergence tests along filters on the ambient family. -/
def preservedDomainSectionMap (U : Domain K A) (g : Aut A) :
    BoundedAlgHom K U.algebra U.algebra := by
  classical
  exact if hg : g ∈ locusStabilizer U then stabilizerSectionMap U ⟨g, hg⟩
    else BoundedAlgHom.id K U.algebra

theorem preservedDomainSectionMap_of_mem (U : Domain K A) {g : Aut A}
    (hg : g ∈ locusStabilizer U) :
    preservedDomainSectionMap U g = stabilizerSectionMap U ⟨g, hg⟩ := by
  classical
  exact dite_eq_left hg

end DomainAutomorphism

namespace RationalChart

private theorem comap_mem_locus_of_spectralBound (d : RationalChart K A)
    {ε δ : ℝ} (hε : ∀ x ∈ d.locus, ε ≤ x d.denominatorClass) (hδ : δ < ε)
    (f : BoundedAlgHom K A A)
    (hb : SpectralBound (f d.denominatorClass - d.denominatorClass) δ)
    (hf : ∀ j, SpectralBound (f (d.numeratorClass j) - d.numeratorClass j) (d.radii j * ε))
    {x : BanachSpectrum A} (hx : x ∈ d.locus) :
    comap f.toBoundedRingHom x ∈ d.locus := by
  have hsmall : x (f d.denominatorClass - d.denominatorClass) < x d.denominatorClass :=
    (hb x).trans_lt (hδ.trans_le (hε x hx))
  have heq : x (f d.denominatorClass) = x d.denominatorClass := by
    simpa only [sub_add_cancel] using
      (x.isNonarchimedean (K := K)).add_eq_right_of_lt
        (map_neg_eq_map x.toMulRingSeminorm) hsmall
  intro j
  change x (f (d.numeratorClass j)) ≤ d.radii j * x (f d.denominatorClass)
  rw [heq]
  have hnum := x.isNonarchimedean (K := K)
    (f (d.numeratorClass j) - d.numeratorClass j) (d.numeratorClass j)
  simpa only [sub_add_cancel] using hnum.trans
    (max_le ((hf j x).trans (mul_le_mul_of_nonneg_left (hε x hx) (d.radii.positive j).le))
      (hx j))

variable [CompleteSpace K]

open DomainAutomorphism

private theorem eventually_mem_locusStabilizer (d : RationalChart K A) {α : T → Aut A}
    (hα : ∀ a, SpectralConvergesOn l (fun t => (α t).hom) (BoundedAlgHom.id K A) a) :
    ∀ᶠ t in l, α t ∈ DomainAutomorphism.locusStabilizer d.toDomain := by
  obtain ⟨ε, hε, hmin⟩ := d.exists_pos_le_denominator
  have hnum : ∀ᶠ t in l, ∀ j,
      SpectralBound ((α t).hom.toAlgHom (d.numeratorClass j) - d.numeratorClass j) (d.radii j * ε) :=
    Filter.eventually_all.mpr (fun j =>
      hα (d.numeratorClass j) (d.radii j * ε) (mul_pos (d.radii.positive j) hε))
  have hden : ∀ᶠ t in l,
      SpectralBound ((α t).hom.toAlgHom d.denominatorClass - d.denominatorClass) (ε / 2) :=
    hα d.denominatorClass (ε / 2) (half_pos hε)
  filter_upwards [hden, hnum] with t hbt hft
  have hib : SpectralBound ((α t).inv.toAlgHom d.denominatorClass - d.denominatorClass) (ε / 2) :=
    (spectralDisplacementSubgroup d.denominatorClass (ε / 2) (half_pos hε).le).inv_mem hbt
  have hif (j : Fin d.arity) :
      SpectralBound ((α t).inv.toAlgHom (d.numeratorClass j) - d.numeratorClass j) (d.radii j * ε) :=
    (spectralDisplacementSubgroup (d.numeratorClass j) (d.radii j * ε)
      (mul_pos (d.radii.positive j) hε).le).inv_mem (hft j)
  apply (DomainAutomorphism.mem_locusStabilizer d.toDomain (α t)).mpr
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact d.comap_mem_locus_of_spectralBound hmin (half_lt_self hε) (α t).inv hib hif hx
  · intro x hx
    exact ⟨(α t)⁻¹ • x,
      d.comap_mem_locus_of_spectralBound hmin (half_lt_self hε) (α t).hom hbt hft hx,
      smul_inv_smul (α t) x⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem eventually_spectralBound_sectionMap (d : RationalChart K A) {α : T → Aut A}
    (hα : ∀ a, SpectralConvergesOn l (fun t => (α t).hom) (BoundedAlgHom.id K A) a)
    (b : d.toDomain.algebra) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in l, ∃ ht : α t ∈ DomainAutomorphism.locusStabilizer d.toDomain,
      SpectralBound (stabilizerSectionMap d.toDomain ⟨α t, ht⟩ b - b) ε := by
  let F (t : T) : BoundedAlgHom K d.algebra d.algebra := preservedDomainSectionMap d.toDomain (α t)
  let I := BoundedAlgHom.id K d.algebra
  have hpres := d.eventually_mem_locusStabilizer hα
  have hF (t : T) (ht : α t ∈ DomainAutomorphism.locusStabilizer d.toDomain) :
      F t = stabilizerSectionMap d.toDomain ⟨α t, ht⟩ :=
    preservedDomainSectionMap_of_mem d.toDomain ht
  have hbase (a : A) : SpectralConvergesOn l F I (d.baseMap a) := by
    intro r hr
    filter_upwards [hpres, hα a r hr] with t ht hb
    rw [hF t ht]
    change SpectralBound ((stabilizerSectionAction d.toDomain ⟨α t, ht⟩).hom.toAlgHom
      (d.toDomain.baseMap a) - d.toDomain.baseMap a) r
    rw [stabilizerSectionAction_baseMap, ← map_sub]
    exact hb.map d.baseMap.toBoundedRingHom
  have hcoord (i : Fin d.algebra.arity) : SpectralConvergesOn l F I (coordinate K d.algebra i) := by
    change Fin (A.arity + d.arity) at i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · have heq : d.baseMap (coordinate K A i) =
          coordinate K d.algebra (Fin.castAdd d.arity i) :=
        RationalPresentation.baseMap_coordinate K A d.radii d.denominator d.numerators i
      simpa only [heq] using hbase (coordinate K A i)
    · change SpectralConvergesOn l F I (d.fractionCoordinate j)
      have hunit : IsUnit (d.baseMap d.denominatorClass) :=
        RationalPresentation.isUnit_baseMap_denominator K A d.radii
        d.denominator d.numerators d.generates
      obtain ⟨a, ha⟩ := hunit
      have hinv : SpectralConvergesOn l F I (↑a⁻¹ : d.algebra) :=
        SpectralConvergesOn.unit_inv a (ha.symm ▸ hbase d.denominatorClass)
      have hfrac : (↑a⁻¹ : d.algebra) * d.baseMap (d.numeratorClass j) = d.fractionCoordinate j := by
        rw [a.inv_mul_eq_iff_eq_mul, ha, d.baseMap_denominator_mul_fractionCoordinate]
      rw [← hfrac]
      exact hinv.mul (hbase _)
  filter_upwards [hpres, spectralConvergesOn_of_coordinates hcoord b ε hε] with t ht hb
  refine ⟨ht, ?_⟩
  simp only [hF t ht, I, BoundedAlgHom.id_apply] at hb
  exact hb

end RationalChart

namespace DomainAutomorphism

variable [CompleteSpace K]

/-- Spectral convergence of bounded automorphisms on an affinoid implies
eventual preservation of each represented domain and spectral convergence
of the actual restricted maps on all of its sections. -/
theorem eventually_spectralBound_sectionMap (U : Domain K A) {α : T → Aut A}
    (hα : ∀ a, SpectralConvergesOn l (fun t => (α t).hom) (BoundedAlgHom.id K A) a)
    (b : U.algebra) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in l, ∃ ht : α t ∈ locusStabilizer U,
      SpectralBound (stabilizerSectionMap U ⟨α t, ht⟩ b - b) ε := by
  let c := Domain.finiteRationalCoverData U
  have hcomp := Filter.eventually_all.mpr (fun i : Fin c.size =>
    RationalChart.eventually_spectralBound_sectionMap (c.chart i) hα
      ((c.map i).restriction b) hε)
  filter_upwards [hcomp] with t ht
  have hU := mem_locusStabilizer_of_cover c.toFiniteCover (α t) (fun i => (ht i).choose)
  refine ⟨hU, (c.toFiniteCover.spectralBound_iff U.spectrumMap_injective _ ε).mpr ?_⟩
  intro i
  change Fin c.size at i
  obtain ⟨hi, hb⟩ := ht i
  change SpectralBound ((c.map i).restriction
    ((stabilizerSectionAction U ⟨α t, hU⟩).hom.toAlgHom b - b)) ε
  rw [restriction_sectionDisplacement (c.map i) (α t) hi hU b]
  exact hb

end DomainAutomorphism

end Langlands.Analytic.PresentedAffinoidAlgebra
