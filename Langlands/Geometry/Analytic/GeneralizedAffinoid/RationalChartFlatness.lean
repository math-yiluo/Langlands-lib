import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormStabilizer
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeSeriesFlatness
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomainComposition
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainFlatnessReduction
import Mathlib.Topology.Order.Compact

/-! # Flatness of rational chart restrictions -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace RationalChart

/-- A domain inside a rational chart has flat structural map over the original
base when both the chart and the inner domain do. -/
theorem flat_extendDomain {A : PresentedAffinoidAlgebra K} (d : RationalChart K A)
    (U : Domain K d.algebra) (hd : d.baseMap.toAlgHom.toRingHom.Flat)
    (hU : U.baseMap.toAlgHom.toRingHom.Flat) :
    (d.extendDomain U).baseMap.toAlgHom.toRingHom.Flat :=
  hd.comp hU

theorem range_spectrumMap {A : PresentedAffinoidAlgebra K} (d : RationalChart K A) :
    Set.range d.spectrumMap = d.locus :=
  d.represents.2.1

/-- Extending the pullback of a chart `e` along a chart `L` describes the
intersection of the two loci. -/
theorem extendDomain_pullback_locus {A : PresentedAffinoidAlgebra K}
    (L e : RationalChart K A) :
    (L.extendDomain (pullback L.baseMap e).toDomain).locus = e.locus ∩ L.locus := by
  rw [extendDomain_locus, toDomain_locus, pullback_locus]
  change L.spectrumMap '' (L.spectrumMap ⁻¹' e.locus) = _
  rw [Set.image_preimage_eq_inter_range, range_spectrumMap]

/-- If the locus of `d` is the intersection of the loci of `e` and `L`, then
flatness of `L` and of the pullback of `e` along `L` gives flatness of `d`. -/
theorem flat_baseMap_of_locus_eq_inter {A : PresentedAffinoidAlgebra K}
    (d L e : RationalChart K A) (h : d.locus = e.locus ∩ L.locus)
    (hL : L.baseMap.toAlgHom.toRingHom.Flat)
    (he : (pullback L.baseMap e).baseMap.toAlgHom.toRingHom.Flat) :
    d.baseMap.toAlgHom.toRingHom.Flat :=
  Domain.flat_baseMap_of_locus_eq (L.extendDomain (pullback L.baseMap e).toDomain) d.toDomain
    (by rw [extendDomain_pullback_locus, toDomain_locus, h])
    (flat_extendDomain L _ hL he)

/-- Charts with one fraction coordinate have flat structural maps. -/
theorem flat_baseMap_of_arity_eq_one {A : PresentedAffinoidAlgebra K}
    (d : RationalChart K A) (h : d.arity = 1) : d.baseMap.toAlgHom.toRingHom.Flat := by
  obtain ⟨m, r, g, f, hgen⟩ := d
  change m = 1 at h
  subst h
  exact flat_rationalPresentation_baseMap A r g f hgen

omit [CompleteSpace K] in
theorem generatesUnitIdeal_of_isUnit {B : PresentedAffinoidAlgebra K} {m : ℕ}
    (g : GeneralizedTateAlgebra B.polyradius K) (f : Fin m → GeneralizedTateAlgebra B.polyradius K)
    (hg : IsUnit (presentationMap K B g)) : RationalPresentation.GeneratesUnitIdeal K B g f :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_insert _ _)) hg

/-- Charts whose denominator class is a unit have flat structural maps, by
induction on the number of fraction coordinates. -/
theorem flat_baseMap_of_isUnit_denominator : ∀ (m : ℕ) (B : PresentedAffinoidAlgebra K)
    (d : RationalChart K B), d.arity = m → IsUnit (presentationMap K B d.denominator) →
      d.baseMap.toAlgHom.toRingHom.Flat
  | 0, B, d, hm, _ => by
      refine Domain.flat_baseMap_of_locus_eq (Domain.whole K B) d.toDomain ?_
        (RingHom.Flat.id B)
      change Set.univ = d.locus
      exact (Set.eq_univ_of_forall fun x j => absurd j.isLt (by omega)).symm
  | m + 1, B, d, hm, hu => by
      let r₁ : PositivePolyradius (Fin 1) :=
        ⟨fun _ => d.radii ⟨0, by omega⟩, fun _ => d.radii.positive _⟩
      let d₁ : RationalChart K B :=
        { arity := 1
          radii := r₁
          denominator := d.denominator
          numerators := fun _ => d.numerators ⟨0, by omega⟩
          generates := generatesUnitIdeal_of_isUnit _ _ hu }
      let r' : PositivePolyradius (Fin m) :=
        ⟨fun j => d.radii ⟨j + 1, by omega⟩, fun _ => d.radii.positive _⟩
      let d' : RationalChart K B :=
        { arity := m
          radii := r'
          denominator := d.denominator
          numerators := fun j => d.numerators ⟨j + 1, by omega⟩
          generates := generatesUnitIdeal_of_isUnit _ _ hu }
      refine flat_baseMap_of_locus_eq_inter d d₁ d' ?_ (flat_baseMap_of_arity_eq_one d₁ rfl) ?_
      · ext x
        constructor
        · intro hx
          exact ⟨fun _ => hx _, fun _ => hx _⟩
        · rintro ⟨h', h₁⟩ ⟨j, hj⟩
          rcases j with _ | j
          · exact h₁ 0
          · exact h' ⟨j, show j < m by omega⟩
      · refine flat_baseMap_of_isUnit_denominator m _ _ rfl ?_
        rw [pullback_denominator_class]
        exact hu.map d₁.baseMap.toAlgHom

omit [CompleteSpace K] in
/-- Every point of a rational chart locus is positive on the denominator. -/
theorem pos_denominator_of_mem_locus {A : PresentedAffinoidAlgebra K} (d : RationalChart K A)
    {x : BanachSpectrum A} (hx : x ∈ d.locus) : 0 < x (presentationMap K A d.denominator) := by
  rcases (apply_nonneg x.toMulRingSeminorm (presentationMap K A d.denominator)).lt_or_eq
    with h | h
  · exact h
  exfalso
  have hker : Ideal.span (insert (presentationMap K A d.denominator)
      (Set.range fun j => presentationMap K A (d.numerators j))) ≤ BanachSpectrum.kernel x := by
    rw [Ideal.span_le]
    rintro _ (rfl | ⟨j, rfl⟩)
    · exact h.symm
    · show x (presentationMap K A (d.numerators j)) = 0
      exact le_antisymm ((hx j).trans (by rw [← h, mul_zero]))
        (apply_nonneg x.toMulRingSeminorm _)
  have h1 : (1 : A) ∈ BanachSpectrum.kernel x := hker (d.generates ▸ Submodule.mem_top)
  have h1' : x 1 = 0 := h1
  rw [map_one x.toMulRingSeminorm] at h1'
  exact one_ne_zero h1'

/-- Every rational chart of a presented affinoid algebra has a flat
structural map. -/
theorem flat_baseMap {A : PresentedAffinoidAlgebra K} (d : RationalChart K A) :
    d.baseMap.toAlgHom.toRingHom.Flat := by
  obtain ⟨c, hc, hcx⟩ := d.exists_pos_le_denominator
  let L : RationalChart K A :=
    { arity := 1
      radii := ⟨fun _ => c⁻¹, fun _ => inv_pos.mpr hc⟩
      denominator := d.denominator
      numerators := fun _ => 1
      generates := by
        apply (Ideal.eq_top_iff_one _).mpr
        apply Ideal.subset_span
        right
        exact ⟨0, map_one (presentationMap K A).toAlgHom⟩ }
  refine flat_baseMap_of_locus_eq_inter d L d ?_ (flat_baseMap_of_arity_eq_one L rfl) ?_
  · refine (Set.inter_eq_left.mpr fun x hx => show x ∈ L.locus from fun j => ?_).symm
    change x ((presentationMap K A).toAlgHom 1) ≤
      c⁻¹ * x (presentationMap K A d.denominator)
    rw [map_one, map_one x.toMulRingSeminorm, ← div_eq_inv_mul, le_div_iff₀ hc, one_mul]
    exact hcx x hx
  · refine flat_baseMap_of_isUnit_denominator _ _ _ rfl ?_
    rw [pullback_denominator_class]
    have heq := RationalPresentation.fraction_equation K A L.radii L.denominator
      L.numerators 0
    refine IsUnit.of_mul_eq_one (RationalPresentation.fraction K A L.radii L.denominator
      L.numerators 0) ?_
    refine heq.trans ?_
    change (RationalPresentation.baseMap K A L.radii L.denominator L.numerators).toAlgHom
      ((presentationMap K A).toAlgHom 1) = 1
    rw [map_one, map_one]

end RationalChart

end Langlands.Analytic.PresentedAffinoidAlgebra
