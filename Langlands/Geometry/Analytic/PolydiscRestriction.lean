import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalRepresentationProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeSeriesMap
import Langlands.Geometry.Analytic.AtlasIntersectionFiniteRecognition

/-! # Closed polydiscs of smaller radius as affinoid domains -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open GeneralizedTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

namespace Polydisc

variable {d : ℕ} (s t : PositivePolyradius (Fin d)) (hts : ∀ i, t i ≤ s i)

/-- The coefficient-preserving restriction from the closed polydisc of
polyradius `s` to the closed polydisc of the smaller polyradius `t`. -/
def restriction : BoundedAlgHom K (polydisc K d s) (polydisc K d t) := by
  letI := (polydisc K d s).ideal_closed
  exact BoundedAlgHom.liftQuotient K (polydisc K d s).ideal
    ((presentationMap K (polydisc K d t)).comp (boundedRestrictRadius s t hts K))
    (by
      intro a ha
      have ha0 : a = 0 := ha
      rw [ha0, map_zero])

@[simp]
theorem restriction_presentationMap (f : GeneralizedTateAlgebra s K) :
    restriction s t hts (presentationMap K (polydisc K d s) f) =
      presentationMap K (polydisc K d t) (restrictRadius s t hts K f) := rfl

@[simp]
theorem restriction_coordinate (i : Fin d) :
    restriction s t hts (coordinate K (polydisc K d s) i) =
      coordinate K (polydisc K d t) i := by
  change presentationMap K (polydisc K d t) (restrictRadius s t hts K (X s K i)) = _
  rw [restrictRadius_X]
  rfl

theorem restriction_self :
    restriction (K := K) s s (fun _ => le_rfl) = BoundedAlgHom.id K (polydisc K d s) := by
  apply hom_ext_coordinate
  intro i
  exact restriction_coordinate s s (fun _ => le_rfl) i

theorem restriction_trans (q : PositivePolyradius (Fin d)) (hqt : ∀ i, q i ≤ t i) :
    restriction (K := K) s q (fun i => (hqt i).trans (hts i)) =
      (restriction t q hqt).comp (restriction s t hts) := by
  apply hom_ext_coordinate
  intro i
  change _ = restriction t q hqt (restriction s t hts (coordinate K (polydisc K d s) i))
  exact (restriction_coordinate s q _ i).trans ((restriction_coordinate t q hqt i).symm.trans
    (congrArg (fun a => restriction t q hqt a) (restriction_coordinate s t hts i).symm))

/-- The Weierstrass chart `{x | x(Tᵢ) ≤ tᵢ}` of the larger polydisc. Its
denominator is `1` and its numerators are the coordinates. -/
def weierstrassChart : RationalChart K (polydisc K d s) where
  arity := d
  radii := t
  denominator := 1
  numerators := fun i => X s K i
  generates := by
    apply Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_insert _ _))
    rw [map_one]
    exact isUnit_one

theorem weierstrassChart_locus :
    (weierstrassChart (K := K) s t).locus =
      {x | ∀ i, x (coordinate K (polydisc K d s) i) ≤ t i} := by
  ext x
  change (∀ i, x (presentationMap K (polydisc K d s) (X s K i)) ≤
    t i * x (presentationMap K (polydisc K d s) 1)) ↔ _
  simp only [map_one, mul_one]
  rfl

private theorem one_norm_le (A : PresentedAffinoidAlgebra K) : ‖(1 : A)‖ ≤ 1 :=
  norm_one_le K A

private theorem coordinate_bounded :
    HasBoundedMonomials t (polydisc K d t) (fun i => coordinate K (polydisc K d t) i) :=
  ⟨1, zero_lt_one, fun e => by
    rw [one_mul]
    exact monomialValue_norm_le_weight t _ (one_norm_le _) _
      (fun i => norm_coordinate_le K (polydisc K d t) i) e⟩

private theorem fraction_bounded :
    HasBoundedMonomials t (weierstrassChart (K := K) s t).algebra
      (fun i => RationalPresentation.fraction K (polydisc K d s) t 1 (fun i => X s K i) i) :=
  ⟨1, zero_lt_one, fun e => by
    rw [one_mul]
    exact monomialValue_norm_le_weight t _ (one_norm_le _) _
      (fun i => RationalPresentation.norm_fraction_le K (polydisc K d s) t 1
        (fun i => X s K i) i) e⟩

variable [CompleteSpace K]

/-- From the Weierstrass chart algebra to the smaller polydisc: the base
polydisc is restricted and each new coordinate goes to the same coordinate. -/
def fromChart : BoundedAlgHom K (weierstrassChart (K := K) s t).algebra (polydisc K d t) :=
  RationalPresentation.liftFromBase K (polydisc K d s) t 1 (fun i => X s K i) _
    (restriction s t hts) (fun i => coordinate K (polydisc K d t) i)
    (coordinate_bounded t) (by
      intro i
      rw [map_one, map_one, one_mul]
      exact (restriction_coordinate s t hts i).symm)

theorem fromChart_comp_baseMap :
    (fromChart s t hts).comp (weierstrassChart (K := K) s t).baseMap = restriction s t hts :=
  RationalPresentation.liftFromBase_comp_baseMap K (polydisc K d s) t 1 (fun i => X s K i) _
    _ _ _ _

/-- From the smaller polydisc to the Weierstrass chart algebra: each coordinate
goes to the corresponding new fraction coordinate. -/
def toChart : BoundedAlgHom K (polydisc K d t) (weierstrassChart (K := K) s t).algebra := by
  letI := (polydisc K d t).ideal_closed
  exact BoundedAlgHom.liftQuotient K (polydisc K d t).ideal
    (evaluateHom t K _ _ (fraction_bounded s t))
    (by
      intro a ha
      have ha0 : a = 0 := ha
      rw [ha0, map_zero])

theorem toChart_coordinate (i : Fin d) :
    toChart s t (coordinate K (polydisc K d t) i) =
      RationalPresentation.fraction K (polydisc K d s) t 1 (fun i => X s K i) i :=
  evaluate_X t K _ _ i

theorem fromChart_toChart (a : polydisc K d t) :
    fromChart s t hts (toChart s t a) = a := by
  have h : (fromChart s t hts).comp (toChart s t) = BoundedAlgHom.id K (polydisc K d t) := by
    apply hom_ext_coordinate
    intro i
    change fromChart s t hts (toChart s t (coordinate K (polydisc K d t) i)) = _
    exact (congrArg (fun a => fromChart s t hts a) (toChart_coordinate s t i)).trans
      (RationalPresentation.liftFromBase_fraction K (polydisc K d s) t 1
        (fun i => X s K i) _ _ _ _ _ i)
  exact congrArg (fun φ : BoundedAlgHom K (polydisc K d t) (polydisc K d t) => φ a) h

theorem toChart_fromChart (b : (weierstrassChart (K := K) s t).algebra) :
    toChart s t (fromChart s t hts b) = b := by
  have h : (toChart s t).comp (fromChart s t hts) =
      BoundedAlgHom.id K (weierstrassChart (K := K) s t).algebra := by
    apply RationalPresentation.hom_ext_base K (polydisc K d s) t 1 (fun i => X s K i) _
      (weierstrassChart (K := K) s t).generates
    apply hom_ext_coordinate
    intro i
    change toChart s t (fromChart s t hts
      ((weierstrassChart (K := K) s t).baseMap (coordinate K (polydisc K d s) i))) =
        (weierstrassChart (K := K) s t).baseMap (coordinate K (polydisc K d s) i)
    have hb := congrArg (fun φ : BoundedAlgHom K (polydisc K d s) (polydisc K d t) =>
      φ (coordinate K (polydisc K d s) i)) (fromChart_comp_baseMap s t hts)
    change fromChart s t hts
      ((weierstrassChart (K := K) s t).baseMap (coordinate K (polydisc K d s) i)) =
        restriction s t hts (coordinate K (polydisc K d s) i) at hb
    rw [hb]
    exact (congrArg (fun a => toChart s t a) (restriction_coordinate s t hts i)).trans
      ((toChart_coordinate s t i).trans
        (RationalPresentation.weierstrass_fraction K (polydisc K d s) t (fun i => X s K i) i))
  exact congrArg (fun φ : BoundedAlgHom K _ _ => φ b) h

/-- The Weierstrass chart algebra is boundedly isomorphic to the smaller polydisc. -/
def chartEquiv :
    BoundedAlgEquiv K (weierstrassChart (K := K) s t).algebra (polydisc K d t) :=
  BoundedAlgEquiv.ofHomInv (fromChart s t hts) (toChart s t)
    (toChart_fromChart s t hts) (fromChart_toChart s t hts)

/-- Radius restriction represents the closed subpolydisc `{x | x(Tᵢ) ≤ tᵢ}`
against every finite positive-polyradius affinoid test. -/
theorem represents_restriction :
    Represents K (restriction (K := K) s t hts)
      {x | ∀ i, x (coordinate K (polydisc K d s) i) ≤ t i} := by
  have h := (RationalChart.represents (weierstrassChart (K := K) s t)).postcomp_equiv
    (chartEquiv s t hts)
  have heq : (chartEquiv s t hts).toBoundedAlgHom.comp
      (weierstrassChart (K := K) s t).baseMap = restriction s t hts :=
    fromChart_comp_baseMap s t hts
  rw [heq, weierstrassChart_locus] at h
  exact h

theorem range_comap_restriction :
    Set.range (BanachSpectrum.comap (restriction (K := K) s t hts).toBoundedRingHom) =
      {x | ∀ i, x (coordinate K (polydisc K d s) i) ≤ t i} :=
  (represents_restriction s t hts).2.1

end Polydisc

end Langlands.Analytic.PresentedAffinoidAlgebra
