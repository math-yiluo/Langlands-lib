import Langlands.Geometry.Analytic.StrictTestDomain.TrivialScalarRationalLocalizationStatement
import Langlands.Geometry.Analytic.StrictTestDomain.RationalRepresentationProof
import Langlands.Geometry.Analytic.RationalLocalization

/-! # Ordinary denominator localization for trivial-scalar rational quotients: proof -/

noncomputable section

open Filter
open scoped Topology

universe u v

namespace Langlands.Analytic.StrictTestDomain

namespace TrivialScalar

open StrictTateAlgebra PresentedStrictAffinoidAlgebra

section Tate

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

omit [IsUltrametricDist K] in
/-- Under the scalar bound, every nonzero scalar has norm one. -/
theorem norm_eq_one (hK : ∀ c : K, ‖c‖ ≤ 1) {c : K} (hc : c ≠ 0) : ‖c‖ = 1 := by
  apply le_antisymm (hK c)
  have h := hK c⁻¹
  rw [norm_inv] at h
  exact (inv_le_one₀ (norm_pos_iff.mpr hc)).mp h

variable (σ : Type v)

/-- Under the scalar bound, a unit-radius restricted series has only finitely
many nonzero coefficients. -/
theorem coeff_support_finite (hK : ∀ c : K, ‖c‖ ≤ 1) (f : StrictTateAlgebra σ K) :
    {t : σ →₀ ℕ | MvPowerSeries.coeff t (series σ K f) ≠ 0}.Finite := by
  have hf : Tendsto (fun t : σ →₀ ℕ => ‖MvPowerSeries.coeff t (series σ K f)‖)
      cofinite (𝓝 0) := by
    have h := f.property
    change MvPowerSeries.IsRestricted (fun _ : σ => (1 : ℝ)) f.val at h
    simpa [MvPowerSeries.IsRestricted, Finsupp.prod, series] using h
  have hev := hf.eventually (gt_mem_nhds (show (0 : ℝ) < 1 from one_pos))
  rw [Filter.eventually_cofinite] at hev
  refine hev.subset fun t ht => ?_
  exact not_lt.mpr (norm_eq_one hK ht).ge

/-- Under the scalar bound, every nonzero series has Gauss norm at least one. -/
theorem one_le_norm (hK : ∀ c : K, ‖c‖ ≤ 1) {f : StrictTateAlgebra σ K} (hf : f ≠ 0) :
    1 ≤ ‖f‖ := by
  obtain ⟨t, ht⟩ : ∃ t, MvPowerSeries.coeff t (series σ K f) ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (Subtype.ext (MvPowerSeries.ext fun t => (h t).trans (map_zero _).symm))
  rw [← norm_eq_one hK ht]
  exact norm_coeff_le σ K f t

/-- Under the scalar bound, every subset of a strict Tate algebra is closed,
since distinct series have distance at least one. -/
theorem isClosed_set (hK : ∀ c : K, ‖c‖ ≤ 1) (S : Set (StrictTateAlgebra σ K)) :
    IsClosed S := by
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨s, hs, hxs⟩ := Metric.mem_closure_iff.mp hx 1 one_pos
  have hzero : x - s = 0 := by
    by_contra h
    have h1 := one_le_norm σ hK h
    rw [dist_eq_norm] at hxs
    linarith
  rwa [sub_eq_zero.mp hzero]

/-- Polynomials included in the strict Tate algebra by evaluation at the actual
coordinates. -/
def polynomialHom : MvPolynomial σ K →ₐ[K] StrictTateAlgebra σ K :=
  MvPolynomial.aeval (X σ K)

theorem series_polynomialHom (p : MvPolynomial σ K) :
    series σ K (polynomialHom σ p) = (p : MvPowerSeries σ K) := by
  have h : (restrictedSubalgebra σ K).val.comp (polynomialHom σ) =
      MvPolynomial.coeToMvPowerSeries.algHom K := by
    ext i : 1
    change series σ K (MvPolynomial.aeval (X σ K) (MvPolynomial.X i)) = _
    rw [MvPolynomial.aeval_X]
    simp [series, X, monomial, MvPowerSeries.X]
  exact DFunLike.congr_fun h p

theorem polynomialHom_X (i : σ) :
    polynomialHom σ (MvPolynomial.X i) = X σ K i :=
  MvPolynomial.aeval_X _ i

theorem polynomialHom_injective : Function.Injective (polynomialHom σ (K := K)) := by
  intro p q h
  apply MvPolynomial.coe_injective
  rw [← series_polynomialHom, ← series_polynomialHom, h]

/-- Under the scalar bound every Tate series is a polynomial. -/
theorem polynomialHom_surjective (hK : ∀ c : K, ‖c‖ ≤ 1) :
    Function.Surjective (polynomialHom σ (K := K)) := by
  intro f
  refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite
    (fun t => MvPowerSeries.coeff t (series σ K f)) (coeff_support_finite σ hK f)), ?_⟩
  apply Subtype.ext
  change series σ K (polynomialHom σ _) = series σ K f
  rw [series_polynomialHom]
  ext t
  rw [MvPolynomial.coeff_coe]
  rfl

/-- Under the scalar bound the polynomial inclusion is an algebra equivalence. -/
def polynomialEquiv (hK : ∀ c : K, ‖c‖ ≤ 1) :
    MvPolynomial σ K ≃ₐ[K] StrictTateAlgebra σ K :=
  AlgEquiv.ofBijective (polynomialHom σ)
    ⟨polynomialHom_injective σ, polynomialHom_surjective σ hK⟩

end Tate

section Localization

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  (hK : ∀ c : K, ‖c‖ ≤ 1) (P : PresentedStrictAffinoidAlgebra K)
  (m : ℕ) (g : P) (f : Fin m → P)

/-- The images of the coordinates in the ordinary localization: an old
coordinate goes to its class in `P`, and the new coordinate `Y_j` goes to
`f_j / g`. -/
def values : Fin (P.arity + m) → Localization.Away g :=
  Fin.append
    (fun i => algebraMap P (Localization.Away g)
      (RationalLocalization.modelEquiv K P
        (coordinate K (RationalLocalization.model K P) i)))
    (fun j => algebraMap P (Localization.Away g) (f j) *
      IsLocalization.Away.invSelf g)

/-- Evaluation of Tate series, which are polynomials under the scalar bound,
at the coordinate values in the ordinary localization. -/
def evalHom : StrictTateAlgebra (Fin (P.arity + m)) K →+* Localization.Away g :=
  (MvPolynomial.eval₂Hom ((algebraMap P (Localization.Away g)).comp (algebraMap K P))
    (values P m g f)).comp
      (polynomialEquiv (Fin (P.arity + m)) hK).symm.toRingEquiv.toRingHom

theorem evalHom_polynomialHom (p : MvPolynomial (Fin (P.arity + m)) K) :
    evalHom hK P m g f (polynomialHom _ p) =
      MvPolynomial.eval₂Hom ((algebraMap P (Localization.Away g)).comp (algebraMap K P))
        (values P m g f) p := by
  change MvPolynomial.eval₂Hom _ _ ((polynomialEquiv (Fin (P.arity + m)) hK).symm
    (polynomialEquiv (Fin (P.arity + m)) hK p)) = _
  rw [AlgEquiv.symm_apply_apply]

theorem evalHom_X (k : Fin (P.arity + m)) :
    evalHom hK P m g f (X (Fin (P.arity + m)) K k) = values P m g f k := by
  rw [← polynomialHom_X, evalHom_polynomialHom, MvPolynomial.eval₂Hom_X']

theorem evalHom_algebraMap (c : K) :
    evalHom hK P m g f (algebraMap K _ c) =
      algebraMap P (Localization.Away g) (algebraMap K P c) := by
  rw [← (polynomialHom (Fin (P.arity + m)) (K := K)).commutes c, evalHom_polynomialHom,
    MvPolynomial.algebraMap_eq, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]

variable [CompleteSpace K]

theorem evalHom_adjoinVariables (h : StrictTateAlgebra (Fin P.arity) K) :
    evalHom hK P m g f (WeierstrassPresentation.adjoinVariables K P.arity m h) =
      algebraMap P (Localization.Away g) (RationalLocalization.modelEquiv K P
        (presentationMap K (RationalLocalization.model K P) h)) := by
  have key : ((evalHom hK P m g f).comp
      (WeierstrassPresentation.adjoinVariables K P.arity m).toAlgHom.toRingHom).comp
        (polynomialHom (Fin P.arity) (K := K)).toRingHom =
      ((algebraMap P (Localization.Away g)).comp
        ((RationalLocalization.modelEquiv K P).toAlgEquiv.toAlgHom.toRingHom.comp
          (presentationMap K (RationalLocalization.model K P)).toAlgHom.toRingHom)).comp
        (polynomialHom (Fin P.arity) (K := K)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change evalHom hK P m g f (WeierstrassPresentation.adjoinVariables K P.arity m
          (polynomialHom _ (MvPolynomial.C c))) =
        algebraMap P (Localization.Away g) (RationalLocalization.modelEquiv K P
          (presentationMap K (RationalLocalization.model K P)
            (polynomialHom _ (MvPolynomial.C c))))
      simp only [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgEquiv.commutes,
        evalHom_algebraMap]
    · intro i
      change evalHom hK P m g f (WeierstrassPresentation.adjoinVariables K P.arity m
          (polynomialHom (Fin P.arity) (K := K) (MvPolynomial.X i))) =
        algebraMap P (Localization.Away g) (RationalLocalization.modelEquiv K P
          (presentationMap K (RationalLocalization.model K P)
            (polynomialHom (Fin P.arity) (K := K) (MvPolynomial.X i))))
      rw [polynomialHom_X, WeierstrassPresentation.adjoinVariables_X, evalHom_X, values,
        Fin.append_left]
      rfl
  obtain ⟨p, rfl⟩ := polynomialHom_surjective (Fin P.arity) hK h
  exact DFunLike.congr_fun key p

/-- Evaluation kills the old relations and the rational relations
`g * Y_j - f_j`. -/
theorem evalHom_relation {r : StrictTateAlgebra (Fin (P.arity + m)) K}
    (hr : r ∈ RationalPresentation.relations K P.arity m P.ideal
      (RationalLocalization.seriesLift K P g)
      (fun j => RationalLocalization.seriesLift K P (f j))) :
    evalHom hK P m g f r = 0 := by
  rcases hr with ⟨h, hh, rfl⟩ | ⟨j, rfl⟩
  · rw [evalHom_adjoinVariables, presentationMap_relation K P.arity _ hh, map_zero, map_zero]
  · rw [map_sub, map_mul, evalHom_adjoinVariables, evalHom_adjoinVariables, evalHom_X,
      RationalLocalization.modelEquiv_presentationMap_seriesLift,
      RationalLocalization.modelEquiv_presentationMap_seriesLift, values, Fin.append_right]
    linear_combination (algebraMap P (Localization.Away g) (f j)) *
      IsLocalization.Away.mul_invSelf (S := Localization.Away g) g

/-- The rational quotient maps to the ordinary localization by evaluation.
Under the scalar bound the relation ideal is already closed. -/
def quotientEval :
    RationalLocalization.algebra K P m g f →+* Localization.Away g :=
  Ideal.Quotient.lift (RationalLocalization.algebra K P m g f).ideal
    (evalHom hK P m g f) (by
      intro r hr
      change r ∈ (Ideal.span (RationalPresentation.relations K P.arity m P.ideal
        (RationalLocalization.seriesLift K P g)
        (fun j => RationalLocalization.seriesLift K P (f j)))).closure at hr
      rw [Ideal.closure_eq_of_isClosed _ (isClosed_set _ hK _)] at hr
      exact RingHom.mem_ker.mp ((Ideal.span_le.mpr fun r hr =>
        RingHom.mem_ker.mpr (evalHom_relation hK P m g f hr)) hr))

theorem quotientEval_presentationMap (r : StrictTateAlgebra (Fin (P.arity + m)) K) :
    quotientEval hK P m g f
      (presentationMap K (RationalLocalization.algebra K P m g f) r) =
      evalHom hK P m g f r :=
  rfl

theorem quotientEval_baseMap (a : P) :
    quotientEval hK P m g f (RationalLocalization.baseMap K P m g f a) =
      algebraMap P (Localization.Away g) a := by
  obtain ⟨h, hh⟩ := presentationMap_surjective K (RationalLocalization.model K P)
    ((RationalLocalization.modelEquiv K P).symm a)
  have ha : RationalLocalization.modelEquiv K P
      (presentationMap K (RationalLocalization.model K P) h) = a := by
    rw [hh, BoundedAlgEquiv.apply_symm_apply]
  change quotientEval hK P m g f (RationalPresentation.baseMap K P.arity m P.ideal
    (RationalLocalization.seriesLift K P g)
    (fun j => RationalLocalization.seriesLift K P (f j))
    ((RationalLocalization.modelEquiv K P).symm a)) = _
  rw [← hh]
  change quotientEval hK P m g f (presentationMap K (RationalLocalization.algebra K P m g f)
    (WeierstrassPresentation.adjoinVariables K P.arity m h)) = _
  rw [quotientEval_presentationMap]
  exact (evalHom_adjoinVariables hK P m g f h).trans (congrArg _ ha)

/-- The universal property of the ordinary localization, applied to the
structural map, whose denominator image is a unit. -/
def localizationLift (hunit : RationalLocalization.GeneratesUnitIdeal K P m g f) :
    Localization.Away g →+* RationalLocalization.algebra K P m g f :=
  IsLocalization.Away.lift g
    (g := (RationalLocalization.baseMap K P m g f).toAlgHom.toRingHom)
    (RationalLocalization.isUnit_baseMap_denominator K P m g f hunit)

theorem localizationLift_algebraMap
    (hunit : RationalLocalization.GeneratesUnitIdeal K P m g f) (a : P) :
    localizationLift P m g f hunit (algebraMap P (Localization.Away g) a) =
      RationalLocalization.baseMap K P m g f a :=
  IsLocalization.Away.lift_eq g _ a

theorem quotientEval_comp_localizationLift
    (hunit : RationalLocalization.GeneratesUnitIdeal K P m g f) :
    (quotientEval hK P m g f).comp (localizationLift P m g f hunit) = RingHom.id _ := by
  refine IsLocalization.ringHom_ext (Submonoid.powers g) (RingHom.ext fun a => ?_)
  change quotientEval hK P m g f
    (localizationLift P m g f hunit (algebraMap P _ a)) = algebraMap P _ a
  rw [localizationLift_algebraMap, quotientEval_baseMap]

theorem localizationLift_comp_quotientEval
    (hunit : RationalLocalization.GeneratesUnitIdeal K P m g f) :
    (localizationLift P m g f hunit).comp (quotientEval hK P m g f) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  have key : (((localizationLift P m g f hunit).comp (quotientEval hK P m g f)).comp
      (Ideal.Quotient.mk (RationalLocalization.algebra K P m g f).ideal)).comp
        (polynomialHom (Fin (P.arity + m)) (K := K)).toRingHom =
      ((RingHom.id _).comp
        (Ideal.Quotient.mk (RationalLocalization.algebra K P m g f).ideal)).comp
        (polynomialHom (Fin (P.arity + m)) (K := K)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change localizationLift P m g f hunit
          (evalHom hK P m g f (polynomialHom _ (MvPolynomial.C c))) =
        presentationMap K (RationalLocalization.algebra K P m g f)
          (polynomialHom _ (MvPolynomial.C c))
      rw [evalHom_polynomialHom, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
        localizationLift_algebraMap, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
        AlgHom.commutes]
      exact ((presentationMap K (RationalLocalization.algebra K P m g f)).toAlgHom.commutes c).symm
    · intro k
      change localizationLift P m g f hunit
          (evalHom hK P m g f (polynomialHom _ (MvPolynomial.X k))) =
        presentationMap K (RationalLocalization.algebra K P m g f)
          (polynomialHom (Fin (P.arity + m)) (K := K) (MvPolynomial.X k))
      rw [evalHom_polynomialHom, MvPolynomial.eval₂Hom_X', polynomialHom_X]
      change _ = coordinate K (RationalLocalization.algebra K P m g f) k
      cases k using Fin.addCases with
      | left i =>
        rw [values, Fin.append_left, localizationLift_algebraMap]
        change RationalPresentation.baseMap K P.arity m P.ideal
          (RationalLocalization.seriesLift K P g)
          (fun j => RationalLocalization.seriesLift K P (f j))
          ((RationalLocalization.modelEquiv K P).symm (RationalLocalization.modelEquiv K P
            (coordinate K (RationalLocalization.model K P) i))) = _
        rw [BoundedAlgEquiv.symm_apply_apply]
        exact RationalPresentation.baseMap_coordinate K P.arity m P.ideal _ _ i
      | right j =>
        rw [values, Fin.append_right, map_mul, localizationLift_algebraMap]
        change RationalLocalization.baseMap K P m g f (f j) *
            localizationLift P m g f hunit (IsLocalization.Away.invSelf g) =
          RationalLocalization.fractionCoordinate K P m g f j
        have h1 := RationalLocalization.coordinate_equation K P m g f j
        have h2 : RationalLocalization.baseMap K P m g f g *
            localizationLift P m g f hunit (IsLocalization.Away.invSelf g) = 1 := by
          rw [← localizationLift_algebraMap P m g f hunit, ← map_mul,
            IsLocalization.Away.mul_invSelf, map_one]
        linear_combination
          (-localizationLift P m g f hunit (IsLocalization.Away.invSelf g)) * h1 +
            RationalLocalization.fractionCoordinate K P m g f j * h2
  exact (RingHom.cancel_right (polynomialHom_surjective (Fin (P.arity + m)) hK)).mp key

/-- The evaluation and the localization lift are inverse ring equivalences. -/
def ringEquiv (hunit : RationalLocalization.GeneratesUnitIdeal K P m g f) :
    Localization.Away g ≃+* RationalLocalization.algebra K P m g f :=
  RingEquiv.ofRingHom (localizationLift P m g f hunit) (quotientEval hK P m g f)
    (localizationLift_comp_quotientEval hK P m g f hunit)
    (quotientEval_comp_localizationLift hK P m g f hunit)

include hK in
/-- Under the scalar bound the rational quotient is the ordinary localization
away from the denominator, along the structural map. -/
theorem isLocalization_away (hunit : RationalLocalization.GeneratesUnitIdeal K P m g f) :
    letI : Algebra P (RationalLocalization.algebra K P m g f) :=
      (RationalLocalization.baseMap K P m g f).toAlgHom.toRingHom.toAlgebra
    IsLocalization.Away g (RationalLocalization.algebra K P m g f) := by
  let _ : Algebra P (RationalLocalization.algebra K P m g f) :=
    (RationalLocalization.baseMap K P m g f).toAlgHom.toRingHom.toAlgebra
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers g)
    (AlgEquiv.ofRingEquiv (f := ringEquiv hK P m g f hunit)
      (localizationLift_algebraMap P m g f hunit))

end Localization

end TrivialScalar

/-- With trivial scalar norm, every rational quotient is the ordinary
localization away from its denominator. -/
theorem trivialScalarRationalLocalization :
    TrivialScalarRationalLocalizationStatement.{u} := by
  intro K _ _ _ P hK d
  exact TrivialScalar.isLocalization_away hK P d.arity d.denominator d.numerator
    d.generatesUnitIdeal

end Langlands.Analytic.StrictTestDomain
