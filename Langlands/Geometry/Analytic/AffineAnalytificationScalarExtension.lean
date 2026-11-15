import Langlands.Geometry.Analytic.AffineAnalytificationSeminorm
import Langlands.Geometry.Analytic.AffineAnalytificationMap

/-! # Restriction of analytic points along an extension of the ground field -/

noncomputable section

universe u u' v w

namespace Langlands.Analytic.AffineAnalytification

open Set Topology PresentedAffinoidAlgebra AnalyticAffineSpace

variable (K : Type u) [NontriviallyNormedField K]
  (L : Type u') [NontriviallyNormedField L] [IsUltrametricDist L]
  {A : Type v} [CommRing A] [Algebra K A] {B : Type w} [CommRing B] [Algebra L B]
  [Algebra K B]
  (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation L B)
  (f : A →ₐ[K] B)

/-! ## Generator values and radius levels -/

/-- The image under `f` of the `t`-th generator of `P`, in the `k`-th chart of `Q`. -/
def extensionValue (k : ℕ) (t : Fin P.arity) : algebra L Q k :=
  PolynomialLocus.algebraMap Q (polyradius L Q.arity k) (f (P.map (MvPolynomial.X t)))

theorem exists_extensionValue_le (k : ℕ) :
    ∃ l, ∀ t, ‖extensionValue K L P Q f k t‖ ≤ radius K l := by
  obtain ⟨l, hl⟩ := exists_radius_gt K (∑ t, ‖extensionValue K L P Q f k t‖)
  refine ⟨l, fun t => ?_⟩
  exact (Finset.single_le_sum (fun s _ => norm_nonneg (extensionValue K L P Q f k s))
    (Finset.mem_univ t)).trans hl.le

open scoped Classical in
/-- The least radius index of `K` bounding the norms of all generator values in the
`k`-th chart of `Q`. -/
def extensionMinimalLevel (k : ℕ) : ℕ :=
  Nat.find (exists_extensionValue_le K L P Q f k)

open scoped Classical in
theorem norm_extensionValue_le_minimalLevel (k : ℕ) (t : Fin P.arity) :
    ‖extensionValue K L P Q f k t‖ ≤ radius K (extensionMinimalLevel K L P Q f k) :=
  Nat.find_spec (exists_extensionValue_le K L P Q f k) t

/-- The monotone radius index of the chart of `P` receiving the `k`-th chart of `Q`. -/
def extensionLevel (k : ℕ) : ℕ :=
  (Finset.range (k + 1)).sup (extensionMinimalLevel K L P Q f)

theorem extensionMinimalLevel_le_level (k : ℕ) :
    extensionMinimalLevel K L P Q f k ≤ extensionLevel K L P Q f k :=
  Finset.le_sup (Finset.self_mem_range_succ k)

theorem extensionLevel_mono {k k' : ℕ} (h : k ≤ k') :
    extensionLevel K L P Q f k ≤ extensionLevel K L P Q f k' :=
  Finset.sup_mono (Finset.range_subset_range.2 (Nat.succ_le_succ h))

theorem norm_extensionValue_le (k : ℕ) (t : Fin P.arity) :
    ‖extensionValue K L P Q f k t‖ ≤ radius K (extensionLevel K L P Q f k) :=
  (norm_extensionValue_le_minimalLevel K L P Q f k t).trans
    ((radius_le_radius_iff K).2 (extensionMinimalLevel_le_level K L P Q f k))

/-- The generator values have weighted monomials bounded by one. -/
theorem extensionValue_hasBoundedMonomials (k : ℕ) :
    GeneralizedTateAlgebra.HasBoundedMonomials (polyradius K P.arity (extensionLevel K L P Q f k))
      (algebra L Q k) (extensionValue K L P Q f k) :=
  ⟨1, one_pos, fun d => by
    rw [one_mul]
    exact GeneralizedTateAlgebra.monomialValue_norm_le_weight _ _ (norm_one_le L _) _
      (norm_extensionValue_le K L P Q f k) d⟩

variable [NormedAlgebra K L]

/-! ## The chart algebras of `Q` as normed algebras over `K` -/

/-- The `k`-th chart algebra of `Q` as a normed `K`-algebra, by restriction of
scalars along `K → L`. This is a local instance of this file only. -/
abbrev extensionNormedAlgebra (k : ℕ) : NormedAlgebra K (algebra L Q k) :=
  NormedAlgebra.restrictScalars K L (algebra L Q k)

attribute [local instance] extensionNormedAlgebra

/-- The radius restriction between two charts of `Q`, as a bounded `K`-algebra map. -/
def extensionRestriction {k k' : ℕ} (h : k ≤ k') :
    BoundedAlgHom K (algebra L Q k') (algebra L Q k) where
  toRingHom := (restriction L Q h).toAlgHom.toRingHom
  commutes' c := (restriction L Q h).toAlgHom.commutes (algebraMap K L c)
  bounded := (restriction L Q h).bounded

omit [Algebra K B] in
theorem extensionRestriction_apply {k k' : ℕ} (h : k ≤ k') (b : algebra L Q k') :
    extensionRestriction K L Q h b = restriction L Q h b :=
  rfl

theorem extensionRestriction_extensionValue {k k' : ℕ} (h : k ≤ k') (t : Fin P.arity) :
    extensionRestriction K L Q h (extensionValue K L P Q f k' t) =
      extensionValue K L P Q f k t := by
  change PolynomialLocus.restriction Q _ _ _
    (PolynomialLocus.algebraMap Q (polyradius L Q.arity k') (f (P.map (MvPolynomial.X t)))) = _
  rw [PolynomialLocus.restriction_algebraMap]
  rfl

/-! ## The bounded chart maps over `K` -/

variable [IsUltrametricDist K] [CompleteSpace L]

/-- Weighted Tate evaluation over `K` at the generator values in a chart of `Q`. -/
def extensionTateMap (k : ℕ) :
    BoundedAlgHom K
      (GeneralizedTateAlgebra (polyradius K P.arity (extensionLevel K L P Q f k)) K)
      (algebra L Q k) :=
  GeneralizedTateAlgebra.evaluateHom (polyradius K P.arity (extensionLevel K L P Q f k)) K
    (algebra L Q k) (extensionValue K L P Q f k)
    (extensionValue_hasBoundedMonomials K L P Q f k)

theorem extensionTateMap_X (k : ℕ) (t : Fin P.arity) :
    extensionTateMap K L P Q f k
        (GeneralizedTateAlgebra.X (polyradius K P.arity (extensionLevel K L P Q f k)) K t) =
      extensionValue K L P Q f k t :=
  GeneralizedTateAlgebra.evaluate_X (polyradius K P.arity (extensionLevel K L P Q f k)) K
    (algebra L Q k) (extensionValue K L P Q f k) t

variable [IsScalarTower K L B]

/-- On polynomials, the Tate evaluation is the image under `f` followed by the
coordinate-algebra map of the chart of `Q`. -/
theorem extensionTateMap_polynomialMap (k : ℕ) (p : MvPolynomial (Fin P.arity) K) :
    extensionTateMap K L P Q f k
        (GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity (extensionLevel K L P Q f k))
          K p) =
      (PolynomialLocus.algebraMap Q (polyradius L Q.arity k) (f (P.map p)) :
        algebra L Q k) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    have h1 : (MvPolynomial.C c : MvPolynomial (Fin P.arity) K) = algebraMap K _ c := rfl
    have h2 : GeneralizedTateAlgebra.polynomialMap
        (polyradius K P.arity (extensionLevel K L P Q f k)) K (algebraMap K _ c) =
          algebraMap K _ c :=
      AlgHom.commutes _ c
    have h3 : (extensionTateMap K L P Q f k).toAlgHom (algebraMap K _ c) =
        algebraMap K (algebra L Q k) c :=
      AlgHom.commutes _ c
    have h4 : f (P.map (algebraMap K _ c)) = algebraMap L B (algebraMap K L c) := by
      rw [AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply K L B]
    rw [h1, h2, h4, h3]
    exact ((PolynomialLocus.algebraMap Q (polyradius L Q.arity k)).commutes _).symm
  | add p q hp hq =>
    simp only [map_add]
    rw [hp, hq]
  | mul_X p t hp =>
    have hX : GeneralizedTateAlgebra.polynomialMap
        (polyradius K P.arity (extensionLevel K L P Q f k)) K (MvPolynomial.X t) =
          GeneralizedTateAlgebra.X (polyradius K P.arity (extensionLevel K L P Q f k)) K t :=
      MvPolynomial.aeval_X _ t
    simp only [map_mul]
    rw [hp, hX, extensionTateMap_X]
    rfl

/-- The bounded `K`-algebra map from the `extensionLevel k`-th chart algebra of `P` to
the `k`-th chart algebra of `Q`, descended through the closed relation ideal. -/
def extensionChartMap (k : ℕ) :
    BoundedAlgHom K (algebra K P (extensionLevel K L P Q f k)) (algebra L Q k) :=
  PresentedAffinoidAlgebra.descendRelations K P.arity
    (polyradius K P.arity (extensionLevel K L P Q f k))
    (PolynomialLocus.relations P (polyradius K P.arity (extensionLevel K L P Q f k)))
    (algebra L Q k) (extensionTateMap K L P Q f k)
    (by
      rintro _ ⟨p, hp, rfl⟩
      have h0 : P.map p = 0 := RingHom.mem_ker.1 hp
      rw [extensionTateMap_polynomialMap, h0, map_zero, map_zero])

theorem extensionChartMap_presentationMap (k : ℕ)
    (g : GeneralizedTateAlgebra (polyradius K P.arity (extensionLevel K L P Q f k)) K) :
    extensionChartMap K L P Q f k
        (presentationMap K (algebra K P (extensionLevel K L P Q f k)) g) =
      extensionTateMap K L P Q f k g :=
  rfl

@[simp]
theorem extensionChartMap_coordinate (k : ℕ) (t : Fin P.arity) :
    extensionChartMap K L P Q f k (coordinate K (algebra K P (extensionLevel K L P Q f k)) t) =
      extensionValue K L P Q f k t :=
  extensionTateMap_X K L P Q f k t

/-- The chart maps are compatible with the coordinate-algebra maps and `f`. -/
@[simp]
theorem extensionChartMap_algebraMap (k : ℕ) (a : A) :
    extensionChartMap K L P Q f k
        (PolynomialLocus.algebraMap P (polyradius K P.arity (extensionLevel K L P Q f k)) a) =
      (PolynomialLocus.algebraMap Q (polyradius L Q.arity k) (f a) :
        algebra L Q k) := by
  obtain ⟨p, rfl⟩ := P.surjective a
  rw [PolynomialLocus.algebraMap_map]
  change extensionTateMap K L P Q f k
    (GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity (extensionLevel K L P Q f k))
      K p) = _
  rw [extensionTateMap_polynomialMap]

/-- The chart maps commute with the radius restrictions of both presentations. -/
theorem extensionRestriction_comp_chartMap {k k' : ℕ} (h : k ≤ k') :
    (extensionRestriction K L Q h).comp (extensionChartMap K L P Q f k') =
      (extensionChartMap K L P Q f k).comp
        (restriction K P (extensionLevel_mono K L P Q f h)) := by
  apply PresentedAffinoidAlgebra.hom_ext_coordinate
  intro t
  have e1 : extensionChartMap K L P Q f k'
      (coordinate K (algebra K P (extensionLevel K L P Q f k')) t) =
        extensionValue K L P Q f k' t :=
    extensionChartMap_coordinate K L P Q f k' t
  have e2 : restriction K P (extensionLevel_mono K L P Q f h)
      (coordinate K (algebra K P (extensionLevel K L P Q f k')) t) =
        coordinate K (algebra K P (extensionLevel K L P Q f k)) t :=
    PolynomialLocus.restriction_coordinate P _ _ _ t
  have e3 : extensionChartMap K L P Q f k
      (coordinate K (algebra K P (extensionLevel K L P Q f k)) t) =
        extensionValue K L P Q f k t :=
    extensionChartMap_coordinate K L P Q f k t
  exact (congrArg (fun b => extensionRestriction K L Q h b) e1).trans
    ((extensionRestriction_extensionValue K L P Q f h t).trans
      (e3.symm.trans (congrArg (fun a => extensionChartMap K L P Q f k a) e2).symm))

/-! ## The continuous map of analytic spaces -/

variable [CompleteSpace K]

/-- The map on one chart spectrum of `Q`. -/
def extensionSigmaMap (x : (k : ℕ) × BanachSpectrum (algebra L Q k)) : Space K P :=
  chart K P (extensionLevel K L P Q f x.1)
    (BanachSpectrum.comap (extensionChartMap K L P Q f x.1).toBoundedRingHom x.2)

theorem comap_extensionChartMap_pull {l k : ℕ} (h : l ≤ k)
    (v : BanachSpectrum (algebra L Q l)) :
    BanachSpectrum.comap (extensionChartMap K L P Q f k).toBoundedRingHom
        ((chartSystem L Q).pull h v) =
      (chartSystem K P).pull (extensionLevel_mono K L P Q f h)
        (BanachSpectrum.comap (extensionChartMap K L P Q f l).toBoundedRingHom v) := by
  apply BanachSpectrum.ext
  intro a
  change v (restriction L Q h (extensionChartMap K L P Q f k a)) =
    v (extensionChartMap K L P Q f l (restriction K P (extensionLevel_mono K L P Q f h) a))
  exact congrArg v (congrArg (fun φ : BoundedAlgHom K _ _ => φ a)
    (extensionRestriction_comp_chartMap K L P Q f h))

theorem extensionSigmaMap_pull {l k : ℕ} (h : l ≤ k) (v : BanachSpectrum (algebra L Q l)) :
    extensionSigmaMap K L P Q f ⟨k, (chartSystem L Q).pull h v⟩ =
      extensionSigmaMap K L P Q f ⟨l, v⟩ := by
  change chart K P (extensionLevel K L P Q f k)
    (BanachSpectrum.comap _ ((chartSystem L Q).pull h v)) = _
  rw [comap_extensionChartMap_pull]
  exact chart_pull K P (extensionLevel_mono K L P Q f h) _

/-- The underlying function, glued from the chart maps. -/
def extensionFun : Space L Q → Space K P :=
  Quotient.lift (extensionSigmaMap K L P Q f) (by
    intro x y hxy
    obtain ⟨l, hlx, hly, v, hx, hy⟩ := hxy
    obtain ⟨k, s⟩ := x
    obtain ⟨k', s'⟩ := y
    dsimp only at hlx hly hx hy
    subst hx hy
    exact (extensionSigmaMap_pull K L P Q f hlx v).trans
      (extensionSigmaMap_pull K L P Q f hly v).symm)

theorem continuous_extensionFun : Continuous (extensionFun K L P Q f) :=
  Continuous.quotient_lift (continuous_sigma fun k =>
    (continuous_chart K P (extensionLevel K L P Q f k)).comp
      (BanachSpectrum.comapContinuous
        (extensionChartMap K L P Q f k).toBoundedRingHom).continuous) _

/-- The continuous map `Space L Q → Space K P` induced by the `K`-algebra map `f`
from `A` to the `L`-algebra `B`. -/
def extensionMap : C(Space L Q, Space K P) :=
  ⟨extensionFun K L P Q f, continuous_extensionFun K L P Q f⟩

@[simp]
theorem extensionMap_chart (k : ℕ) (x : BanachSpectrum (algebra L Q k)) :
    extensionMap K L P Q f (chart L Q k x) =
      chart K P (extensionLevel K L P Q f k)
        (BanachSpectrum.comap (extensionChartMap K L P Q f k).toBoundedRingHom x) :=
  rfl

/-- The seminorm of the image of a point is the seminorm of the point composed
with `f`. -/
theorem pointSeminorm_extensionMap (y : Space L Q) (a : A) :
    pointSeminorm K P (extensionMap K L P Q f y) a = pointSeminorm L Q y (f a) := by
  obtain ⟨k, x, rfl⟩ := exists_chart L Q y
  rw [extensionMap_chart, pointSeminorm_chart, pointSeminorm_chart, chartSeminorm_apply,
    chartSeminorm_apply]
  change x (extensionChartMap K L P Q f k
    (PolynomialLocus.algebraMap P (polyradius K P.arity (extensionLevel K L P Q f k)) a)) = _
  rw [extensionChartMap_algebraMap]

/-! ## Base change of the ground field -/

section BaseChange

open scoped TensorProduct

/-- The base change of a finite polynomial presentation of `A` along `K → L`: the
`L`-algebra `L ⊗[K] A` is presented by the same number of generators `1 ⊗ xₜ`. -/
def baseChangePresentation : FinitePolynomialPresentation L (L ⊗[K] A) where
  arity := P.arity
  map := (Algebra.TensorProduct.map (AlgHom.id L L) P.map).comp
    (MvPolynomial.algebraTensorAlgEquiv K L).symm.toAlgHom
  surjective :=
    (Algebra.TensorProduct.map_surjective (AlgHom.id L L) P.map (fun x => ⟨x, rfl⟩)
      P.surjective).comp (MvPolynomial.algebraTensorAlgEquiv K L).symm.surjective

omit [IsUltrametricDist L] [IsUltrametricDist K] [CompleteSpace L] [CompleteSpace K] in
theorem baseChangePresentation_map_X (t : Fin P.arity) :
    (baseChangePresentation K L P).map (MvPolynomial.X t) =
      (1 : L) ⊗ₜ[K] P.map (MvPolynomial.X t) := by
  change Algebra.TensorProduct.map (AlgHom.id L L) P.map
    ((MvPolynomial.algebraTensorAlgEquiv K L).symm (MvPolynomial.X t)) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_symm_X, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply]

/-- The canonical continuous map from the analytification of the base change
`L ⊗[K] A` over `L` to the analytification of `A` over `K`, induced by
`a ↦ 1 ⊗ a`. -/
def baseChangeMap : C(Space L (baseChangePresentation K L P), Space K P) :=
  extensionMap K L P (baseChangePresentation K L P) Algebra.TensorProduct.includeRight

/-- The seminorm of the image of a point of the base change at `a` is its seminorm
at `1 ⊗ a`. -/
theorem pointSeminorm_baseChangeMap (y : Space L (baseChangePresentation K L P)) (a : A) :
    pointSeminorm K P (baseChangeMap K L P y) a =
      pointSeminorm L (baseChangePresentation K L P) y ((1 : L) ⊗ₜ[K] a) :=
  pointSeminorm_extensionMap K L P (baseChangePresentation K L P)
    Algebra.TensorProduct.includeRight y a

end BaseChange

end Langlands.Analytic.AffineAnalytification
