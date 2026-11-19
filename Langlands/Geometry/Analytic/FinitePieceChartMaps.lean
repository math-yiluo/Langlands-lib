import Langlands.Geometry.Analytic.AffineAnalytificationLocalDomainMaps
import Langlands.Geometry.Analytic.WeightedPowerBounds

/-! # Bounded chart maps into complete normed algebras -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffineAnalytification.FinitePieceLocal

open Set Topology PresentedAffinoidAlgebra AnalyticAffineSpace IndexedAffinoidAtlas

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
  (E : Type w) [NormedCommRing E] [NormedAlgebra K E]

/-! ## Radius levels admitted by an algebra map -/

/-- The images of the generators of `A` have norm at most the `m`-th radius. -/
def Admits (τ : A →ₐ[K] E) (m : ℕ) : Prop :=
  ∀ t : Fin P.arity, ‖τ (P.map (MvPolynomial.X t))‖ ≤ radius K m

omit [IsUltrametricDist K] in
theorem exists_admits (τ : A →ₐ[K] E) : ∃ m, Admits P E τ m := by
  obtain ⟨m, hm⟩ := exists_radius_gt K (∑ t, ‖τ (P.map (MvPolynomial.X t))‖)
  refine ⟨m, fun t => ?_⟩
  exact (Finset.single_le_sum (fun s _ => norm_nonneg (τ (P.map (MvPolynomial.X s))))
    (Finset.mem_univ t)).trans hm.le

omit [IsUltrametricDist K] in
theorem Admits.mono {τ : A →ₐ[K] E} {m k : ℕ} (h : Admits P E τ m) (hmk : m ≤ k) :
    Admits P E τ k :=
  fun t => (h t).trans ((radius_le_radius_iff K).2 hmk)

omit [IsUltrametricDist K] in
theorem hasBoundedMonomials_of_admits {τ : A →ₐ[K] E} {m : ℕ} (h : Admits P E τ m) :
    GeneralizedTateAlgebra.HasBoundedMonomials (polyradius K P.arity m) E
      (fun t => τ (P.map (MvPolynomial.X t))) := by
  rw [GeneralizedTateAlgebra.hasBoundedMonomials_iff_radiusBoundedPowers]
  intro t
  refine ⟨max 1 ‖(1 : E)‖, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun n => ?_⟩
  have hr : polyradius K P.arity m t = radius K m := rfl
  rw [hr]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, pow_zero, mul_one]
    exact le_max_right _ _
  · calc
      ‖τ (P.map (MvPolynomial.X t)) ^ n‖ ≤ ‖τ (P.map (MvPolynomial.X t))‖ ^ n :=
        norm_pow_le' _ hn
      _ ≤ radius K m ^ n := pow_le_pow_left₀ (norm_nonneg _) (h t) n
      _ ≤ max 1 ‖(1 : E)‖ * radius K m ^ n :=
        le_mul_of_one_le_left (pow_nonneg (radius_pos K m).le n) (le_max_left _ _)

/-! ## The bounded chart map -/

variable [IsUltrametricDist E] [CompleteSpace E] [CompleteSpace K]

/-- Weighted Tate evaluation at the generator values. -/
def tateLift (τ : A →ₐ[K] E) (m : ℕ) (h : Admits P E τ m) :
    BoundedAlgHom K (GeneralizedTateAlgebra (polyradius K P.arity m) K) E :=
  GeneralizedTateAlgebra.evaluateHom (polyradius K P.arity m) K E
    (fun t => τ (P.map (MvPolynomial.X t))) (hasBoundedMonomials_of_admits P E h)

omit [CompleteSpace K] in
theorem tateLift_polynomialMap (τ : A →ₐ[K] E) (m : ℕ) (h : Admits P E τ m)
    (p : MvPolynomial (Fin P.arity) K) :
    tateLift P E τ m h
        (GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity m) K p) =
      τ (P.map p) := by
  have hc : (tateLift P E τ m h).toAlgHom.comp
      (GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity m) K) = τ.comp P.map := by
    apply MvPolynomial.algHom_ext
    intro t
    change tateLift P E τ m h (MvPolynomial.aeval _ (MvPolynomial.X t)) =
      τ (P.map (MvPolynomial.X t))
    rw [MvPolynomial.aeval_X]
    exact GeneralizedTateAlgebra.evaluate_X (polyradius K P.arity m) K E
      (fun t => τ (P.map (MvPolynomial.X t))) t
  exact AlgHom.congr_fun hc p

/-- The bounded map from the `m`-th chart algebra extending `τ`. -/
def chartLift (τ : A →ₐ[K] E) (m : ℕ) (h : Admits P E τ m) :
    BoundedAlgHom K (algebra K P m) E :=
  PresentedAffinoidAlgebra.descendRelations K P.arity (polyradius K P.arity m)
    (PolynomialLocus.relations P (polyradius K P.arity m)) E (tateLift P E τ m h)
    (by
      rintro _ ⟨p, hp, rfl⟩
      have h0 : P.map p = 0 := RingHom.mem_ker.1 hp
      rw [tateLift_polynomialMap, h0, map_zero])

omit [CompleteSpace K] in
theorem chartLift_algebraMap (τ : A →ₐ[K] E) (m : ℕ) (h : Admits P E τ m) (a : A) :
    chartLift P E τ m h (PolynomialLocus.algebraMap P (polyradius K P.arity m) a) = τ a := by
  obtain ⟨p, rfl⟩ := P.surjective a
  rw [PolynomialLocus.algebraMap_map]
  change tateLift P E τ m h
    (GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity m) K p) = _
  rw [tateLift_polynomialMap]

omit [CompleteSpace K] in
/-- Two bounded maps out of a chart algebra into a normed algebra agree once they
agree on the image of `A`. -/
theorem chart_hom_ext {E' : Type w} [NormedCommRing E'] [NormedAlgebra K E'] (m : ℕ)
    (ψ ψ' : BoundedAlgHom K (algebra K P m) E')
    (h : ∀ a : A, ψ (PolynomialLocus.algebraMap P (polyradius K P.arity m) a) =
      ψ' (PolynomialLocus.algebraMap P (polyradius K P.arity m) a)) : ψ = ψ' := by
  apply PresentedAffinoidAlgebra.hom_ext_coordinate K E' (algebra K P m)
  intro t
  exact (congrArg ψ (LocalDomainMaps.coordinate_eq_algebraMap P m t)).trans
    ((h _).trans (congrArg ψ' (LocalDomainMaps.coordinate_eq_algebraMap P m t)).symm)

/-- The chart map from the selected representative of the `m`-th chart. -/
def representativeLift (τ : A →ₐ[K] E) (m : ℕ) (h : Admits P E τ m) :
    BoundedAlgHom K (algebra K P (representative K P m).val) E :=
  (chartLift P E τ m h).comp (representativeEquiv K P m).toBoundedAlgHom

theorem representativeLift_algebraMap (τ : A →ₐ[K] E) (m : ℕ) (h : Admits P E τ m) (a : A) :
    representativeLift P E τ m h
        (PolynomialLocus.algebraMap P (polyradius K P.arity (representative K P m).val) a) =
      τ a := by
  change chartLift P E τ m h (representativeEquiv K P m
    (PolynomialLocus.algebraMap P (polyradius K P.arity (representative K P m).val) a)) = _
  rw [representativeEquiv, equalRangeEquiv_algebraMap, chartLift_algebraMap]

/-! ## Original indices of the saturated atlas -/

/-- The saturated index of an original chart. -/
abbrev origIndex (c : ChartIndex K P) : (presentation K P).atlas.saturatedAtlas.Index :=
  (presentation K P).atlas.originalSaturatedIndex c

/-- The coordinate-algebra map into a saturated chart algebra. -/
def satMap (S : (presentation K P).atlas.saturatedAtlas.Index) :
    A →ₐ[K] (presentation K P).atlas.saturatedAtlas.algebra S :=
  LocalDomainMaps.localAlgebraMap P ((presentation K P).atlas.saturatedRepresentative S)

theorem satMap_restriction (S T : (presentation K P).atlas.saturatedAtlas.Index)
    (h : range ((presentation K P).atlas.saturatedAtlas.chart S) ⊆
      range ((presentation K P).atlas.saturatedAtlas.chart T)) (a : A) :
    (presentation K P).atlas.saturatedAtlas.restriction S T h (satMap P T a) = satMap P S a :=
  LocalDomainMaps.inclusion_localAlgebraMap P
    ((presentation K P).atlas.saturatedInclusion S T h) a

theorem range_origIndex (c : ChartIndex K P) :
    range ((presentation K P).atlas.saturatedAtlas.chart (origIndex P c)) =
      range (chart K P c.val) :=
  (presentation K P).atlas.saturatedAtlas_original_range c

theorem range_origIndex_representative (m : ℕ) :
    range ((presentation K P).atlas.saturatedAtlas.chart (origIndex P (representative K P m))) =
      range (chart K P m) :=
  (range_origIndex P _).trans (range_representative K P m)

omit [IsUltrametricDist E] [CompleteSpace E] in
theorem whole_hom_ext {E' : Type w} [NormedCommRing E'] [NormedAlgebra K E']
    (c : ChartIndex K P) (L : LocalDomain (presentation K P).atlas)
    (hL : L = ⟨c, Domain.whole K ((presentation K P).atlas.algebra c)⟩)
    (ψ ψ' : BoundedAlgHom K L.algebra E')
    (h : ∀ a, ψ (LocalDomainMaps.localAlgebraMap P L a) =
      ψ' (LocalDomainMaps.localAlgebraMap P L a)) : ψ = ψ' := by
  subst hL
  exact chart_hom_ext P c.val ψ ψ' h

/-- Bounded maps out of an original saturated chart algebra are determined on `A`. -/
theorem orig_hom_ext {E' : Type w} [NormedCommRing E'] [NormedAlgebra K E']
    (c : ChartIndex K P)
    (ψ ψ' : BoundedAlgHom K ((presentation K P).atlas.saturatedAtlas.algebra (origIndex P c)) E')
    (h : ∀ a, ψ (satMap P (origIndex P c) a) = ψ' (satMap P (origIndex P c) a)) : ψ = ψ' :=
  whole_hom_ext P c _ ((presentation K P).atlas.saturatedRepresentative_original c) ψ ψ' h

theorem exists_whole_lift (τ : A →ₐ[K] E) (m : ℕ) (h : Admits P E τ m)
    (L : LocalDomain (presentation K P).atlas)
    (hL : L = ⟨representative K P m,
      Domain.whole K ((presentation K P).atlas.algebra (representative K P m))⟩) :
    ∃ ψ : BoundedAlgHom K L.algebra E, ∀ a, ψ (LocalDomainMaps.localAlgebraMap P L a) = τ a := by
  subst hL
  exact ⟨representativeLift P E τ m h, representativeLift_algebraMap P E τ m h⟩

/-- A `K`-algebra map admitting the `m`-th radius extends boundedly to the
original saturated chart algebra representing the `m`-th chart. -/
theorem exists_orig_lift (τ : A →ₐ[K] E) (m : ℕ) (h : Admits P E τ m) :
    ∃ ψ : BoundedAlgHom K ((presentation K P).atlas.saturatedAtlas.algebra
        (origIndex P (representative K P m))) E,
      ∀ a, ψ (satMap P (origIndex P (representative K P m)) a) = τ a :=
  exists_whole_lift P E τ m h _
    ((presentation K P).atlas.saturatedRepresentative_original (representative K P m))

/-! ## Compact sets lie in charts -/

omit [IsUltrametricDist E] [CompleteSpace E] in
/-- Every compact subset of the analytification lies in all sufficiently large charts. -/
theorem exists_chart_superset {Z : Set (Space K P)} (hZ : IsCompact Z) :
    ∃ m₀, ∀ m, m₀ ≤ m → Z ⊆ range (chart K P m) := by
  have hcover : Z ⊆ ⋃ m : ℕ, interior (range (chart K P m)) := by
    intro z _
    obtain ⟨m, s, rfl⟩ := exists_chart K P (z := z)
    exact Set.mem_iUnion.2 ⟨m + 1, mem_interior_iff_mem_nhds.2
      (range_chart_mem_nhds K P ⟨s, rfl⟩)⟩
  have hdir : Directed (· ⊆ ·) fun m : ℕ => interior (range (chart K P m)) :=
    Monotone.directed_le fun m k hmk => interior_mono (range_chart_mono K P hmk)
  obtain ⟨m₀, hm₀⟩ := hZ.elim_directed_cover _ (fun _ => isOpen_interior) hcover hdir
  exact ⟨m₀, fun m hm => hm₀.trans (interior_subset.trans (range_chart_mono K P hm))⟩

end Langlands.Analytic.AffineAnalytification.FinitePieceLocal
