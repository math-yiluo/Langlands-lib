import Langlands.Geometry.FormalGroup.TruncatedPoints

/-! # Formal coordinate maps from natural maps of nilpotent points -/

noncomputable section

universe v

namespace Langlands.FormalGroup

open CategoryTheory MvPolynomial

variable {R : Type v} [CommRing R] {σ τ : Type} [Finite σ] [Finite τ]

/-- A family of maps of nilpotent tuples over all coefficient algebras that
commutes with every algebra homomorphism. -/
def IsNaturalPointMap
    (Φ : ∀ T : CommAlgCat.{v} R, SeriesPoint T σ Empty → SeriesPoint T τ Empty) : Prop :=
  ∀ {T T' : CommAlgCat.{v} R} (ψ : T ⟶ T') (x : SeriesPoint T σ Empty),
    (Φ T x).map ψ.hom.toRingHom = Φ T' (x.map ψ.hom.toRingHom)

namespace CoordinateMap

omit [Finite σ] in
/-- Evaluation of a coordinate map on all nilpotent tuples is natural. -/
theorem isNaturalPointMap_eval (F : CoordinateMap R σ τ) :
    IsNaturalPointMap (fun (T : CommAlgCat.{v} R) (x : SeriesPoint T σ Empty) =>
      SeriesPoint.eval (F.map (algebraMap R T)) x) := by
  intro T T' ψ x
  rw [SeriesPoint.map_eval, map_ringHom_comp]
  have h : ψ.hom.toRingHom.comp (algebraMap R T) = algebraMap R T' :=
    RingHom.ext ψ.hom.commutes
  rw [h]

/-- A coordinate map is determined by its values on nilpotent tuples. -/
theorem ext_of_eval {F G : CoordinateMap R σ τ}
    (h : ∀ (T : CommAlgCat.{v} R) (x : SeriesPoint T σ Empty),
      SeriesPoint.eval (F.map (algebraMap R T)) x =
        SeriesPoint.eval (G.map (algebraMap R T)) x) : F = G := by
  apply CoordinateMap.ext
  funext t
  ext μ
  let m := μ.degree + 1
  have hμ : ∀ i, μ i < m := fun i => Nat.lt_succ_of_le (Finsupp.le_degree i μ)
  have hx : ∀ i, MvPowerSeries.constantCoeff ((boxPoint R σ m).val i) ^ m = 0 := by
    intro i
    rw [constantCoeff_boxPoint]
    exact mk_X_pow_eq_zero m i
  have he := congrArg (fun p : SeriesPoint (BoxAlgebra R σ m) τ Empty =>
    MvPowerSeries.constantCoeff (p.val t)) (h (CommAlgCat.of R (BoxAlgebra R σ m)) (boxPoint R σ m))
  simp only at he
  rw [constantCoeff_eval_map F _ hx, constantCoeff_eval_map G _ hx] at he
  simp only [constantCoeff_boxPoint, aeval_mk_X] at he
  have hc := (mk_eq_mk_iff_coeff.mp he) μ hμ
  rwa [coeff_truncBox_of_mem _ hμ, coeff_truncBox_of_mem _ hμ] at hc

section Construction

variable (Φ : ∀ T : CommAlgCat.{v} R, SeriesPoint T σ Empty → SeriesPoint T τ Empty)

/-- The truncated test algebra as a coefficient algebra. -/
abbrev boxObj (m : ℕ) : CommAlgCat.{v} R := CommAlgCat.of R (BoxAlgebra R σ m)

/-- The value of the family at the universal truncated point. -/
def boxValue (m : ℕ) (t : τ) : BoxAlgebra R σ m :=
  MvPowerSeries.constantCoeff ((Φ (boxObj (σ := σ) m) (boxPoint R σ m)).val t)

/-- A polynomial representative of the value at the universal truncated point. -/
def boxRep (m : ℕ) (t : τ) : MvPolynomial σ R :=
  (Ideal.Quotient.mk_surjective (boxValue Φ m t)).choose

omit [Finite τ] in
theorem mk_boxRep (m : ℕ) (t : τ) :
    Ideal.Quotient.mk (boxIdeal R σ m) (boxRep Φ m t) = boxValue Φ m t :=
  (Ideal.Quotient.mk_surjective (boxValue Φ m t)).choose_spec

variable {Φ}

omit [Finite τ] in
theorem boxValue_factor (hΦ : IsNaturalPointMap Φ) {m m' : ℕ} (h : m ≤ m') (t : τ) :
    Ideal.Quotient.factorₐ R (boxIdeal_mono (R := R) (σ := σ) h) (boxValue Φ m' t) =
      boxValue Φ m t := by
  have hn := hΦ (T := boxObj (σ := σ) m') (T' := boxObj (σ := σ) m)
    (CommAlgCat.ofHom (Ideal.Quotient.factorₐ R (boxIdeal_mono (R := R) (σ := σ) h)))
    (boxPoint R σ m')
  have he := congrArg (fun p : SeriesPoint (BoxAlgebra R σ m) τ Empty =>
    MvPowerSeries.constantCoeff (p.val t)) hn
  simp only [CommAlgCat.hom_ofHom] at he
  rw [boxPoint_map_factor h, SeriesPoint.map_val, MvPowerSeries.constantCoeff_map] at he
  exact he

omit [Finite τ] in
theorem coeff_boxRep_eq (hΦ : IsNaturalPointMap Φ) {m m' : ℕ} (h : m ≤ m') (t : τ)
    {μ : σ →₀ ℕ} (hμ : ∀ i, μ i < m) :
    (boxRep Φ m t).coeff μ = (boxRep Φ m' t).coeff μ := by
  have he : Ideal.Quotient.mk (boxIdeal R σ m) (boxRep Φ m t) =
      Ideal.Quotient.mk (boxIdeal R σ m) (boxRep Φ m' t) := by
    rw [mk_boxRep, ← boxValue_factor hΦ h, ← mk_boxRep Φ m' t]
    rfl
  exact mk_eq_mk_iff_coeff.mp he μ hμ

variable (Φ) in
/-- The power series assembled from the values at all truncated universal points. -/
def seriesOf (t : τ) : MvPowerSeries σ R :=
  fun μ => (boxRep Φ (μ.degree + 1) t).coeff μ

theorem coeff_seriesOf (hΦ : IsNaturalPointMap Φ) {m : ℕ} (t : τ)
    {μ : σ →₀ ℕ} (hμ : ∀ i, μ i < m) :
    MvPowerSeries.coeff μ (seriesOf Φ t) = (boxRep Φ m t).coeff μ := by
  have hk : ∀ i, μ i < min m (μ.degree + 1) := fun i =>
    lt_min (hμ i) (Nat.lt_succ_of_le (Finsupp.le_degree i μ))
  change (boxRep Φ (μ.degree + 1) t).coeff μ = _
  rw [← coeff_boxRep_eq hΦ (min_le_right _ _) t hk, coeff_boxRep_eq hΦ (min_le_left _ _) t hk]

theorem boxValue_eq (hΦ : IsNaturalPointMap Φ) (m : ℕ) (t : τ) :
    boxValue Φ m t = Ideal.Quotient.mk (boxIdeal R σ m) (truncBox m (seriesOf Φ t)) := by
  rw [← mk_boxRep]
  apply mk_eq_mk_iff_coeff.mpr
  intro μ hμ
  rw [coeff_truncBox_of_mem _ hμ, coeff_seriesOf hΦ t hμ]

theorem constantCoeff_seriesOf (hΦ : IsNaturalPointMap Φ)
    (h0 : ∀ T : CommAlgCat.{v} R, Φ T SeriesPoint.zero = SeriesPoint.zero) (t : τ) :
    MvPowerSeries.constantCoeff (seriesOf Φ t) = 0 := by
  have h1 : ∀ i, (0 : σ →₀ ℕ) i < 1 := fun _ => Nat.zero_lt_one
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_seriesOf hΦ t h1]
  have hv : boxValue Φ 1 t = 0 := by
    rw [boxValue, boxPoint_one, h0]
    rfl
  rw [← mk_boxRep, ← _root_.map_zero (Ideal.Quotient.mk (boxIdeal R σ 1))] at hv
  rw [mk_eq_mk_iff_coeff.mp hv 0 h1]
  rfl

variable (Φ) in
/-- The coordinate map attached to a natural family of maps of nilpotent tuples. -/
def ofNatural (hΦ : IsNaturalPointMap Φ)
    (h0 : ∀ T : CommAlgCat.{v} R, Φ T SeriesPoint.zero = SeriesPoint.zero) :
    CoordinateMap R σ τ where
  series := seriesOf Φ
  constantCoeff_eq_zero := constantCoeff_seriesOf hΦ h0

/-- The assembled coordinate map evaluates to the given natural family. -/
theorem eval_ofNatural (hΦ : IsNaturalPointMap Φ)
    (h0 : ∀ T : CommAlgCat.{v} R, Φ T SeriesPoint.zero = SeriesPoint.zero)
    (T : CommAlgCat.{v} R) (x : SeriesPoint T σ Empty) :
    SeriesPoint.eval ((ofNatural Φ hΦ h0).map (algebraMap R T)) x = Φ T x := by
  obtain ⟨m, hx⟩ := exists_pow_eq_zero x
  apply SeriesPoint.ext_constantCoeff
  intro t
  rw [constantCoeff_eval_map _ x hx t]
  let ψ : boxObj (σ := σ) m ⟶ T := CommAlgCat.ofHom (boxLift _ hx)
  have hn := hΦ ψ (boxPoint R σ m)
  have he := congrArg (fun p : SeriesPoint T τ Empty =>
    MvPowerSeries.constantCoeff (p.val t)) hn
  simp only [ψ, CommAlgCat.hom_ofHom] at he
  rw [boxPoint_map_boxLift x hx, SeriesPoint.map_val, MvPowerSeries.constantCoeff_map] at he
  rw [← he]
  change _ = boxLift _ hx (boxValue Φ m t)
  rw [boxValue_eq hΦ, boxLift_mk]
  rfl

end Construction

end CoordinateMap

end Langlands.FormalGroup
