import Langlands.GroupScheme.IntegralModel.DiagonalScaledVector
import Langlands.GroupScheme.IntegralModel.NaturalVectorDepth

/-! # Vector depth models with independent real coordinate offsets -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {K : Type u} [Field K]
  (v : Valuation K (WithZero (Multiplicative ℤ)))
  (hv : Function.Surjective v)
  (R : ValuationSubring K) (hvR : v.valuationSubring = R)
  {n : ℕ}

include hvR in
/-- The diagonal fractional lattice has the exact valuation bound of each
independently chosen nonzero scale. -/
theorem mem_diagonalVectorLattice_iff_valuation_le
    (t : Fin n → Kˣ) (w : Fin n → K) :
    w ∈ diagonalVectorLattice R K n (fun j => (t j : K)) ↔
      ∀ j, v (w j) ≤ v (t j : K) := by
  constructor
  · rintro ⟨a, ha⟩ j
    rw [ha j, map_mul]
    have hj : v (algebraMap R K (a j)) ≤ 1 :=
      (v.mem_valuationSubring_iff _).mp (hvR.symm ▸ (a j).property)
    exact (mul_le_mul_of_nonneg_left hj zero_le).trans_eq (mul_one _)
  · intro h
    have hint (j : Fin n) : w j / (t j : K) ∈ R := by
      rw [← hvR, v.mem_valuationSubring_iff, v.map_div,
        div_le_one₀ (zero_lt_iff.mpr (v.ne_zero_iff.mpr (Units.ne_zero (t j))))]
      exact h j
    refine ⟨fun j => ⟨w j / (t j : K), hint j⟩, ?_⟩
    intro j
    change w j = (t j : K) * (w j / (t j : K))
    field_simp

/-- Coordinate `j` has integer-rounded depth `r - offset j`. The integral
polynomial group is fixed throughout the depth family. -/
def coordinateDepthVector (offset : Fin n → ℝ) (r : ℝ) :
    IntegralModel R K (VectorGroup.groupScheme (CommRingCat.of K) n) :=
  diagonalScaledVector R K n (fun j => integerDepthScale v hv ⌈r - offset j⌉)

theorem coordinateDepthVector_isSmooth (offset : Fin n → ℝ) (r : ℝ) :
    (coordinateDepthVector v hv R offset r).IsSmooth :=
  diagonalScaledVector_isSmooth R K n _

theorem coordinateDepthVector_hasGeometricallyConnectedFibres
    (offset : Fin n → ℝ) (r : ℝ) :
    (coordinateDepthVector v hv R offset r).HasGeometricallyConnectedFibres :=
  diagonalScaledVector_hasGeometricallyConnectedFibres R K n _

include hvR in
/-- The actual integral-point image has the separately rounded coordinate
valuation bounds, including negative and nonintegral depths and offsets. -/
theorem coordinateDepthVector_mem_integralPoints
    (offset : Fin n → ℝ) (r : ℝ)
    (g : rationalPoints (VectorGroup.groupScheme (CommRingCat.of K) n)) :
    g ∈ (coordinateDepthVector v hv R offset r).integralPoints ↔
      ∀ j, v ((VectorGroup.sectionCoordinates (CommRingCat.of K) n g).toAdd j) ≤
        WithZero.exp (-⌈r - offset j⌉) := by
  rw [coordinateDepthVector, diagonalScaledVector_mem_integralPoints,
    mem_diagonalVectorLattice_iff_valuation_le v R hvR]
  simp only [valuation_integerDepthScale]

include hvR in
/-- These are exactly the independent additive depth thresholds. -/
theorem coordinateDepthVector_mem_integralPoints_iff_value
    (hH : HenselianLocalRing v.valuationSubring)
    (offset : Fin n → ℝ) (r : ℝ)
    (g : rationalPoints (VectorGroup.groupScheme (CommRingCat.of K) n)) :
    g ∈ (coordinateDepthVector v hv R offset r).integralPoints ↔
      ∀ j, ((r - offset j : ℝ) : WithTop ℝ) ≤
        FieldTheory.henselianIntegerAddValuation v hH K
          ((VectorGroup.sectionCoordinates (CommRingCat.of K) n g).toAdd j) := by
  rw [coordinateDepthVector_mem_integralPoints v hv R hvR]
  exact forall_congr' fun j =>
    (real_le_henselianIntegerAddValuation_iff v hH (r - offset j) _).symm

/-- The integral coefficient in each coordinate of the deeper-to-shallower
identity extension. -/
def coordinateDepthVectorCoefficient (offset : Fin n → ℝ)
    {r s : ℝ} (h : r ≤ s) : Fin n → R :=
  fun j => integerDepthVectorCoefficient v hv R hvR (sub_le_sub_right h (offset j))

/-- The explicit integral diagonal transition extends the generic identity. -/
def coordinateDepthVectorTransition (offset : Fin n → ℝ)
    {r s : ℝ} (h : r ≤ s) :
    (coordinateDepthVector v hv R offset s).Hom
      (coordinateDepthVector v hv R offset r) (𝟙 _) :=
  diagonalScaledVectorTransition
    (fun j => integerDepthScale v hv ⌈s - offset j⌉)
    (fun j => integerDepthScale v hv ⌈r - offset j⌉)
    (coordinateDepthVectorCoefficient v hv R hvR offset h) (by
      intro j
      change (_ / (integerDepthScale v hv ⌈r - offset j⌉ : K)) * _ = _
      exact div_mul_cancel₀ _ (Units.ne_zero _))

include hvR in
/-- Every compatible identity extension has the actual diagonal transition's
smooth connected unipotent special-fibre kernel. -/
theorem coordinateDepthVector_kernel_properties
    (offset : Fin n → ℝ) {r s : ℝ} (h : r ≤ s)
    (φ : (coordinateDepthVector v hv R offset s).Hom
      (coordinateDepthVector v hv R offset r) (𝟙 _)) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) := by
  apply diagonalScaledVector_kernel_properties
    (fun j => integerDepthScale v hv ⌈s - offset j⌉)
    (fun j => integerDepthScale v hv ⌈r - offset j⌉)
    (coordinateDepthVectorCoefficient v hv R hvR offset h) _ φ
  intro j
  change (_ / (integerDepthScale v hv ⌈r - offset j⌉ : K)) * _ = _
  exact div_mul_cancel₀ _ (Units.ne_zero _)

variable {U : GroupScheme (Spec (CommRingCat.of K))}
  (e : U ≅ VectorGroup.groupScheme (CommRingCat.of K) n)

/-- Transport the coordinate-offset family to the original generic group
along an actual group-scheme isomorphism. -/
def vectorIsoCoordinateDepthModel (offset : Fin n → ℝ) (r : ℝ) :
    IntegralModel R K U :=
  (coordinateDepthVector v hv R offset r).retarget e.symm

theorem vectorIsoCoordinateDepthModel_isSmooth (offset : Fin n → ℝ) (r : ℝ) :
    (vectorIsoCoordinateDepthModel v hv R e offset r).IsSmooth := by
  change Smooth (VectorGroup.groupScheme (CommRingCat.of R) n).X.hom
  exact VectorGroup.smooth _ _

theorem vectorIsoCoordinateDepthModel_hasGeometricallyConnectedFibres
    (offset : Fin n → ℝ) (r : ℝ) :
    (vectorIsoCoordinateDepthModel v hv R e offset r).HasGeometricallyConnectedFibres := by
  change GeometricallyConnected (VectorGroup.groupScheme (CommRingCat.of R) n).X.hom
  exact VectorGroup.geometricallyConnected _ _

/-- The transport changes only the generic identification, so its point
image is detected by the original actual vector isomorphism. -/
theorem vectorIsoCoordinateDepthModel_mem_integralPoints
    (offset : Fin n → ℝ) (r : ℝ) (g : rationalPoints U) :
    g ∈ (vectorIsoCoordinateDepthModel v hv R e offset r).integralPoints ↔
      rationalPoints.map e.hom g ∈ (coordinateDepthVector v hv R offset r).integralPoints := by
  rw [vectorIsoCoordinateDepthModel, retarget_integralPoints]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have he : rationalPoints.map e.hom (rationalPoints.map e.inv z) = z := by
      simp only [rationalPoints.map_apply, Category.assoc,
        ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
    exact he.symm ▸ hz
  · intro hg
    refine ⟨rationalPoints.map e.hom g, hg, ?_⟩
    simp only [Iso.symm_hom, rationalPoints.map_apply, Category.assoc,
      ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]

include hvR in
theorem vectorIsoCoordinateDepthModel_mem_integralPoints_iff_value
    (hH : HenselianLocalRing v.valuationSubring)
    (offset : Fin n → ℝ) (r : ℝ) (g : rationalPoints U) :
    g ∈ (vectorIsoCoordinateDepthModel v hv R e offset r).integralPoints ↔
      ∀ j, ((r - offset j : ℝ) : WithTop ℝ) ≤
        FieldTheory.henselianIntegerAddValuation v hH K
          ((VectorGroup.sectionCoordinates (CommRingCat.of K) n
            (rationalPoints.map e.hom g)).toAdd j) := by
  rw [vectorIsoCoordinateDepthModel_mem_integralPoints,
    coordinateDepthVector_mem_integralPoints_iff_value v hv R hvR]

/-- Transporting the generic identifications preserves the actual identity
transition on integral polynomial groups. -/
def vectorIsoCoordinateDepthTransition (offset : Fin n → ℝ)
    {r s : ℝ} (h : r ≤ s) :
    (vectorIsoCoordinateDepthModel v hv R e offset s).Hom
      (vectorIsoCoordinateDepthModel v hv R e offset r) (𝟙 _) where
  hom := (coordinateDepthVectorTransition v hv R hvR offset h).hom
  generic_comm := by
    have hc := (coordinateDepthVectorTransition v hv R hvR offset h).generic_comm
    change _ ≫ ((coordinateDepthVector v hv R offset r).genericIso.hom ≫ e.inv) =
      ((coordinateDepthVector v hv R offset s).genericIso.hom ≫ e.inv) ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc, hc, Category.comp_id]

include hvR in
/-- The every-extension kernel conclusion survives transport to the original
generic group. -/
theorem vectorIsoCoordinateDepthModel_kernel_properties
    (offset : Fin n → ℝ) {r s : ℝ} (h : r ≤ s)
    (φ : (vectorIsoCoordinateDepthModel v hv R e offset s).Hom
      (vectorIsoCoordinateDepthModel v hv R e offset r) (𝟙 _)) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) := by
  have hφ := φ.hom_eq (vectorIsoCoordinateDepthTransition v hv R hvR e offset h)
  change Smooth (kernel ((GroupScheme.baseChange (residueBaseMap R)).map φ.hom)).X.hom ∧
    ConnectedSpace (kernel ((GroupScheme.baseChange (residueBaseMap R)).map φ.hom)).X.left ∧
      IsUnipotent (kernel ((GroupScheme.baseChange (residueBaseMap R)).map φ.hom))
  rw [hφ]
  exact coordinateDepthVector_kernel_properties v hv R hvR offset h
    (coordinateDepthVectorTransition v hv R hvR offset h)

variable
  (c : ∀ X : Over (Spec (CommRingCat.of K)),
    (X ⟶ U.X) ≃* Multiplicative (Fin n → Γ(X.left, ⊤)))
  (hc : RelativeRoot.IsNaturalVectorCoordinates c)

/-- Natural vector coordinates on all scheme tests supply the required
actual isomorphism for the coordinate-offset family. -/
def naturalCoordinateDepthModel (offset : Fin n → ℝ) (r : ℝ) :
    IntegralModel R K U :=
  vectorIsoCoordinateDepthModel v hv R (RelativeRoot.vectorGroupIso c hc) offset r

include hvR in
/-- In the original all-test coordinates, the integral-point image is exactly
the prescribed independent additive depth bounds. -/
theorem naturalCoordinateDepthModel_mem_integralPoints_iff_value
    (hH : HenselianLocalRing v.valuationSubring)
    (offset : Fin n → ℝ) (r : ℝ) (g : rationalPoints U) :
    g ∈ (naturalCoordinateDepthModel v hv R c hc offset r).integralPoints ↔
      ∀ j, ((r - offset j : ℝ) : WithTop ℝ) ≤
        FieldTheory.henselianIntegerAddValuation v hH K
          ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
            ((c (Over.mk (𝟙 _)) g).toAdd j)) := by
  rw [naturalCoordinateDepthModel,
    vectorIsoCoordinateDepthModel_mem_integralPoints_iff_value v hv R hvR]
  exact forall_congr' fun j => by rw [sectionCoordinates_vectorGroupIso]

end Langlands.GroupScheme.IntegralModel
