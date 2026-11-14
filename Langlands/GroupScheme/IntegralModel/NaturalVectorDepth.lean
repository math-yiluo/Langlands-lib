import Langlands.GroupScheme.IntegralModel.IntegerDepthVector
import Langlands.GroupScheme.IntegralModel.SemilinearExtension
import Langlands.GroupScheme.Rational.RootSubgroupWeightCoordinates
import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Langlands.Geometry.Building.RootVectorCoordinateValuation

/-! # Actual depth models from natural vector coordinates -/

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
  (hH : HenselianLocalRing v.valuationSubring)

/-- The normalized additive value has exactly the real thresholds encoded
by integer-ceiling multiplicative valuation bounds. -/
theorem real_le_henselianIntegerAddValuation_iff (r : ℝ) (x : K) :
    (r : WithTop ℝ) ≤ FieldTheory.henselianIntegerAddValuation v hH K x ↔
      v x ≤ WithZero.exp (-⌈r⌉) := by
  by_cases hx : x = 0
  · subst x
    simp
  · have hbase := FieldTheory.henselianIntegerAddValuation_base v hH K hx
    rw [Algebra.algebraMap_self_apply] at hbase
    rw [hbase, WithTop.coe_le_coe, ← Int.ceil_le]
    calc
      ⌈r⌉ ≤ -WithZero.log (v x) ↔ WithZero.log (v x) ≤ -⌈r⌉ := by omega
      _ ↔ v x ≤ WithZero.exp (-⌈r⌉) :=
        WithZero.log_le_iff_le_exp (v.ne_zero_iff.mpr hx)

/-- The minimum of the coordinate values has the same exact coordinate ball. -/
theorem real_le_finiteVectorValue_iff {n : ℕ} (r : ℝ) (w : Fin n → K) :
    (r : WithTop ℝ) ≤ Geometry.Building.finiteVectorValue
      (FieldTheory.henselianIntegerAddValuation v hH K) w ↔
        ∀ j, v (w j) ≤ WithZero.exp (-⌈r⌉) := by
  classical
  simp only [Geometry.Building.finiteVectorValue, Finset.le_inf_iff,
    Finset.mem_univ, forall_const]
  exact forall_congr' fun j => real_le_henselianIntegerAddValuation_iff v hH r (w j)

variable (hv : Function.Surjective v)
  (R : ValuationSubring K) (hvR : v.valuationSubring = R)
  {U : GroupScheme (Spec (CommRingCat.of K))} {n : ℕ}
  (e : U ≅ VectorGroup.groupScheme (CommRingCat.of K) n)

/-- An actual vector-group isomorphism transports the explicit depth family
to an integral model of its original generic group. -/
def vectorIsoDepthModel (r : ℝ) : IntegralModel R K U :=
  (integerDepthVector v hv R n r).retarget e.symm

/-- Membership in the transported model is detected by its actual generic
vector coordinates. -/
theorem vectorIsoDepthModel_mem_integralPoints (r : ℝ) (g : rationalPoints U) :
    g ∈ (vectorIsoDepthModel v hv R e r).integralPoints ↔
      rationalPoints.map e.hom g ∈ (integerDepthVector v hv R n r).integralPoints := by
  rw [vectorIsoDepthModel, retarget_integralPoints]
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
/-- The transported models have precisely the additive coordinate-minimum
thresholds, without an assumption on the supplied root filtration. -/
theorem vectorIsoDepthModel_mem_integralPoints_iff_value (r : ℝ) (g : rationalPoints U) :
    g ∈ (vectorIsoDepthModel v hv R e r).integralPoints ↔
      (r : WithTop ℝ) ≤ Geometry.Building.finiteVectorValue
        (FieldTheory.henselianIntegerAddValuation v hH K)
        (VectorGroup.sectionCoordinates (CommRingCat.of K) n
          (rationalPoints.map e.hom g)).toAdd := by
  rw [vectorIsoDepthModel_mem_integralPoints,
    integerDepthVector_mem_integralPoints v hv R hvR,
    real_le_finiteVectorValue_iff]

/-- Smoothness of the transported depth model is the smoothness of its
unchanged polynomial integral group. -/
theorem vectorIsoDepthModel_isSmooth (r : ℝ) :
    (vectorIsoDepthModel v hv R e r).IsSmooth := by
  change Smooth (VectorGroup.groupScheme (CommRingCat.of R) n).X.hom
  exact VectorGroup.smooth _ _

/-- The transported depth model has geometrically connected fibres. -/
theorem vectorIsoDepthModel_hasGeometricallyConnectedFibres (r : ℝ) :
    (vectorIsoDepthModel v hv R e r).HasGeometricallyConnectedFibres := by
  change GeometricallyConnected (VectorGroup.groupScheme (CommRingCat.of R) n).X.hom
  exact VectorGroup.geometricallyConnected _ _

/-- Transporting both generic identifications preserves the actual integral
transition extending the identity. -/
def vectorIsoDepthTransition {r s : ℝ} (h : r ≤ s) :
    (vectorIsoDepthModel v hv R e s).Hom (vectorIsoDepthModel v hv R e r) (𝟙 _) where
  hom := (integerDepthVectorTransition v hv R hvR n h).hom
  generic_comm := by
    have hc := (integerDepthVectorTransition v hv R hvR n h).generic_comm
    change _ ≫ ((integerDepthVector v hv R n r).genericIso.hom ≫ e.inv) =
      ((integerDepthVector v hv R n s).genericIso.hom ≫ e.inv) ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc, hc, Category.comp_id]

include hvR in
/-- Every compatible identity extension between the transported models has
the same actual special-fibre kernel properties. -/
theorem vectorIsoDepthModel_kernel_properties {r s : ℝ} (h : r ≤ s)
    (φ : (vectorIsoDepthModel v hv R e s).Hom (vectorIsoDepthModel v hv R e r) (𝟙 _)) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) := by
  have hφ := φ.hom_eq (vectorIsoDepthTransition v hv R hvR e h)
  change Smooth (kernel ((GroupScheme.baseChange (residueBaseMap R)).map φ.hom)).X.hom ∧
    ConnectedSpace (kernel ((GroupScheme.baseChange (residueBaseMap R)).map φ.hom)).X.left ∧
      IsUnipotent (kernel ((GroupScheme.baseChange (residueBaseMap R)).map φ.hom))
  rw [hφ]
  exact integerDepthVector_kernel_properties v hv R hvR n h
    (integerDepthVectorTransition v hv R hvR n h)

variable
  (c : ∀ X : Over (Spec (CommRingCat.of K)),
    (X ⟶ U.X) ≃* Multiplicative (Fin n → Γ(X.left, ⊤)))
  (hc : RelativeRoot.IsNaturalVectorCoordinates c)

/-- Natural coordinates on all scheme tests give an actual depth model,
using the actual isomorphism they induce. -/
def naturalVectorDepthModel (r : ℝ) : IntegralModel R K U :=
  vectorIsoDepthModel v hv R (RelativeRoot.vectorGroupIso c hc) r

/-- The generic point coordinates of the actual natural-coordinate
isomorphism are the original scheme-section coordinates. -/
theorem sectionCoordinates_vectorGroupIso (g : rationalPoints U) (j : Fin n) :
    (VectorGroup.sectionCoordinates (CommRingCat.of K) n
      (rationalPoints.map (RelativeRoot.vectorGroupIso c hc).hom g)).toAdd j =
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
          ((c (Over.mk (𝟙 _)) g).toAdd j) := by
  rw [VectorGroup.sectionCoordinates_apply,
    rationalPoints.map_apply, RelativeRoot.coordinates_comp_vectorGroupIso_hom]

include hvR in
/-- The natural-coordinate depth model has exactly the finite polynomial
coordinate valuation bounds in the original all-test coordinates. -/
theorem naturalVectorDepthModel_mem_integralPoints (r : ℝ) (g : rationalPoints U) :
    g ∈ (naturalVectorDepthModel v hv R c hc r).integralPoints ↔
      ∀ j, v ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
        ((c (Over.mk (𝟙 _)) g).toAdd j)) ≤ WithZero.exp (-⌈r⌉) := by
  rw [naturalVectorDepthModel, vectorIsoDepthModel_mem_integralPoints,
    integerDepthVector_mem_integralPoints v hv R hvR]
  exact forall_congr' fun j => by rw [sectionCoordinates_vectorGroupIso]

end Langlands.GroupScheme.IntegralModel
