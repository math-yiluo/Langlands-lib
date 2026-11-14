import Langlands.GroupScheme.Examples.SU3TraceZeroScheme
import Langlands.GroupScheme.IntegralModel.CoordinateDepthVector

/-! # Integral depth models for the actual quadratic trace-zero line -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.SU3Root

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  (eta : Parameters.traceZero (fieldInvolution k L)) (hEta : (eta : L) ≠ 0)

/-- Relative global sections of the rational test carry their canonical base-field algebra. -/
def traceZeroRationalSectionsEquiv :
    ((algΓ (CommRingCat.of k)).obj (Over.mk (𝟙 (Spec (CommRingCat.of k))))).unop ≃ₐ[k] k where
  __ := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  commutes' r := by
    change (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r) = r
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of k)).inv_hom_id r

/-- The actual rational tensor algebra contracts to the original extension field. -/
def traceZeroRationalTensorEquiv :
    ((algΓ (CommRingCat.of k)).obj (Over.mk (𝟙 (Spec (CommRingCat.of k))))).unop ⊗[k] L ≃ₐ[k] L :=
  (Algebra.TensorProduct.congr (traceZeroRationalSectionsEquiv k) (AlgEquiv.refl : L ≃ₐ[k] L)).trans
    (Algebra.TensorProduct.lid k L)

/-- The contraction intertwines the actual tensor and field conjugations. -/
theorem traceZeroRationalTensorEquiv_bar
    (x : ((algΓ (CommRingCat.of k)).obj (Over.mk (𝟙 (Spec (CommRingCat.of k))))).unop ⊗[k] L) :
    traceZeroRationalTensorEquiv k L ((tensorInvolution k L _).bar x) =
      (fieldInvolution k L).bar (traceZeroRationalTensorEquiv k L x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    change traceZeroRationalSectionsEquiv k r • conjugation k L x =
      conjugation k L (traceZeroRationalSectionsEquiv k r • x)
    exact (map_smul (conjugation k L) _ _).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The actual field trace-zero coordinate of a rational point, obtained by tensor contraction. -/
def traceZeroRationalParameter (g : rationalPoints (traceZeroGroupScheme k L eta hEta)) :
    Parameters.traceZero (fieldInvolution k L) :=
  ⟨traceZeroRationalTensorEquiv k L
    (traceZeroPointsEquiv k L eta hEta (Over.mk (𝟙 _)) g).toAdd.val, by
    change _ + (fieldInvolution k L).bar _ = 0
    rw [← traceZeroRationalTensorEquiv_bar, ← map_add,
      (traceZeroPointsEquiv k L eta hEta (Over.mk (𝟙 _)) g).toAdd.property, map_zero]⟩

/-- The contracted field coordinate is exactly the scalar coordinate times eta. -/
theorem traceZeroRationalParameter_eq_scalar
    (g : rationalPoints (traceZeroGroupScheme k L eta hEta)) :
    (traceZeroRationalParameter k L eta hEta g : L) =
      algebraMap k L ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
        ((traceZeroVectorCoordinates k L eta hEta (Over.mk (𝟙 _)) g).toAdd 0)) * eta := by
  let R := ((algΓ (CommRingCat.of k)).obj (Over.mk (𝟙 (Spec (CommRingCat.of k))))).unop
  let x := (traceZeroPointsEquiv k L eta hEta (Over.mk (𝟙 _)) g).toAdd
  have hx := congrArg Subtype.val ((tensorTraceZeroEquiv k L eta hEta R).apply_symm_apply x)
  change traceZeroRationalTensorEquiv k L x.val =
    algebraMap k L ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
      ((tensorTraceZeroEquiv k L eta hEta R).symm x)) * eta
  rw [← hx]
  change traceZeroRationalSectionsEquiv k _ • (eta : L) = _
  rw [Algebra.smul_def]
  rfl

variable (v : Valuation k (WithZero (Multiplicative ℤ)))
  (hH : HenselianLocalRing v.valuationSubring)

/-- The real shift is the finite additive value of the chosen nonzero trace-zero scalar. -/
def traceZeroOffset : ℝ :=
  (FieldTheory.henselianIntegerAddValuation v hH L eta).untop
    ((FieldTheory.henselianIntegerAddValuation v hH L).ne_top_iff.mpr hEta)

@[simp]
theorem coe_traceZeroOffset :
    (traceZeroOffset k L eta hEta v hH : WithTop ℝ) =
      FieldTheory.henselianIntegerAddValuation v hH L eta :=
  WithTop.coe_untop _ _

/-- The chosen normalized prolongations have the same value on every base-field scalar. -/
theorem traceZero_base_value (x : k) :
    FieldTheory.henselianIntegerAddValuation v hH L (algebraMap k L x) =
      FieldTheory.henselianIntegerAddValuation v hH k x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [FieldTheory.henselianIntegerAddValuation_base v hH L hx,
      ← FieldTheory.henselianIntegerAddValuation_base v hH k hx,
      Algebra.algebraMap_self_apply]

/-- The exact shifted scalar threshold is the actual extension-field valuation threshold. -/
theorem traceZero_scalar_value_bound (r : ℝ) (x : k) :
    (r : WithTop ℝ) ≤ FieldTheory.henselianIntegerAddValuation v hH L
        (algebraMap k L x * eta) ↔
      ((r - traceZeroOffset k L eta hEta v hH : ℝ) : WithTop ℝ) ≤
        FieldTheory.henselianIntegerAddValuation v hH k x := by
  rw [AddValuation.map_mul, traceZero_base_value k L v hH,
    ← coe_traceZeroOffset k L eta hEta v hH]
  by_cases hx : x = 0
  · simp [hx]
  · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp
      ((FieldTheory.henselianIntegerAddValuation v hH k).ne_top_iff.mpr hx)
    rw [← ha, ← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
    exact sub_le_iff_le_add.symm

variable (hv : Function.Surjective v)
  (R : ValuationSubring k) (hvR : v.valuationSubring = R)

/-- The polynomial integral line at depth r minus the actual value of eta,
retargeted to the represented trace-zero group. -/
def traceZeroDepthModel (r : ℝ) :
    IntegralModel R k (traceZeroGroupScheme k L eta hEta) :=
  IntegralModel.vectorIsoCoordinateDepthModel v hv R (traceZeroVectorIso k L eta hEta)
    (fun _ : Fin 1 => traceZeroOffset k L eta hEta v hH) r

theorem traceZeroDepthModel_isSmooth (r : ℝ) :
    (traceZeroDepthModel k L eta hEta v hH hv R r).IsSmooth :=
  IntegralModel.vectorIsoCoordinateDepthModel_isSmooth _ _ _ _ _ _

theorem traceZeroDepthModel_hasGeometricallyConnectedFibres (r : ℝ) :
    (traceZeroDepthModel k L eta hEta v hH hv R r).HasGeometricallyConnectedFibres :=
  IntegralModel.vectorIsoCoordinateDepthModel_hasGeometricallyConnectedFibres _ _ _ _ _ _

include hvR in
/-- Its actual integral-point image consists precisely of field trace-zero coordinates
whose prolonged additive value is at least the requested real depth. -/
theorem traceZeroDepthModel_mem_integralPoints (r : ℝ)
    (g : rationalPoints (traceZeroGroupScheme k L eta hEta)) :
    g ∈ (traceZeroDepthModel k L eta hEta v hH hv R r).integralPoints ↔
      (r : WithTop ℝ) ≤ FieldTheory.henselianIntegerAddValuation v hH L
        (traceZeroRationalParameter k L eta hEta g : L) := by
  rw [traceZeroDepthModel,
    IntegralModel.vectorIsoCoordinateDepthModel_mem_integralPoints_iff_value v hv R hvR
      (traceZeroVectorIso k L eta hEta) hH]
  simp only [Fin.forall_fin_one]
  rw [traceZeroVectorIso, IntegralModel.sectionCoordinates_vectorGroupIso,
    traceZeroRationalParameter_eq_scalar]
  exact (traceZero_scalar_value_bound k L eta hEta v hH r _).symm

/-- The actual integral diagonal transition extends the generic identity. -/
def traceZeroDepthTransition {r s : ℝ} (h : r ≤ s) :
    (traceZeroDepthModel k L eta hEta v hH hv R s).Hom
      (traceZeroDepthModel k L eta hEta v hH hv R r) (𝟙 _) :=
  IntegralModel.vectorIsoCoordinateDepthTransition v hv R hvR (traceZeroVectorIso k L eta hEta)
    (fun _ : Fin 1 => traceZeroOffset k L eta hEta v hH) h

include hvR in
/-- Every compatible identity extension between these actual trace-zero depth models
has smooth, connected and unipotent scheme-theoretic special-fibre kernel. -/
theorem traceZeroDepthModel_kernel_properties {r s : ℝ} (h : r ≤ s)
    (phi : (traceZeroDepthModel k L eta hEta v hH hv R s).Hom
      (traceZeroDepthModel k L eta hEta v hH hv R r) (𝟙 _)) :
    Smooth (kernel phi.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel phi.specialFibreMap).X.left ∧
        IsUnipotent (kernel phi.specialFibreMap) :=
  IntegralModel.vectorIsoCoordinateDepthModel_kernel_properties v hv R hvR
    (traceZeroVectorIso k L eta hEta)
    (fun _ : Fin 1 => traceZeroOffset k L eta hEta v hH) h phi

end Langlands.GroupScheme.SU3Root
