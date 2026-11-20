import Langlands.Geometry.FormalGroup.FormalCoordinateInverse

/-! # Formal coordinates for an idempotent with a presented tangent image -/

noncomputable section

universe u

namespace Langlands.FormalGroup.CoordinateMap

open MvPowerSeries
open scoped Classical

variable {R : Type u} [CommRing R] {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]

/-- The pointed coordinate map of a linear map of coordinate vectors. -/
def ofLinearMap (f : (σ → R) →ₗ[R] (τ → R)) : CoordinateMap R σ τ := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  exact {
    series i := ∑ j, C (f (Pi.single j 1) i) * X j
    constantCoeff_eq_zero i := by simp }

omit [Finite τ] in
theorem ofLinearMap_series [Fintype σ] (f : (σ → R) →ₗ[R] (τ → R)) (i : τ) :
    (ofLinearMap f).series i = ∑ j, C (f (Pi.single j 1) i) * X j := by
  classical
  unfold ofLinearMap
  exact Finset.sum_congr (by ext; simp) (fun _ _ => rfl)

omit [Finite σ] [Finite τ] in
private theorem linearMap_apply_eq_sum [Fintype σ] (f : (σ → R) →ₗ[R] (τ → R))
    (x : σ → R) (i : τ) :
    f x i = ∑ j, f (Pi.single j 1) i * x j := by
  classical
  have h := congrArg (fun z => f z i) (LinearMap.sum_single_apply (fun _ : σ => R) x)
  rw [map_sum, Finset.sum_apply] at h
  refine h.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
  have hx : (Pi.single j (x j) : σ → R) = x j • Pi.single j 1 := by
    rw [← Pi.single_smul]
    simp
  rw [hx, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

omit [Finite τ] in
@[simp]
theorem linearPart_ofLinearMap (f : (σ → R) →ₗ[R] (τ → R)) :
    (ofLinearMap f).linearPart = f := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  apply LinearMap.ext
  intro x
  funext i
  rw [linearPart_apply, linearMap_apply_eq_sum f]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold linearCoeff
  rw [ofLinearMap_series]
  simp [map_sum, coeff_C_mul, coeff_index_single_X]

@[simp]
theorem ofLinearMap_id : ofLinearMap (LinearMap.id : (σ → R) →ₗ[R] (σ → R)) = id := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  apply CoordinateMap.ext
  funext i
  rw [ofLinearMap_series]
  simp [Pi.single_apply, apply_ite, ite_mul]

omit [Finite τ] in
@[simp]
theorem ofLinearMap_zero : ofLinearMap (0 : (σ → R) →ₗ[R] (τ → R)) = zero := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  apply CoordinateMap.ext
  funext i
  rw [ofLinearMap_series]
  simp

omit [Finite σ] [Finite υ] in
private theorem ofLinearMap_comp_series (g : (τ → R) →ₗ[R] (υ → R)) [Fintype τ]
    (f : CoordinateMap R σ τ) (i : υ) :
    ((ofLinearMap g).comp f).series i = ∑ j, C (g (Pi.single j 1) i) * f.series j := by
  rw [comp_series, ofLinearMap_series]
  simp only [← substAlgHom_apply f.hasSubst, map_sum, map_mul, substAlgHom_X]
  simp [substAlgHom_apply, subst_C]

omit [Finite υ] in
theorem ofLinearMap_comp (g : (τ → R) →ₗ[R] (υ → R)) (f : (σ → R) →ₗ[R] (τ → R)) :
    (ofLinearMap g).comp (ofLinearMap f) = ofLinearMap (g.comp f) := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  let : Fintype τ := Fintype.ofFinite τ
  apply CoordinateMap.ext
  funext i
  rw [ofLinearMap_comp_series, ofLinearMap_series]
  simp_rw [ofLinearMap_series, Finset.mul_sum, ← mul_assoc, ← map_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← map_sum, LinearMap.comp_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← linearMap_apply_eq_sum g]

private def seriesAdd (f g : CoordinateMap R σ τ) : CoordinateMap R σ τ where
  series i := f.series i + g.series i
  constantCoeff_eq_zero i := by rw [map_add, f.constantCoeff_eq_zero, g.constantCoeff_eq_zero, add_zero]

private def seriesSub (f g : CoordinateMap R σ τ) : CoordinateMap R σ τ where
  series i := f.series i - g.series i
  constantCoeff_eq_zero i := by rw [map_sub, f.constantCoeff_eq_zero, g.constantCoeff_eq_zero, sub_zero]

omit [Finite τ] in
private theorem linearPart_seriesAdd (f g : CoordinateMap R σ τ) :
    (f.seriesAdd g).linearPart = f.linearPart + g.linearPart := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  apply LinearMap.ext
  intro x
  funext i
  simp [linearPart_apply, linearCoeff, seriesAdd, add_mul, Finset.sum_add_distrib]

omit [Finite τ] in
private theorem linearPart_seriesSub (f g : CoordinateMap R σ τ) :
    (f.seriesSub g).linearPart = f.linearPart - g.linearPart := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  apply LinearMap.ext
  intro x
  funext i
  simp [linearPart_apply, linearCoeff, seriesSub, sub_mul, Finset.sum_sub_distrib]

omit [Finite σ] [Finite υ] in
private theorem seriesAdd_comp (f g : CoordinateMap R τ υ) (h : CoordinateMap R σ τ) :
    (f.seriesAdd g).comp h = (f.comp h).seriesAdd (g.comp h) := by
  apply CoordinateMap.ext
  funext i
  simp only [seriesAdd, comp_series, ← substAlgHom_apply h.hasSubst, map_add]

omit [Finite σ] [Finite υ] in
private theorem seriesSub_comp (f g : CoordinateMap R τ υ) (h : CoordinateMap R σ τ) :
    (f.seriesSub g).comp h = (f.comp h).seriesSub (g.comp h) := by
  apply CoordinateMap.ext
  funext i
  simp only [seriesSub, comp_series, ← substAlgHom_apply h.hasSubst, map_sub]

omit [Finite σ] [Finite υ] in
private theorem ofLinearMap_comp_seriesAdd (g : (τ → R) →ₗ[R] (υ → R))
    (f h : CoordinateMap R σ τ) :
    (ofLinearMap g).comp (f.seriesAdd h) =
      ((ofLinearMap g).comp f).seriesAdd ((ofLinearMap g).comp h) := by
  classical
  let : Fintype τ := Fintype.ofFinite τ
  apply CoordinateMap.ext
  funext i
  simp only [seriesAdd, ofLinearMap_comp_series, mul_add, Finset.sum_add_distrib]

omit [Finite σ] [Finite τ] in
private theorem seriesAdd_zero (f : CoordinateMap R σ τ) : f.seriesAdd zero = f := by
  apply CoordinateMap.ext
  funext i
  simp [seriesAdd]

omit [Finite σ] [Finite τ] in
private theorem seriesSub_self (f : CoordinateMap R σ τ) : f.seriesSub f = zero := by
  apply CoordinateMap.ext
  funext i
  simp [seriesSub]

private theorem linearPart_mul_self (e : CoordinateMap R σ σ) (he : e.comp e = e) :
    e.linearPart * e.linearPart = e.linearPart := by
  change e.linearPart.comp e.linearPart = _
  rw [← linearPart_comp, he]

private theorem linearPart_mul_complement (e : CoordinateMap R σ σ) (he : e.comp e = e) :
    e.linearPart * (1 - e.linearPart) = 0 := by
  rw [mul_sub, mul_one, linearPart_mul_self e he, sub_self]

/-- The pointed change of coordinates that sends an idempotent to its linear part. -/
def linearizingMap (e : CoordinateMap R σ σ) : CoordinateMap R σ σ :=
  ((ofLinearMap e.linearPart).comp e).seriesAdd
    ((ofLinearMap (LinearMap.id - e.linearPart)).comp (id.seriesSub e))

theorem linearizingMap_linearPart (e : CoordinateMap R σ σ) (he : e.comp e = e) :
    e.linearizingMap.linearPart = LinearMap.id := by
  rw [linearizingMap, linearPart_seriesAdd, linearPart_comp, linearPart_comp,
    linearPart_ofLinearMap, linearPart_ofLinearMap, linearPart_seriesSub, linearPart_id]
  change e.linearPart * e.linearPart + (1 - e.linearPart) * (1 - e.linearPart) = 1
  rw [linearPart_mul_self e he, sub_mul, one_mul, linearPart_mul_complement e he, sub_zero]
  abel

/-- The change of coordinates intertwines the actual map and the linear projector. -/
theorem linearizingMap_comp (e : CoordinateMap R σ σ) (he : e.comp e = e) :
    e.linearizingMap.comp e = (ofLinearMap e.linearPart).comp e.linearizingMap := by
  have hzero : e.linearPart.comp (LinearMap.id - e.linearPart) = 0 :=
    linearPart_mul_complement e he
  have hproj : e.linearPart.comp e.linearPart = e.linearPart := linearPart_mul_self e he
  calc
    _ = (ofLinearMap e.linearPart).comp e := by
      simp only [linearizingMap, seriesAdd_comp, comp_assoc, seriesSub_comp, id_comp,
        he, seriesSub_self, comp_zero, seriesAdd_zero]
    _ = _ := by
      symm
      simp only [linearizingMap, ofLinearMap_comp_seriesAdd,
        ← comp_assoc (ofLinearMap e.linearPart), ofLinearMap_comp, hproj, hzero,
        ofLinearMap_zero, zero_comp, seriesAdd_zero]

/-- Inclusion and projection of a pointed idempotent in finite coordinates. -/
structure IdempotentCoordinates (e : CoordinateMap R σ σ) (τ : Type) [Finite τ] where
  inclusion : CoordinateMap R τ σ
  projection : CoordinateMap R σ τ
  projection_inclusion : projection.comp inclusion = CoordinateMap.id
  inclusion_projection : inclusion.comp projection = e

/-- A presentation of the tangent image gives a formal coordinate presentation. -/
def IdempotentCoordinates.ofTangentRetraction (e : CoordinateMap R σ σ) (he : e.comp e = e)
    (j : (τ → R) →ₗ[R] (σ → R)) (r : (σ → R) →ₗ[R] (τ → R))
    (hj : r.comp j = LinearMap.id) (hr : j.comp r = e.linearPart) :
    IdempotentCoordinates e τ := by
  let F := e.linearizingMap
  let hF := F.order_variable_sub_of_linearPart_id (e.linearizingMap_linearPart he)
  let G := F.inverseOfIdentityLinear hF
  have hc : F.comp e = (ofLinearMap e.linearPart).comp F := e.linearizingMap_comp he
  refine ⟨G.comp (ofLinearMap j), (ofLinearMap r).comp F, ?_, ?_⟩
  · rw [comp_assoc, ← comp_assoc F G, comp_inverseOfIdentityLinear, id_comp,
      ofLinearMap_comp, hj, ofLinearMap_id]
  · rw [comp_assoc G, ← comp_assoc (ofLinearMap j), ofLinearMap_comp, hr, ← hc,
      ← comp_assoc G F, inverseOfIdentityLinear_comp, id_comp]

end Langlands.FormalGroup.CoordinateMap
