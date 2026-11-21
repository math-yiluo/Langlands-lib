import Langlands.Geometry.FormalGroup.FormalIdempotentLaw
import Langlands.Geometry.FormalGroup.RationalHeightLinearization

/-! # Linearizing a finite-order formal action in character coordinates -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.CoordinateMap

open MvPowerSeries

variable {k : Type v} [Field k]
variable {σ τ : Type} [Finite σ] [Finite τ]

/-- The diagonal map with the specified tangent characters. -/
def diagonalLinear (c : τ → k) : (τ → k) →ₗ[k] (τ → k) where
  toFun x i := c i * x i
  map_add' x y := funext fun i => mul_add _ _ _
  map_smul' r x := funext fun i => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

omit [Finite σ] in
/-- On formal series, the diagonal map multiplies each output series by its weight. -/
theorem diagonal_comp_series (c : τ → k) (F : CoordinateMap k σ τ) (i : τ) :
    ((ofLinearMap (diagonalLinear c)).comp F).series i = c i • F.series i := by
  classical
  let : Fintype τ := Fintype.ofFinite τ
  have hseries : (ofLinearMap (diagonalLinear c)).series i = C (c i) * X i := by
    rw [ofLinearMap_series, Finset.sum_eq_single i]
    · simp [diagonalLinear]
    · intro j _ hji
      simp [diagonalLinear, Ne.symm hji]
    · simp
  rw [comp_series, hseries, ← substAlgHom_apply F.hasSubst, map_mul, substAlgHom_X,
    substAlgHom_apply, subst_C, MvPowerSeries.smul_eq_C_mul]

/-- A pointed coordinate map whose derivative is invertible determines an actual
formal retraction of the identity with that coordinate map as projection. -/
def identityCoordinatesOfTangentEquiv (F : CoordinateMap k σ τ)
    (a : (σ → k) ≃ₗ[k] (τ → k)) (hF : F.linearPart = a.toLinearMap) :
    IdempotentCoordinates (CoordinateMap.id : CoordinateMap k σ σ) τ := by
  let A := ofLinearMap a.toLinearMap
  let B := ofLinearMap a.symm.toLinearMap
  have hAB : A.comp B = CoordinateMap.id := by
    dsimp only [A, B]
    rw [ofLinearMap_comp, LinearEquiv.comp_symm, ofLinearMap_id]
  have hBA : B.comp A = CoordinateMap.id := by
    dsimp only [A, B]
    rw [ofLinearMap_comp, LinearEquiv.symm_comp, ofLinearMap_id]
  let G := B.comp F
  have hG : G.linearPart = LinearMap.id := by
    dsimp only [G, B]
    rw [linearPart_comp, linearPart_ofLinearMap, hF, LinearEquiv.symm_comp]
  let H := G.inverseOfIdentityLinear (G.order_variable_sub_of_linearPart_id hG)
  have hH : G.comp H = CoordinateMap.id := G.comp_inverseOfIdentityLinear _
  have hH' : H.comp G = CoordinateMap.id := G.inverseOfIdentityLinear_comp _
  have hA : F = A.comp G := by
    change F = A.comp (B.comp F)
    rw [← comp_assoc, hAB, id_comp]
  refine ⟨H.comp B, F, ?_, ?_⟩
  · calc
      F.comp (H.comp B) = (A.comp G).comp (H.comp B) := congrArg (·.comp (H.comp B)) hA
      _ = A.comp ((G.comp H).comp B) := by rw [comp_assoc, ← comp_assoc G H B]
      _ = CoordinateMap.id := by rw [hH, id_comp, hAB]
  · rw [comp_assoc, hH']

end Langlands.FormalGroup.CoordinateMap

namespace Langlands.FormalGroup.ModuleLaw

open CoordinateMap MvPowerSeries RationalHeightLinearization

variable {k : Type v} [Field k]
variable {O : Type u} [CommRing O] [Algebra O k]
variable {σ τ : Type} [Finite σ] [Finite τ] {M : ModuleLaw O k σ}
variable (γ : Hom M M) (a : (σ → k) ≃ₗ[k] (τ → k)) (c : τ → k) (m : ℕ)

private abbrev originalCoordinate (j : ℕ) : CoordinateMap k σ τ :=
  (ofLinearMap a.toLinearMap).comp (γ ^ j).toHom.toCoordinateMap

/-- Each coordinate is the finite average projecting its original coordinate
series to the corresponding character. -/
def cyclicProjection : CoordinateMap k σ τ where
  series i := weightedAverage m (c i) (fun j => (originalCoordinate γ a j).series i)
  constantCoeff_eq_zero i := by
    rw [← coeff_zero_eq_constantCoeff_apply, map_weightedAverage]
    have he : (coeff 0 : MvPowerSeries σ k →ₗ[k] k) ∘
        (fun j => (originalCoordinate γ a j).series i) = fun _ => 0 := by
      funext j
      exact (coeff_zero_eq_constantCoeff_apply _).trans ((originalCoordinate γ a j).constantCoeff_eq_zero i)
    rw [he]
    simp [weightedAverage]

omit [Finite τ] in
private theorem originalCoordinate_pow_linearPart
    (hdiag : ∀ (x : σ → k) (i : τ), a (γ.toHom.toCoordinateMap.linearPart x) i = c i * a x i)
    (j : ℕ) (x : σ → k) (i : τ) :
    (originalCoordinate γ a j).linearPart x i = c i ^ j * a x i := by
  simp only [originalCoordinate, linearPart_comp, linearPart_ofLinearMap, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  induction j generalizing x with
  | zero => simp [show (1 : Hom M M) = Hom.id M from rfl, Hom.id]
  | succ j ih =>
    have he : (γ ^ (j + 1)).toHom.toCoordinateMap =
        (γ ^ j).toHom.toCoordinateMap.comp γ.toHom.toCoordinateMap := by
      rw [pow_succ]
      rfl
    rw [he, linearPart_comp, LinearMap.comp_apply, ih, hdiag, pow_succ, mul_assoc]

omit [Finite τ] in
/-- Averaging the formal series retains exactly the given tangent eigenbasis. -/
theorem cyclicProjection_linearPart
    (hm : (m : k) ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hdiag : ∀ (x : σ → k) (i : τ), a (γ.toHom.toCoordinateMap.linearPart x) i = c i * a x i) :
    (cyclicProjection γ a c m).linearPart = a.toLinearMap := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  have hcoeff (F : CoordinateMap k σ τ) (i : τ) (j : σ) :
      F.linearCoeff i j = F.linearPart (Pi.single j 1) i := by
    simp [linearPart_apply, Pi.single_apply, mul_ite]
  have hp (i : τ) (j : σ) : (cyclicProjection γ a c m).linearCoeff i j = a (Pi.single j 1) i := by
    change (coeff (Finsupp.single j 1))
      (weightedAverage m (c i) (fun r => (originalCoordinate γ a r).series i)) = _
    rw [map_weightedAverage]
    have he : (coeff (Finsupp.single j 1) : MvPowerSeries σ k →ₗ[k] k) ∘
        (fun r => (originalCoordinate γ a r).series i) =
        (fun r => c i ^ r • a (Pi.single j 1) i) := by
      funext r
      change (originalCoordinate γ a r).linearCoeff i j = _
      rw [hcoeff, originalCoordinate_pow_linearPart γ a c hdiag]
      rfl
    rw [he]
    exact weightedAverage_smul_pows hm (hc i) _
  apply LinearMap.ext
  intro x
  funext i
  have h := (hp i)
  rw [linearPart_apply]
  change ∑ j, (cyclicProjection γ a c m).linearCoeff i j * x j = a x i
  have he := congrArg (fun z => a z i) (LinearMap.sum_single_apply (fun _ : σ => k) x)
  rw [map_sum, Finset.sum_apply] at he
  rw [← he]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h j, show (Pi.single j (x j) : σ → k) = x j • Pi.single j 1 by rw [← Pi.single_smul]; simp,
    map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- The average of the coordinate series satisfies the exact formal eigenvalue identity. -/
theorem cyclicProjection_comp
    (hm : m ≠ 0) (hc : ∀ i, c i ^ m = 1) (hγ : γ ^ m = 1) :
    (cyclicProjection γ a c m).comp γ.toHom.toCoordinateMap =
      (ofLinearMap (diagonalLinear c)).comp (cyclicProjection γ a c m) := by
  apply CoordinateMap.ext
  funext i
  rw [comp_series, diagonal_comp_series, ← substAlgHom_apply γ.toHom.toCoordinateMap.hasSubst]
  change (substAlgHom γ.toHom.toCoordinateMap.hasSubst).toLinearMap
    (weightedAverage m (c i) (fun j => (originalCoordinate γ a j).series i)) = _
  rw [map_weightedAverage]
  have he : (substAlgHom γ.toHom.toCoordinateMap.hasSubst).toLinearMap ∘
      (fun j => (originalCoordinate γ a j).series i) =
      (fun j => (originalCoordinate γ a (j + 1)).series i) := by
    funext j
    simp only [Function.comp_apply, AlgHom.toLinearMap_apply, substAlgHom_apply, ← comp_series]
    change (((ofLinearMap a.toLinearMap).comp (γ ^ j).toHom.toCoordinateMap).comp
      γ.toHom.toCoordinateMap).series i =
        ((ofLinearMap a.toLinearMap).comp (γ ^ (j + 1)).toHom.toCoordinateMap).series i
    rw [comp_assoc, pow_succ]
    rfl
  rw [he]
  exact weightedAverage_shift hm (hc i) (fun j => (originalCoordinate γ a j).series i) (by
    change ((ofLinearMap a.toLinearMap).comp (γ ^ m).toHom.toCoordinateMap).series i =
      ((ofLinearMap a.toLinearMap).comp (γ ^ 0).toHom.toCoordinateMap).series i
    rw [hγ, pow_zero])


variable (hm : (m : k) ≠ 0) (hc : ∀ i, c i ≠ 0)
variable (hdiag : ∀ (x : σ → k) (i : τ), a (γ.toHom.toCoordinateMap.linearPart x) i = c i * a x i)

/-- Keep the actual inverse formal coordinate maps for the averaged projection. -/
def cyclicCoordinates : IdempotentCoordinates (CoordinateMap.id : CoordinateMap k σ σ) τ :=
  identityCoordinatesOfTangentEquiv (cyclicProjection γ a c m) a
    (cyclicProjection_linearPart γ a c m hm hc hdiag)

/-- Transport the actual formal module to the averaged coordinates using the
identity idempotent image. -/
def cyclicCoordinateIso : Iso M
    ((cyclicCoordinates γ a c m hm hc hdiag).imageModuleLaw (b := Hom.id M)) := by
  let C := (cyclicCoordinates γ a c m hm hc hdiag).moduleImage (b := Hom.id M)
  exact ⟨C.projection, C.inclusion, C.inclusion_projection, C.projection_inclusion⟩

/-- In the transported module the actual cyclic endomorphism is the diagonal
linear coordinate map. -/
theorem cyclicCoordinateIso_conjugate
    (hm₀ : m ≠ 0) (hc₁ : ∀ i, c i ^ m = 1) (hγ : γ ^ m = 1) :
    let e := cyclicCoordinateIso γ a c m hm hc hdiag
    (e.hom.comp (γ.comp e.inv)).toHom.toCoordinateMap = ofLinearMap (diagonalLinear c) := by
  let C := cyclicCoordinates γ a c m hm hc hdiag
  have hex : C.projection.comp γ.toHom.toCoordinateMap =
      (ofLinearMap (diagonalLinear c)).comp C.projection :=
    cyclicProjection_comp γ a c m hm₀ hc₁ hγ
  change C.projection.comp (γ.toHom.toCoordinateMap.comp C.inclusion) = _
  rw [← CoordinateMap.comp_assoc, hex, CoordinateMap.comp_assoc, C.projection_inclusion,
    CoordinateMap.comp_id]

end Langlands.FormalGroup.ModuleLaw
