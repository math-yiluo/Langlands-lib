import Langlands.Theta.DualPair.Unitary.LeraySplitting
import Mathlib.GroupTheory.NoncommCoprod

/-!
# The Weil representation of the unitary dual pair `(U(ν, ν), U(Q))`

GKT §12.4.1 (Proposition 12.26 (3), p. 371: the member `H(V)` acts geometrically,
`ω(1_W, h) φ(x^* ⊗ v) = μ(h) φ(x^* ⊗ h⁻¹ v)`, here with `μ = 1`), Definition 12.20 (splittings of a
pair) and Definition 13.15 (`ω_{ψ,s} = ω_ψ ∘ s`), in Case `3₊` with `W` split.

The unitary group `U(Q) = UnitaryGroup.ofForm c Q` of the Hermitian space `V = (E^α, Q)` acts on
`𝕎 = M_{α×2ν}(E) = M_{α×ν}(E)²` by left multiplication, preserving the book's form
(`hermitianTracePairing_mul_mul`), and on the Schwartz–Bruhat functions on `𝕏^* = M_{α×ν}(E)` by
`geometricWeil c ν Q h φ = φ(h⁻¹ ·)`, which normalizes the book's Schrödinger model. The two actions
commute (`lerayWeil_comm_geometricWeil`: on the Siegel parabolic because left and right
multiplications commute and `h` preserves the form; at the Weyl element because `x ↦ h x` preserves
Haar measure, `|N det h| = 1`); so `(g, h) ↦ lerayWeil g ∘ geometricWeil h` is a representation
`pairWeil` of `U(ν, ν) × U(Q)`, the Weil representation of the splitting `pairSplitting` of the dual
pair in the metaplectic group of pairs of the book's Schrödinger model. Every other splitting of
`U(Q)` (the book's `μ(h) ≠ 1`) is a twist by a character (`MetaplecticGroup.Splitting.twist`,
`MetaplecticGroup.Splitting.exists_eq_twist`).
-/

noncomputable section

open MeasureTheory Matrix

namespace Langlands.Theta

open Langlands.UnitaryGroup Langlands.HarmonicAnalysis Langlands.HeisenbergGroup
open Langlands.LinearMap.BilinForm (isometryGroup)

section Action

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] {c : E →ₐ[F] E}
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν] {Q : Matrix α α E}

/-- The matrix of an element of `U(Q)`. -/
abbrev unitaryMat (h : ofForm c Q) : Matrix α α E := ((h : GL α E) : Matrix α α E)

omit [Fintype ν] [DecidableEq ν] in
theorem unitaryMat_inv_mul_cancel (h : ofForm c Q) (x : Matrix α ν E) :
    unitaryMat h⁻¹ * (unitaryMat h * x) = x := by
  rw [← Matrix.mul_assoc, unitaryMat, unitaryMat, Subgroup.coe_inv, Units.inv_mul, Matrix.one_mul]

omit [Fintype ν] [DecidableEq ν] in
theorem unitaryMat_mul_inv_cancel (h : ofForm c Q) (x : Matrix α ν E) :
    unitaryMat h * (unitaryMat h⁻¹ * x) = x := by
  rw [← Matrix.mul_assoc, unitaryMat, unitaryMat, Subgroup.coe_inv, Units.mul_inv, Matrix.one_mul]

omit [DecidableEq ν] in
/-- `U(Q)` preserves the pairing: `β(h x, h y) = β(x, y)`. -/
theorem hermitianPairing_mul_mul (h : ofForm c Q) (x y : Matrix α ν E) :
    hermitianPairing c Q (unitaryMat h * x) (unitaryMat h * y) = hermitianPairing c Q x y := by
  have hh : (unitaryMat h)ᵀ * Q * (unitaryMat h).map c = Q := h.2
  rw [hermitianPairing_apply, hermitianPairing_apply]
  congr 2
  have e1 : (unitaryMat h * y).map c = (unitaryMat h).map c * y.map c :=
    Matrix.map_mul (f := c.toRingHom)
  have e : ((unitaryMat h * y).map c)ᵀ = (y.map c)ᵀ * ((unitaryMat h).map c)ᵀ := by
    rw [e1]; exact transpose_mul _ _
  calc Matrix.trace (Qᵀ * (unitaryMat h * x * ((unitaryMat h * y).map c)ᵀ))
      = Matrix.trace ((Qᵀ * unitaryMat h * x * (y.map c)ᵀ) * ((unitaryMat h).map c)ᵀ) := by
        rw [e]; simp only [Matrix.mul_assoc]
    _ = Matrix.trace (((unitaryMat h).map c)ᵀ * (Qᵀ * unitaryMat h * x * (y.map c)ᵀ)) :=
        Matrix.trace_mul_comm _ _
    _ = Matrix.trace (((unitaryMat h)ᵀ * Q * (unitaryMat h).map c)ᵀ * x * (y.map c)ᵀ) := by
        simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
    _ = Matrix.trace (Qᵀ * (x * (y.map c)ᵀ)) := by rw [hh, Matrix.mul_assoc]

omit [DecidableEq ν] in
/-- `U(Q)` preserves the book's pairing. -/
theorem hermitianTracePairing_mul_mul (h : ofForm c Q) (x y : Matrix α ν E) :
    hermitianTracePairing c Q (unitaryMat h * x) (unitaryMat h * y) =
      hermitianTracePairing c Q x y := by
  rw [hermitianTracePairing_eq_mul, hermitianTracePairing_eq_mul, hermitianPairing_mul_mul]

variable (ν) in
/-- `h ∈ U(Q)` acting on `𝕎 = M_{α×ν}(E)²` by left multiplication. -/
def _root_.Langlands.UnitaryGroup.leftMulEquiv (h : ofForm c Q) :
    (Matrix α ν E × Matrix α ν E) ≃ₗ[F] (Matrix α ν E × Matrix α ν E) where
  toFun w := (unitaryMat h * w.1, unitaryMat h * w.2)
  invFun w := (unitaryMat h⁻¹ * w.1, unitaryMat h⁻¹ * w.2)
  map_add' w w' := by simp [Matrix.mul_add]
  map_smul' r w := by simp [Matrix.mul_smul]
  left_inv w := by simp only [unitaryMat_inv_mul_cancel]
  right_inv w := by simp only [unitaryMat_mul_inv_cancel]

variable (ν) in
/-- **`U(Q)` in the isometry group of the book's form** `⟪,⟫` on `𝕎`: `h` acts by left
multiplication (the action of `1_W ⊗ h` on `W ⊗ V`). -/
def _root_.Langlands.UnitaryGroup.toTraceIsometryOfForm :
    ofForm c Q →* isometryGroup (polarizedForm (hermitianTracePairing (ν := ν) c Q)) where
  toFun h := ⟨UnitaryGroup.leftMulEquiv ν h, fun w w' => by
    simp only [polarizedForm_apply]
    change hermitianTracePairing c Q (unitaryMat h * w.1) (unitaryMat h * w'.2) -
        hermitianTracePairing c Q (unitaryMat h * w'.1) (unitaryMat h * w.2) = _
    rw [hermitianTracePairing_mul_mul, hermitianTracePairing_mul_mul]⟩
  map_one' := Subtype.ext <| LinearEquiv.ext fun w => by
    change (unitaryMat (1 : ofForm c Q) * w.1, unitaryMat (1 : ofForm c Q) * w.2) = w
    simp [unitaryMat]
  map_mul' h h' := Subtype.ext <| LinearEquiv.ext fun w => by
    change (unitaryMat (h * h') * w.1, unitaryMat (h * h') * w.2) =
      (unitaryMat h * (unitaryMat h' * w.1), unitaryMat h * (unitaryMat h' * w.2))
    simp [unitaryMat, Matrix.mul_assoc]

omit [Fintype ν] [DecidableEq ν] in
theorem _root_.Langlands.UnitaryGroup.leftMulEquiv_apply (h : ofForm c Q)
    (w : Matrix α ν E × Matrix α ν E) :
    UnitaryGroup.leftMulEquiv ν h w = (unitaryMat h * w.1, unitaryMat h * w.2) := rfl

omit [DecidableEq ν] in
theorem _root_.Langlands.UnitaryGroup.toTraceIsometryOfForm_apply (h : ofForm c Q) :
    (UnitaryGroup.toTraceIsometryOfForm ν h : (Matrix α ν E × Matrix α ν E) ≃ₗ[F] _) =
      UnitaryGroup.leftMulEquiv ν h := rfl

omit [DecidableEq α] [Fintype ν] [DecidableEq ν] in
private theorem toCols₁_mul_left (A : Matrix α α E) (X : Matrix α (ν ⊕ ν) E) :
    (A * X).toCols₁ = A * X.toCols₁ := by
  conv_lhs => rw [← fromCols_toCols X, mul_fromCols, toCols₁_fromCols]

omit [DecidableEq α] [Fintype ν] [DecidableEq ν] in
private theorem toCols₂_mul_left (A : Matrix α α E) (X : Matrix α (ν ⊕ ν) E) :
    (A * X).toCols₂ = A * X.toCols₂ := by
  conv_lhs => rw [← fromCols_toCols X, mul_fromCols, toCols₂_fromCols]

/-- Right multiplication by `g⁻¹ ∈ U(ν, ν)` and left multiplication by `h ∈ U(Q)` commute on `𝕎`. -/
theorem _root_.Langlands.UnitaryGroup.rightMulInvEquiv_leftMulEquiv
    (g : ofForm c (hyperbolicForm ν E)) (h : ofForm c Q) (w : Matrix α ν E × Matrix α ν E) :
    UnitaryGroup.rightMulInvEquiv c g (UnitaryGroup.leftMulEquiv ν h w) =
      UnitaryGroup.leftMulEquiv ν h (UnitaryGroup.rightMulInvEquiv c g w) := by
  simp only [UnitaryGroup.rightMulInvEquiv_apply, UnitaryGroup.leftMulEquiv_apply,
    ← mul_fromCols, Matrix.mul_assoc, toCols₁_mul_left, toCols₂_mul_left]

/-- **The dual pair `(U(ν, ν), U(Q))` in the isometry group of `⟪,⟫`** (GKT §5.1, the map
`U(W) × U(V) → Sp(𝕎)` of the pair, `𝕎 = W ⊗ V`): `(g, h)` acts by `w ↦ h w g⁻¹`. -/
def _root_.Langlands.UnitaryGroup.pairToTraceIsometry (hc : Function.Involutive c)
    (hQ : Matrix.IsHermitianFor c Q) :
    ofForm c (hyperbolicForm ν E) × ofForm c Q →*
      isometryGroup (polarizedForm (hermitianTracePairing (ν := ν) c Q)) :=
  (UnitaryGroup.toTraceIsometry hc hQ).noncommCoprod (UnitaryGroup.toTraceIsometryOfForm ν)
    fun g h => Subtype.ext <| LinearEquiv.ext fun w =>
      UnitaryGroup.rightMulInvEquiv_leftMulEquiv g h w

theorem _root_.Langlands.UnitaryGroup.pairToTraceIsometry_apply (hc : Function.Involutive c)
    (hQ : Matrix.IsHermitianFor c Q) (g : ofForm c (hyperbolicForm ν E) × ofForm c Q) :
    UnitaryGroup.pairToTraceIsometry (ν := ν) hc hQ g =
      UnitaryGroup.toTraceIsometry hc hQ g.1 * UnitaryGroup.toTraceIsometryOfForm ν g.2 := rfl

end Action

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] {c : E →ₐ[F] E}
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν] {Q : Matrix α α E}

/-- Left multiplication by an `E`-matrix, as an `F`-linear map of `M_{α×ν}(E)`. -/
private def leftMulLinear (A : Matrix α α E) : Matrix α ν E →ₗ[F] Matrix α ν E where
  toFun x := A * x
  map_add' := Matrix.mul_add A
  map_smul' r x := Matrix.mul_smul A r x

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [DecidableEq α] [DecidableEq ν] in
private theorem continuous_leftMul [IsTopologicalRing F] (A : Matrix α α E) :
    Continuous fun x : Matrix α ν E => A * x := by
  have := isModuleTopology_matrix F (E := E) α ν
  have := IsModuleTopology.toContinuousAdd F (Matrix α ν E)
  exact IsModuleTopology.continuous_of_linearMap (leftMulLinear (F := F) (ν := ν) A)

/-- `x ↦ h⁻¹ x` as a homeomorphism of `M_{α×ν}(E)`. -/
private def leftMulHomeomorph (h : ofForm c Q) : Matrix α ν E ≃ₜ Matrix α ν E where
  toFun x := unitaryMat h⁻¹ * x
  invFun x := unitaryMat h * x
  left_inv x := unitaryMat_mul_inv_cancel h x
  right_inv x := unitaryMat_inv_mul_cancel h x
  continuous_toFun := continuous_leftMul (F := F) _
  continuous_invFun := continuous_leftMul (F := F) _

variable (c ν Q) in
/-- **The geometric action of `U(Q)`** on the Schrödinger model (GKT Proposition 12.26 (3) with
`μ = 1`): `h · φ = φ(h⁻¹ ·)`. -/
def geometricWeil : Representation ℂ (ofForm c Q) (SchwartzBruhat (Matrix α ν E)) where
  toFun h :=
    { toFun := fun φ => ⟨fun x => (φ : Matrix α ν E → ℂ) (unitaryMat h⁻¹ * x),
        φ.2.1.comp_continuous (leftMulHomeomorph h).continuous,
        φ.2.2.comp_homeomorph (leftMulHomeomorph h)⟩
      map_add' := fun φ φ' => rfl
      map_smul' := fun a φ => rfl }
  map_one' := by
    ext φ x
    simp [unitaryMat]
  map_mul' h h' := by
    ext φ x
    change (φ : Matrix α ν E → ℂ) (unitaryMat (h * h')⁻¹ * x) =
      (φ : Matrix α ν E → ℂ) (unitaryMat h'⁻¹ * (unitaryMat h⁻¹ * x))
    simp [unitaryMat, Matrix.mul_assoc]

omit [DecidableEq ν] in
theorem geometricWeil_apply (h : ofForm c Q) (φ : SchwartzBruhat (Matrix α ν E))
    (x : Matrix α ν E) :
    (geometricWeil c ν Q h φ : Matrix α ν E → ℂ) x = (φ : Matrix α ν E → ℂ) (unitaryMat h⁻¹ * x) :=
  rfl

/-- The geometric action normalizes the book's Schrödinger model along the isometries of `U(Q)`:
the operator of `h` carries `ρ(w, t)` to `ρ(h w, t)` (relation (2.2) of GKT p. 47). -/
theorem geometricWeil_normalizes [Invertible (2 : F)] (ψ : UnitaryAdditiveCharacter F) :
    Normalizes (hermitianTraceSchrodinger c ν Q ψ)
      ((isometryAction _).comp (UnitaryGroup.toTraceIsometryOfForm ν)) (geometricWeil c ν Q) := by
  intro h k
  refine LinearMap.ext fun φ => Subtype.ext (funext fun x => ?_)
  change ψ.complex k.cen * (ψ.complex (hermitianTracePairing c Q (unitaryMat h⁻¹ * x) k.vec.2 +
      ⅟2 * hermitianTracePairing c Q k.vec.1 k.vec.2) *
        (φ : Matrix α ν E → ℂ) (unitaryMat h⁻¹ * x + k.vec.1)) =
    ψ.complex k.cen * (ψ.complex (hermitianTracePairing c Q x (unitaryMat h * k.vec.2) +
      ⅟2 * hermitianTracePairing c Q (unitaryMat h * k.vec.1) (unitaryMat h * k.vec.2)) *
        (φ : Matrix α ν E → ℂ) (unitaryMat h⁻¹ * (x + unitaryMat h * k.vec.1)))
  conv_rhs => rw [← unitaryMat_mul_inv_cancel h x]
  rw [hermitianTracePairing_mul_mul, hermitianTracePairing_mul_mul, Matrix.mul_add,
    unitaryMat_inv_mul_cancel, unitaryMat_inv_mul_cancel]

variable (ν) in
/-- **The splitting of `U(Q)`** (GKT Proposition 12.26 (3) with `μ = 1`):
`h ↦ (w ↦ h w, geometricWeil h)` in the metaplectic group of pairs of the book's Schrödinger model.
-/
def geometricSplitting [Invertible (2 : F)] (ψ : UnitaryAdditiveCharacter F) :
    MetaplecticGroup.Splitting (hermitianTraceSchrodinger c ν Q ψ)
      (UnitaryGroup.toTraceIsometryOfForm (c := c) (Q := Q) ν) :=
  MetaplecticGroup.Splitting.ofNormalizes _ (geometricWeil_normalizes ψ)

@[simp] theorem weil_geometricSplitting [Invertible (2 : F)] (ψ : UnitaryAdditiveCharacter F) :
    (geometricSplitting ν (c := c) (Q := Q) ψ).weil = geometricWeil c ν Q :=
  MetaplecticGroup.Splitting.weil_ofNormalizes _ _

end Local

section Measure

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] {c : E →ₐ[F] E}
  {δ : E} {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν] {Q : Matrix α α E}
  [Invertible (2 : F)] [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [TopologicalSpace E]
  [IsModuleTopology F E] [Fintype ν] [DecidableEq ν] [MeasurableSpace (Matrix α ν E)]
  [BorelSpace (Matrix α ν E)] in
/-- `|N_{E/F} det h| = 1` for `h ∈ U(Q)`: the norm of `det h` is `1`. -/
theorem _root_.Langlands.UnitaryGroup.norm_det_eq_one (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (h : ofForm c Q) :
    Units.map (Algebra.norm F : E →* F) (Matrix.GeneralLinearGroup.det (h : GL α E)) = 1 := by
  have hd := mem_normOneSubgroup.mp (det_mem_normOneSubgroup hQ hQu h)
  refine Units.ext ((algebraMap F E).injective ?_)
  rw [Units.coe_map, hE.algebraMap_norm, hd, Units.val_one, map_one]

/-- **`x ↦ h x` preserves every Haar measure** of `M_{α×ν}(E)`, `h ∈ U(Q)`
(`map_mul_mul_addHaar`, `|N det h| = 1`). -/
theorem measurePreserving_unitaryMat_mul (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (μ : Measure (Matrix α ν E))
    [μ.IsAddHaarMeasure] (h : ofForm c Q) :
    MeasurePreserving (fun x : Matrix α ν E => unitaryMat h * x) μ μ := by
  have : FiniteDimensional F E := hE.finite
  refine ⟨(continuous_leftMul (F := F) _).measurable, ?_⟩
  have hmap := map_mul_mul_addHaar (F := F) μ (h : GL α E) (1 : GL ν E)
  have e : (fun x : Matrix α ν E => unitaryMat h * x) =
      fun x => ((h : GL α E) : Matrix α α E) * x * ((1 : GL ν E) : Matrix ν ν E) := by
    funext x; rw [Units.val_one, Matrix.mul_one]
  rw [e, hmap, UnitaryGroup.norm_det_eq_one hE hQ hQu h, map_one, map_one, map_one, map_one,
    one_pow, one_pow, mul_one, inv_one, one_smul]

/-- `geometricWeil` preserves `∫ ‖φ‖²` for every Haar measure. -/
theorem geometricWeil_lintegral_enorm_sq (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (μ : Measure (Matrix α ν E))
    [μ.IsAddHaarMeasure] (h : ofForm c Q) (φ : SchwartzBruhat (Matrix α ν E)) :
    ∫⁻ x, ‖(geometricWeil c ν Q h φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ =
      ∫⁻ x, ‖(φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ :=
  (measurePreserving_unitaryMat_mul hE hQ hQu μ h⁻¹).lintegral_comp_emb
    (leftMulHomeomorph h).measurableEmbedding (fun y => ‖(φ : Matrix α ν E → ℂ) y‖ₑ ^ 2)

/-- **The splitting of `U(Q)` lands in `Mp(𝕎)^{ℂ¹}`** (GKT p. 49). -/
theorem geometricSplitting_mem_unitary (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (ψ : UnitaryAdditiveCharacter F)
    (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (h : ofForm c Q) :
    (geometricSplitting ν (c := c) (Q := Q) ψ).toMonoidHom h ∈
      MetaplecticGroup.unitary _ (schwartzBruhatInner μ) :=
  fun f f' => schwartzBruhatInner_map μ (geometricWeil c ν Q h)
    (fun φ => geometricWeil_lintegral_enorm_sq hE hQ hQu μ h φ) f f'

end Measure

section Pair

open Unitary.Internal

variable {F : Type} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Invertible (2 : F)] {E : Type} [Field E] [Algebra F E]
  [TopologicalSpace E] [IsModuleTopology F E] [Algebra.IsQuadraticExtension F E]
  {c : E →ₐ[F] E} {δ : E} {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]
  {Q : Matrix α α E} {χ : Eˣ →* Circle} {ψ : UnitaryAdditiveCharacter F}

/-- **The two members of the pair commute** (GKT Proposition 12.26): `ω(g)` and `h · ` commute for
`g ∈ U(ν, ν)`, `h ∈ U(Q)`; on the Siegel parabolic since `h` preserves `⟪,⟫` and left and right
multiplications commute, at the Weyl element since `x ↦ h x` preserves Haar measure; then `P` and
the Weyl element generate `U(ν, ν)`. -/
theorem lerayWeil_mul_geometricWeil (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    (g : ofForm c (hyperbolicForm ν E)) (h : ofForm c Q) :
    lerayWeil c ν ψ χ Q g * geometricWeil c ν Q h =
      geometricWeil c ν Q h * lerayWeil c ν ψ χ Q g := by
  let U : Subgroup (ofForm c (hyperbolicForm ν E)) :=
    { carrier := {g | lerayWeil c ν ψ χ Q g * geometricWeil c ν Q h =
        geometricWeil c ν Q h * lerayWeil c ν ψ χ Q g}
      mul_mem' := fun {a b} ha hb => by
        change lerayWeil c ν ψ χ Q (a * b) * geometricWeil c ν Q h =
          geometricWeil c ν Q h * lerayWeil c ν ψ χ Q (a * b)
        rw [map_mul, mul_assoc, hb.out, ← mul_assoc, ha.out, mul_assoc]
      one_mem' := by
        change lerayWeil c ν ψ χ Q 1 * geometricWeil c ν Q h =
          geometricWeil c ν Q h * lerayWeil c ν ψ χ Q 1
        rw [map_one, one_mul, mul_one]
      inv_mem' := fun {a} ha => by
        change lerayWeil c ν ψ χ Q a⁻¹ * geometricWeil c ν Q h =
          geometricWeil c ν Q h * lerayWeil c ν ψ χ Q a⁻¹
        have := ha.out
        calc lerayWeil c ν ψ χ Q a⁻¹ * geometricWeil c ν Q h
            = lerayWeil c ν ψ χ Q a⁻¹ * geometricWeil c ν Q h *
                (lerayWeil c ν ψ χ Q a * lerayWeil c ν ψ χ Q a⁻¹) := by
              rw [← map_mul, mul_inv_cancel, map_one, mul_one]
          _ = lerayWeil c ν ψ χ Q a⁻¹ * (geometricWeil c ν Q h * lerayWeil c ν ψ χ Q a) *
                lerayWeil c ν ψ χ Q a⁻¹ := by simp only [mul_assoc]
          _ = lerayWeil c ν ψ χ Q a⁻¹ * (lerayWeil c ν ψ χ Q a * geometricWeil c ν Q h) *
                lerayWeil c ν ψ χ Q a⁻¹ := by rw [this]
          _ = geometricWeil c ν Q h * lerayWeil c ν ψ χ Q a⁻¹ := by
              rw [← mul_assoc (lerayWeil c ν ψ χ Q a⁻¹), ← map_mul, inv_mul_cancel, map_one,
                one_mul] }
  suffices hU : U = ⊤ from (show g ∈ U from hU ▸ Subgroup.mem_top g)
  have : Infinite F := Infinite.of_injective _ Nat.cast_injective
  refine eq_top_of_siegelParabolic_le_of_weylElement_mem hE (fun p hp => ?_) ?_
  · refine LinearMap.ext fun φ => Subtype.ext (funext fun x => ?_)
    change (lerayWeil c ν ψ χ Q p (geometricWeil c ν Q h φ) : Matrix α ν E → ℂ) x =
      (geometricWeil c ν Q h (lerayWeil c ν ψ χ Q p φ) : Matrix α ν E → ℂ) x
    rw [lerayWeil_apply_of_mem_siegelParabolic hE hQ hQu hχ hres hp, geometricWeil_apply,
      geometricWeil_apply, lerayWeil_apply_of_mem_siegelParabolic hE hQ hQu hχ hres hp,
      Matrix.mul_assoc (unitaryMat h⁻¹) x, Matrix.mul_assoc (unitaryMat h⁻¹) x,
      hermitianTracePairing_mul_mul]
  · refine LinearMap.ext fun φ => Subtype.ext (funext fun x => ?_)
    let _ : MeasurableSpace (Matrix α ν E) := borel _
    have : BorelSpace (Matrix α ν E) := ⟨rfl⟩
    have : FiniteDimensional F E := hE.finite
    have : IsModuleTopology F (Matrix α ν E) := isModuleTopology_matrix F (E := E) α ν
    have := IsModuleTopology.isTopologicalAddGroup F (Matrix α ν E)
    have := locallyCompactSpace_of_finiteDimensional F (Matrix α ν E)
    have := t2Space_of_finiteDimensional F (Matrix α ν E)
    let μ : Measure (Matrix α ν E) := Measure.addHaar
    change (lerayWeil c ν ψ χ Q (weylElement c ν) (geometricWeil c ν Q h φ) :
        Matrix α ν E → ℂ) x =
      (geometricWeil c ν Q h (lerayWeil c ν ψ χ Q (weylElement c ν) φ) : Matrix α ν E → ℂ) x
    rw [lerayWeil_weylElement_apply hE hQ hQu hχ hres μ, geometricWeil_apply,
      lerayWeil_weylElement_apply hE hQ hQu hχ hres μ]
    congr 1
    have key := (measurePreserving_unitaryMat_mul hE hQ hQu μ h⁻¹).integral_comp
      (leftMulHomeomorph h).measurableEmbedding
      (fun y => (ψ (hermitianTracePairing c Q (unitaryMat h⁻¹ * x) y) : ℂ) *
        (φ : Matrix α ν E → ℂ) y)
    refine Eq.trans ?_ key
    congr 1
    funext y
    rw [geometricWeil_apply, hermitianTracePairing_mul_mul]

variable (c ν) in
/-- **The Weil representation of the dual pair `(U(ν, ν), U(Q))`** (GKT §12.4.1, Proposition 12.26,
Proposition 12.27 (1), with `μ = 1` on `U(Q)`): `(g, h) ↦ ω_{ψ,χ}(g) ∘ (h ·)` on the book's
Schrödinger model. -/
def pairWeil (ψ : UnitaryAdditiveCharacter F) (χ : Eˣ →* Circle) (Q : Matrix α α E)
    (hE : IsQuadraticInvolution c δ) (hQ : Matrix.IsHermitianFor c Q)
    (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α) :
    Representation ℂ (ofForm c (hyperbolicForm ν E) × ofForm c Q) (SchwartzBruhat (Matrix α ν E)) :=
  (lerayWeil c ν ψ χ Q).noncommCoprod (geometricWeil c ν Q)
    (lerayWeil_mul_geometricWeil hE hQ hQu hχ hres)

theorem pairWeil_apply (hE : IsQuadraticInvolution c δ) (hQ : Matrix.IsHermitianFor c Q)
    (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    (g : ofForm c (hyperbolicForm ν E) × ofForm c Q) :
    pairWeil c ν ψ χ Q hE hQ hQu hχ hres g = lerayWeil c ν ψ χ Q g.1 * geometricWeil c ν Q g.2 :=
  rfl

/-- The Weil representation of the pair restricts to `ω_{ψ,χ}` on `U(ν, ν)`. -/
@[simp] theorem pairWeil_comp_inl (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α) :
    (pairWeil c ν ψ χ Q hE hQ hQu hχ hres).comp (MonoidHom.inl _ _) = lerayWeil c ν ψ χ Q :=
  MonoidHom.noncommCoprod_comp_inl _ _ _

/-- The Weil representation of the pair restricts to the geometric action on `U(Q)`. -/
@[simp] theorem pairWeil_comp_inr (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α) :
    (pairWeil c ν ψ χ Q hE hQ hQu hχ hres).comp (MonoidHom.inr _ _) = geometricWeil c ν Q :=
  MonoidHom.noncommCoprod_comp_inr _ _ _

/-- The Weil representation of the pair normalizes the book's Schrödinger model along
`(g, h) ↦ (w ↦ h w g⁻¹)`. -/
theorem pairWeil_normalizes (hE : IsQuadraticInvolution c δ) (hQ : Matrix.IsHermitianFor c Q)
    (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α) :
    Normalizes (hermitianTraceSchrodinger c ν Q ψ)
      ((isometryAction _).comp (UnitaryGroup.pairToTraceIsometry hE.involutive hQ))
      (pairWeil c ν ψ χ Q hE hQ hQu hχ hres) := by
  rintro ⟨g, h⟩ k
  have h1 : ∀ g k, lerayWeil c ν ψ χ Q g ∘ₗ hermitianTraceSchrodinger c ν Q ψ k =
      hermitianTraceSchrodinger c ν Q ψ
        (isometryAction _ (UnitaryGroup.toTraceIsometry hE.involutive hQ g) k) ∘ₗ
        lerayWeil c ν ψ χ Q g :=
    lerayWeil_normalizes hE hQ hQu hχ hres
  have h2 : ∀ h k, geometricWeil c ν Q h ∘ₗ hermitianTraceSchrodinger c ν Q ψ k =
      hermitianTraceSchrodinger c ν Q ψ
        (isometryAction _ (UnitaryGroup.toTraceIsometryOfForm ν h) k) ∘ₗ geometricWeil c ν Q h :=
    geometricWeil_normalizes ψ
  change (lerayWeil c ν ψ χ Q g * geometricWeil c ν Q h) ∘ₗ hermitianTraceSchrodinger c ν Q ψ k =
    hermitianTraceSchrodinger c ν Q ψ (isometryAction _
      (UnitaryGroup.toTraceIsometry hE.involutive hQ g * UnitaryGroup.toTraceIsometryOfForm ν h)
        k) ∘ₗ (lerayWeil c ν ψ χ Q g * geometricWeil c ν Q h)
  rw [map_mul, MulAut.mul_apply, Module.End.mul_eq_comp,
    LinearMap.comp_assoc, h2, ← LinearMap.comp_assoc, h1, LinearMap.comp_assoc]

/-- **The splitting of the dual pair** `U(ν, ν) × U(Q) → Mp(𝕎)` (GKT Definition 12.20, §12.4.1,
Case `3₊` with `W` split): `(g, h) ↦ (w ↦ h w g⁻¹, ω_{ψ,χ}(g) ∘ (h ·))` in the metaplectic group
of pairs of the book's Schrödinger model. -/
def pairSplitting (hE : IsQuadraticInvolution c δ) (hQ : Matrix.IsHermitianFor c Q)
    (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α) :
    MetaplecticGroup.Splitting (hermitianTraceSchrodinger c ν Q ψ)
      (UnitaryGroup.pairToTraceIsometry hE.involutive hQ) :=
  MetaplecticGroup.Splitting.ofNormalizes _ (pairWeil_normalizes hE hQ hQu hχ hres)

/-- **`ω_{ψ,s} = ω_ψ ∘ s` for the pair** (GKT Definition 13.15). -/
@[simp] theorem weil_pairSplitting (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α) :
    (pairSplitting (ψ := ψ) hE hQ hQu hχ hres).weil = pairWeil c ν ψ χ Q hE hQ hQu hχ hres :=
  MetaplecticGroup.Splitting.weil_ofNormalizes _ _

/-- The splitting of the pair restricts to the Leray splitting on `U(ν, ν)`. -/
theorem pairSplitting_comp_inl (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α) :
    (pairSplitting (ν := ν) (ψ := ψ) hE hQ hQu hχ hres).toMonoidHom.comp (MonoidHom.inl _ _) =
      (leraySplitting hE hQ hQu hχ hres).toMonoidHom := by
  refine MonoidHom.ext fun g => MetaplecticGroup.ext _ ?_ (LinearEquiv.ext fun v => ?_)
  · change MetaplecticGroup.proj _
        ((pairSplitting (ν := ν) (ψ := ψ) hE hQ hQu hχ hres).toMonoidHom (g, 1)) =
      MetaplecticGroup.proj _ ((leraySplitting (ψ := ψ) hE hQ hQu hχ hres).toMonoidHom g)
    rw [MetaplecticGroup.Splitting.proj_apply, MetaplecticGroup.Splitting.proj_apply,
      UnitaryGroup.pairToTraceIsometry_apply, map_one, mul_one]
  · change (pairSplitting (ν := ν) (ψ := ψ) hE hQ hQu hχ hres).weil (g, 1) v =
      (leraySplitting (ψ := ψ) hE hQ hQu hχ hres).weil g v
    rw [weil_pairSplitting, weil_leraySplitting, pairWeil_apply, map_one, mul_one]

/-- The splitting of the pair restricts to `geometricSplitting` on `U(Q)`. -/
theorem pairSplitting_comp_inr (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α) :
    (pairSplitting (ν := ν) (ψ := ψ) hE hQ hQu hχ hres).toMonoidHom.comp (MonoidHom.inr _ _) =
      (geometricSplitting ν (c := c) (Q := Q) ψ).toMonoidHom := by
  refine MonoidHom.ext fun h => MetaplecticGroup.ext _ ?_ (LinearEquiv.ext fun v => ?_)
  · change MetaplecticGroup.proj _
        ((pairSplitting (ν := ν) (ψ := ψ) hE hQ hQu hχ hres).toMonoidHom (1, h)) =
      MetaplecticGroup.proj _ ((geometricSplitting ν (c := c) (Q := Q) ψ).toMonoidHom h)
    rw [MetaplecticGroup.Splitting.proj_apply, MetaplecticGroup.Splitting.proj_apply,
      UnitaryGroup.pairToTraceIsometry_apply, map_one, one_mul]
  · change (pairSplitting (ν := ν) (ψ := ψ) hE hQ hQu hχ hres).weil (1, h) v =
      (geometricSplitting ν (c := c) (Q := Q) ψ).weil h v
    rw [weil_pairSplitting, weil_geometricSplitting, pairWeil_apply, map_one, one_mul]

/-- **The splitting of the pair lands in `Mp(𝕎)^{ℂ¹}`** (GKT p. 49). -/
theorem pairSplitting_mem_unitary (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E))
    [μ.IsAddHaarMeasure] (g : ofForm c (hyperbolicForm ν E) × ofForm c Q) :
    (pairSplitting (ν := ν) (ψ := ψ) hE hQ hQu hχ hres).toMonoidHom g ∈
      MetaplecticGroup.unitary _ (schwartzBruhatInner μ) :=
  fun f f' => schwartzBruhatInner_map μ (pairWeil c ν ψ χ Q hE hQ hQu hχ hres g)
    (fun φ => by
      rw [pairWeil_apply, Module.End.mul_apply, lerayWeil_lintegral_enorm_sq hE hQ hQu hχ hres μ,
        geometricWeil_lintegral_enorm_sq hE hQ hQu μ])
    f f'

end Pair

end Langlands.Theta
