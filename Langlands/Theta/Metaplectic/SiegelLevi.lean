import Langlands.Theta.Metaplectic.Defs
import Langlands.Theta.Heisenberg.SchrodingerUnitary
import Langlands.HarmonicAnalysis.LinearHaarScaling

/-!
# The splitting of the Siegel Levi subgroup

GKT §2.3.2 (Lemma 2.16, p. 58): on the Siegel Levi subgroup `M(X)` of a polarization, the standard
Weil operator is `r(m(a)) φ(y) = |det a|^{1/2} φ(a^* y)`, and `m(a) ↦ (m(a), r(m(a)))` is a
splitting of `M(X)` in the metaplectic group of pairs of the Schrödinger model.

For a pairing `β : X →ₗ Y →ₗ R`, the Schrödinger model `HeisenbergGroup.schrodingerSB` lives on
functions on `X` (the book's `Y`, with the book's `X` the file's `Y`).

* `siegelLeviGroup β`: the pairs `(a, a')` of automorphisms of `X` and `Y` with
  `β (a x) (a' y) = β x y`, the Siegel Levi `M(Y)` of the polarization `X × Y` of
  `polarizedForm β`; `siegelLeviGroup.toIsometry β`, `(a, a') ↦ a × a'`, into the isometry group.
* `dualSiegelLevi R V : (V ≃ₗ[R] V) →* siegelLeviGroup (LinearMap.id)`, `a ↦ ((a⁻¹)^*, a)`, for the
  polarization `V^* × V` with the canonical pairing: the book's `a ↦ m(a)`, `a ∈ GL(V)`.
* `siegelLeviWeil β`: over a nonarchimedean local field, `(a, a')` acts on `S(X)` by
  `φ ↦ |det a|^{-1/2} φ(a⁻¹ ·)`; it normalizes the Schrödinger model
  (`siegelLeviWeil_normalizes`), preserves `∫ ‖φ‖²` for every Haar measure
  (`siegelLeviWeil_lintegral_enorm_sq`), and `siegelLeviSplitting` is the splitting.
* `siegelLeviWeil_dualSiegelLevi_apply`: on `m(a)` it is the book's
  `φ ↦ |det a|^{1/2} φ(a^* ·)`.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.Theta

open HeisenbergGroup HarmonicAnalysis
open Langlands.LinearMap.BilinForm (isometryGroup)

section Levi

variable {R : Type*} [CommRing R] {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y]
  [Module R Y]

variable (β : X →ₗ[R] Y →ₗ[R] R)

/-- **The Siegel Levi subgroup** of the polarization `X × Y` of `polarizedForm β` (GKT §2.3.2,
p. 57: `M(X) = {m(a)}`, here for the Lagrangian `0 × Y`): the pairs `(a, a')` of automorphisms of
`X` and `Y` with `β (a x) (a' y) = β x y`. -/
def siegelLeviGroup : Subgroup ((X ≃ₗ[R] X) × (Y ≃ₗ[R] Y)) where
  carrier := {p | ∀ x y, β (p.1 x) (p.2 y) = β x y}
  mul_mem' {p q} hp hq x y := by
    change β (p.1 (q.1 x)) (p.2 (q.2 y)) = β x y
    rw [hp, hq]
  one_mem' _ _ := rfl
  inv_mem' {p} hp x y := by
    change β (p.1.symm x) (p.2.symm y) = β x y
    rw [← hp, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem mem_siegelLeviGroup {p : (X ≃ₗ[R] X) × (Y ≃ₗ[R] Y)} :
    p ∈ siegelLeviGroup β ↔ ∀ x y, β (p.1 x) (p.2 y) = β x y :=
  Iff.rfl

/-- The Siegel Levi in the isometry group of `polarizedForm β`: `(a, a')` acts by `a × a'`. -/
def siegelLeviGroup.toIsometry : siegelLeviGroup β →* isometryGroup (polarizedForm β) where
  toFun p := ⟨LinearEquiv.prodCongr p.1.1 p.1.2, fun w w' => by
    simp only [polarizedForm_apply]
    change β (p.1.1 w.1) (p.1.2 w'.2) - β (p.1.1 w'.1) (p.1.2 w.2) = _
    rw [p.2, p.2]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem siegelLeviGroup.toIsometry_apply (p : siegelLeviGroup β) (w : X × Y) :
    (siegelLeviGroup.toIsometry β p : (X × Y) ≃ₗ[R] (X × Y)) w = (p.1.1 w.1, p.1.2 w.2) := rfl

variable (R) (V : Type*) [AddCommGroup V] [Module R V]

/-- **`a ↦ m(a)`** for the polarization `V^* × V` with the canonical pairing (GKT p. 57):
`a ∈ GL(V)` acts on `V` by `a` and on `V^*` by `(a⁻¹)^* : f ↦ f ∘ a⁻¹`. -/
def dualSiegelLevi :
    (V ≃ₗ[R] V) →* siegelLeviGroup (LinearMap.id : Module.Dual R V →ₗ[R] V →ₗ[R] R) where
  toFun a := ⟨(a.symm.dualMap, a), fun f v => by
    change f (a.symm (a v)) = f v
    rw [LinearEquiv.symm_apply_apply]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem dualSiegelLevi_apply (a : V ≃ₗ[R] V) :
    (dualSiegelLevi R V a : (Module.Dual R V ≃ₗ[R] Module.Dual R V) × (V ≃ₗ[R] V)) =
      (a.symm.dualMap, a) := rfl

end Levi

section Local

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {X Y : Type*} [AddCommGroup X] [Module F X] [FiniteDimensional F X] [TopologicalSpace X]
  [IsModuleTopology F X] [AddCommGroup Y] [Module F Y] {β : X →ₗ[F] Y →ₗ[F] F}

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [FiniteDimensional F X] in
private theorem continuous_linearEquiv (a : X ≃ₗ[F] X) : Continuous a := by
  have := IsModuleTopology.toContinuousAdd F X
  exact IsModuleTopology.continuous_of_linearMap a.toLinearMap

/-- A linear automorphism as a homeomorphism (the module topology). -/
private def toHomeomorph (a : X ≃ₗ[F] X) : X ≃ₜ X where
  toEquiv := a.toEquiv
  continuous_toFun := continuous_linearEquiv a
  continuous_invFun := continuous_linearEquiv a.symm

variable (F) in
/-- `|det a|^{-1/2}`, with `|·|` the modulus `distribHaarChar F`. -/
def siegelLeviScalar (a : X ≃ₗ[F] X) : ℝ≥0 :=
  distribHaarChar F (LinearEquiv.det a) ^ (-(1 : ℝ) / 2)

omit [FiniteDimensional F X] [TopologicalSpace X] [IsModuleTopology F X] in
theorem siegelLeviScalar_mul (a b : X ≃ₗ[F] X) :
    siegelLeviScalar F (a * b) = siegelLeviScalar F a * siegelLeviScalar F b := by
  simp only [siegelLeviScalar, map_mul, NNReal.mul_rpow]

omit [FiniteDimensional F X] [TopologicalSpace X] [IsModuleTopology F X] in
theorem siegelLeviScalar_one : siegelLeviScalar F (1 : X ≃ₗ[F] X) = 1 := by
  simp [siegelLeviScalar]

omit [FiniteDimensional F X] in
private theorem mem_schwartzBruhatSubmodule (a : X ≃ₗ[F] X) (φ : SchwartzBruhat X) :
    (fun x => (siegelLeviScalar F a : ℂ) * (φ : X → ℂ) (a.symm x)) ∈ schwartzBruhatSubmodule X :=
  ⟨(IsLocallyConstant.const _).mul (φ.locallyConstant.comp_continuous
      (continuous_linearEquiv a.symm)),
    (φ.hasCompactSupport.comp_homeomorph (toHomeomorph a.symm)).mul_left⟩

variable (β) in
/-- **The Weil representation of the Siegel Levi** (GKT Lemma 2.16 for `m(a)`): `(a, a')` acts on
the Schrödinger model by `φ ↦ |det a|^{-1/2} φ(a⁻¹ ·)`. -/
def siegelLeviWeil : Representation ℂ (siegelLeviGroup β) (SchwartzBruhat X) where
  toFun p :=
    { toFun := fun φ => ⟨_, mem_schwartzBruhatSubmodule p.1.1 φ⟩
      map_add' := fun φ ψ => by
        ext x
        simp only [Submodule.coe_add, Pi.add_apply, mul_add]
      map_smul' := fun c φ => by
        ext x
        simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  map_one' := by
    ext φ x
    change (siegelLeviScalar F (1 : X ≃ₗ[F] X) : ℂ) * (φ : X → ℂ) x = (φ : X → ℂ) x
    rw [siegelLeviScalar_one, NNReal.coe_one, Complex.ofReal_one, one_mul]
  map_mul' p q := by
    ext φ x
    change (siegelLeviScalar F (p.1.1 * q.1.1) : ℂ) * (φ : X → ℂ) ((p.1.1 * q.1.1).symm x) =
      (siegelLeviScalar F p.1.1 : ℂ) * ((siegelLeviScalar F q.1.1 : ℂ) *
        (φ : X → ℂ) (q.1.1.symm (p.1.1.symm x)))
    rw [siegelLeviScalar_mul, NNReal.coe_mul, Complex.ofReal_mul, mul_assoc]
    rfl

omit [FiniteDimensional F X] in
theorem siegelLeviWeil_apply (p : siegelLeviGroup β) (φ : SchwartzBruhat X) (x : X) :
    (siegelLeviWeil β p φ : X → ℂ) x =
      ((distribHaarChar F (LinearEquiv.det p.1.1) ^ (-(1 : ℝ) / 2) : ℝ≥0) : ℂ) *
        (φ : X → ℂ) (p.1.1.symm x) := rfl

omit [FiniteDimensional F X] in
/-- **The Siegel Levi normalizes the Schrödinger model**: `ω(m) ρ(w, t) = ρ(m w, t) ω(m)`
(relation (2.2) of GKT p. 47). -/
theorem siegelLeviWeil_normalizes [Invertible (2 : F)] [IsTopologicalAddGroup X] {ψ : AddChar F ℂ}
    (hψ : Continuous ψ) (hβ : ∀ y, Continuous fun x => β x y) :
    Normalizes (schrodingerSB hψ hβ) ((isometryAction _).comp (siegelLeviGroup.toIsometry β))
      (siegelLeviWeil β) := by
  intro p k
  refine LinearMap.ext fun φ => Subtype.ext (funext fun x => ?_)
  change (siegelLeviScalar F p.1.1 : ℂ) * (ψ k.cen * (ψ (β (p.1.1.symm x) k.vec.2 +
      ⅟2 * β k.vec.1 k.vec.2) * (φ : X → ℂ) (p.1.1.symm x + k.vec.1))) =
    ψ k.cen * (ψ (β x (p.1.2 k.vec.2) + ⅟2 * β (p.1.1 k.vec.1) (p.1.2 k.vec.2)) *
      ((siegelLeviScalar F p.1.1 : ℂ) * (φ : X → ℂ) (p.1.1.symm (x + p.1.1 k.vec.1))))
  have e : β x (p.1.2 k.vec.2) = β (p.1.1.symm x) k.vec.2 := by
    conv_lhs => rw [← LinearEquiv.apply_symm_apply p.1.1 x]
    exact p.2 _ _
  rw [e, p.2, LinearEquiv.map_add, LinearEquiv.symm_apply_apply]
  ring

/-- **The splitting of the Siegel Levi** (GKT §2.3.2, Lemma 2.16 for `m(a)`): `(a, a') ↦
(a × a', siegelLeviWeil (a, a'))` in the metaplectic group of pairs of the Schrödinger model. -/
def siegelLeviSplitting [Invertible (2 : F)] [IsTopologicalAddGroup X] {ψ : AddChar F ℂ}
    (hψ : Continuous ψ) (hβ : ∀ y, Continuous fun x => β x y) :
    MetaplecticGroup.Splitting (schrodingerSB hψ hβ) (siegelLeviGroup.toIsometry β) :=
  MetaplecticGroup.Splitting.ofNormalizes _ (siegelLeviWeil_normalizes hψ hβ)

omit [FiniteDimensional F X] in
@[simp] theorem weil_siegelLeviSplitting [Invertible (2 : F)] [IsTopologicalAddGroup X]
    {ψ : AddChar F ℂ} (hψ : Continuous ψ) (hβ : ∀ y, Continuous fun x => β x y) :
    (siegelLeviSplitting hψ hβ).weil = siegelLeviWeil β :=
  MetaplecticGroup.Splitting.weil_ofNormalizes _ _

/-- **The operators are unitary** for every Haar measure (this fixes the factor `|det a|^{-1/2}`,
GKT Lemma 2.16): `∫ ‖ω(m) φ‖² = ∫ ‖φ‖²`. -/
theorem siegelLeviWeil_lintegral_enorm_sq [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [μ.IsAddHaarMeasure] (p : siegelLeviGroup β) (φ : SchwartzBruhat X) :
    ∫⁻ x, ‖(siegelLeviWeil β p φ : X → ℂ) x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖(φ : X → ℂ) x‖ₑ ^ 2 ∂μ := by
  set a := p.1.1
  set d : ℝ≥0 := distribHaarChar F (LinearEquiv.det a) with hd_def
  have hd : d ≠ 0 := by
    have h1 : d * distribHaarChar F (LinearEquiv.det a)⁻¹ = 1 := by
      rw [hd_def, ← map_mul, mul_inv_cancel, map_one]
    exact left_ne_zero_of_mul_eq_one h1
  have hcont : Continuous fun x : X => (φ : X → ℂ) x := φ.continuous
  have hf : Measurable fun y : X => ‖(φ : X → ℂ) y‖ₑ ^ 2 := hcont.measurable.enorm.pow_const 2
  have hg : Measurable a.symm := (continuous_linearEquiv a.symm).measurable
  have hc : ∀ t : ℝ≥0, ‖((t : ℝ) : ℂ)‖ₑ = (t : ENNReal) := fun t => by
    rw [← ofReal_norm]; simp
  have hsq : (d ^ (-(1 : ℝ) / 2)) ^ 2 = d⁻¹ := by
    rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
    norm_num
    exact NNReal.rpow_neg_one d
  have e1 : ∀ x, ‖(siegelLeviWeil β p φ : X → ℂ) x‖ₑ ^ 2 =
      ((d⁻¹ : ℝ≥0) : ENNReal) * ‖(φ : X → ℂ) (a.symm x)‖ₑ ^ 2 := fun x => by
    rw [siegelLeviWeil_apply, enorm_mul, mul_pow, hc, ← ENNReal.coe_pow, ← hsq]
  have hm : ∫⁻ y, ‖(φ : X → ℂ) y‖ₑ ^ 2 ∂(μ.map a.symm) =
      ∫⁻ x, ‖(φ : X → ℂ) (a.symm x)‖ₑ ^ 2 ∂μ := lintegral_map hf hg
  simp only [e1]
  rw [lintegral_const_mul (f := fun x => ‖(φ : X → ℂ) (a.symm x)‖ₑ ^ 2) _
    ((hcont.comp (continuous_linearEquiv a.symm)).measurable.enorm.pow_const 2), ← hm,
    map_linearEquiv_addHaar μ a.symm, lintegral_smul_measure, LinearEquiv.det_symm, map_inv,
    map_inv, inv_inv, ← hd_def, ENNReal.smul_def, smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul,
    inv_mul_cancel₀ hd, ENNReal.coe_one, one_mul]

/-- **The splitting of the Siegel Levi lands in `Mp(W)^{ℂ¹}`** (GKT p. 49): its operators preserve
the `L²` inner product of every Haar measure. -/
theorem siegelLeviSplitting_mem_unitary [Invertible (2 : F)] [IsTopologicalAddGroup X]
    {ψ : AddChar F ℂ} (hψ : Continuous ψ) (hβ : ∀ y, Continuous fun x => β x y)
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]
    (p : siegelLeviGroup β) :
    (siegelLeviSplitting hψ hβ).toMonoidHom p ∈
      MetaplecticGroup.unitary _ (schwartzBruhatInner μ) :=
  fun f f' => schwartzBruhatInner_map μ (siegelLeviWeil β p)
    (fun φ => siegelLeviWeil_lintegral_enorm_sq μ p φ) f f'

/-- **GKT Lemma 2.16 for `m(a)`**, in the book's form: for the polarization `V^* × V` with the
canonical pairing (functions on `V^*`), `m(a)`, `a ∈ GL(V)`, acts by
`φ ↦ |det a|^{1/2} φ(a^* ·)`, `a^* f = f ∘ a`. -/
theorem siegelLeviWeil_dualSiegelLevi_apply {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [TopologicalSpace (Module.Dual F V)]
    [IsModuleTopology F (Module.Dual F V)] (a : V ≃ₗ[F] V)
    (φ : SchwartzBruhat (Module.Dual F V)) (f : Module.Dual F V) :
    (siegelLeviWeil (LinearMap.id : Module.Dual F V →ₗ[F] V →ₗ[F] F) (dualSiegelLevi F V a) φ :
        Module.Dual F V → ℂ) f =
      ((distribHaarChar F (LinearEquiv.det a) ^ ((1 : ℝ) / 2) : ℝ≥0) : ℂ) *
        (φ : Module.Dual F V → ℂ) (a.dualMap f) := by
  have hdet : LinearEquiv.det a.symm.dualMap = (LinearEquiv.det a)⁻¹ := by
    refine Units.ext ?_
    rw [LinearEquiv.coe_det, ← map_inv, ← LinearEquiv.det_symm, LinearEquiv.coe_det]
    exact LinearMap.det_dualMap (a.symm : V →ₗ[F] V)
  rw [siegelLeviWeil_apply]
  change ((distribHaarChar F (LinearEquiv.det a.symm.dualMap) ^ (-(1 : ℝ) / 2) : ℝ≥0) : ℂ) *
      (φ : Module.Dual F V → ℂ) (a.symm.dualMap.symm f) = _
  rw [hdet, map_inv, NNReal.inv_rpow, ← NNReal.rpow_neg, neg_div, neg_neg]
  rfl

end Local

end Langlands.Theta
