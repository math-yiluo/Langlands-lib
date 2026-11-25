import Langlands.Theta.Metaplectic.Defs
import Langlands.Theta.Metaplectic.Exact
import Langlands.Theta.Heisenberg.InvariantForm
import Langlands.Theta.Heisenberg.SchrodingerInduced
import Langlands.HarmonicAnalysis.FiniteDimensionalQuotient
import Langlands.HarmonicAnalysis.Bicharacter.DualMeasure

/-!
# The standard Weil operator of a polarization

GKT §2.3.1 (Definition 2.9, Proposition 2.13 and (2.15)–(2.17), pp. 53–55). Let
`β : X →ₗ[F] Y →ₗ[F] F` be a perfect pairing of finite-dimensional spaces over a nonarchimedean
local field and `W = X × Y` with `polarizedForm β`. The Schrödinger model `schrodingerSB` lives on
`S(X)`; in the book's notation `W = X_B ⊕ Y_B` with `X_B = 0 × Y` (the Lagrangian of the induced
model) and `Y_B = X × 0`, and `⟨y_B, x_B⟩ = β(y_B, x_B)`.

For `g` in the isometry group write `g⁻¹ (x, y) = (d x + c y, b x + a y)` (the book's
`g⁻¹ = [[a, b], [c, d]]` with respect to `X_B ⊕ Y_B`): `standardC g = c : Y → X` is the c-part of
`g⁻¹` (Definition 2.15), and `standardKernel g = ker c` is the book's `gX ∩ X` (2.15). For a Haar
measure `μ` on `Y ⧸ ker c` (the book's `ker(c) \ X`),

`standardOperatorWith μ g φ (x) = ∫_{Y / ker c} ψ(½ β(x', y') - ½ β(x, y)) φ(x') dμ(y)`,
`(x', y') = g⁻¹ (x, y)`,

which is the book's (2.10) read through the restriction `R_{X,Y}` (Theorem 1.13): the integrand is
`f_φ (g⁻¹ · ((0, y) (x, 0)))` for the induced function `f_φ`. Expanded, this is (2.17):
`ψ(½ β(dx, bx)) ∫ ψ(β(cy, bx) + ½ β(cy, ay)) φ(cy + dx) dμ(y)` (`standardIntegrand_eq`).

* `standardOperatorWith_schrodinger`: it intertwines `σ` with `σ ∘ g` (Proposition 2.5 through
  (2.12)); it preserves `S(X)` and is not zero.
* `standardOperator g`: the operator for the Haar measure that makes it unitary (the book's
  `d_g x`, "the unique measure so that `r(g)` is unitary"): `C^{-1/2} • standardOperatorWith μ g`
  for the constant `C > 0` of `exists_pos_schwartzBruhatInner_map`. It is unitary
  (`standardOperator_inner`), `d_g` is the only Haar measure with this property
  (`standardOperatorWith_inner_iff`, Proposition 2.13), and `(g, r(g))` lies in the metaplectic
  group of pairs (`standardPair`, Definition 2.9).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal Pointwise

namespace Langlands.Theta

open HeisenbergGroup Langlands.HarmonicAnalysis
open Langlands.LinearMap.BilinForm (isometryGroup)

universe u v w

section Blocks

variable {F : Type u} [CommRing F] {X : Type v} {Y : Type w} [AddCommGroup X] [Module F X]
  [AddCommGroup Y] [Module F Y] {β : X →ₗ[F] Y →ₗ[F] F}

/-- The linear automorphism `g⁻¹` of `X × Y`. -/
abbrev isometryInv (g : isometryGroup (polarizedForm β)) : (X × Y) ≃ₗ[F] (X × Y) :=
  ((g⁻¹ : isometryGroup (polarizedForm β)) : (X × Y) ≃ₗ[F] (X × Y))

/-- **The c-part of `g⁻¹`** (GKT Definition 2.15, (2.18)): `y ↦ (g⁻¹ (0, y)).1`, a map `Y → X`
(the book's `c : X_B → Y_B`). -/
def standardC (g : isometryGroup (polarizedForm β)) : Y →ₗ[F] X :=
  LinearMap.fst F X Y ∘ₗ (isometryInv g).toLinearMap ∘ₗ LinearMap.inr F X Y

theorem standardC_apply (g : isometryGroup (polarizedForm β)) (y : Y) :
    standardC g y = (isometryInv g (0, y)).1 := rfl

/-- **`ker c = gX ∩ X`** (GKT (2.15)): the `y` with `g⁻¹ (0, y) ∈ 0 × Y`. -/
def standardKernel (g : isometryGroup (polarizedForm β)) : Submodule F Y :=
  LinearMap.ker (standardC g)

theorem mem_standardKernel {g : isometryGroup (polarizedForm β)} {y : Y} :
    y ∈ standardKernel g ↔ (isometryInv g (0, y)).1 = 0 :=
  Iff.rfl

/-- `g⁻¹` preserves the form. -/
theorem polarizedForm_isometryInv (g : isometryGroup (polarizedForm β)) (w w' : X × Y) :
    polarizedForm β (isometryInv g w) (isometryInv g w') = polarizedForm β w w' :=
  (g⁻¹).2 w w'

/-- On `ker c`, `β (x', a k) = β (x, k)` where `(x', ·) = g⁻¹ (x, y)` and `a k = (g⁻¹ (0, k)).2`. -/
theorem pairing_isometryInv_kernel (g : isometryGroup (polarizedForm β)) {k : Y}
    (hk : k ∈ standardKernel g) (w : X × Y) :
    β (isometryInv g w).1 (isometryInv g (0, k)).2 = β w.1 k := by
  have h := polarizedForm_isometryInv g w (0, k)
  have hk' : (isometryInv g (0, k)).1 = 0 := hk
  simp only [polarizedForm_apply, hk', map_zero, LinearMap.zero_apply, sub_zero] at h
  exact h

/-- The d-part of `g⁻¹`: `x ↦ (g⁻¹ (x, 0)).1` (the book's `d : Y_B → Y_B`). -/
def standardD (g : isometryGroup (polarizedForm β)) : X →ₗ[F] X :=
  LinearMap.fst F X Y ∘ₗ (isometryInv g).toLinearMap ∘ₗ LinearMap.inl F X Y

/-- The b-part of `g⁻¹`: `x ↦ (g⁻¹ (x, 0)).2` (the book's `b : Y_B → X_B`). -/
def standardB (g : isometryGroup (polarizedForm β)) : X →ₗ[F] Y :=
  LinearMap.snd F X Y ∘ₗ (isometryInv g).toLinearMap ∘ₗ LinearMap.inl F X Y

/-- The a-part of `g⁻¹`: `y ↦ (g⁻¹ (0, y)).2` (the book's `a : X_B → X_B`). -/
def standardA (g : isometryGroup (polarizedForm β)) : Y →ₗ[F] Y :=
  LinearMap.snd F X Y ∘ₗ (isometryInv g).toLinearMap ∘ₗ LinearMap.inr F X Y

/-- `g⁻¹ (x, y) = (d x + c y, b x + a y)`. -/
theorem isometryInv_apply_eq (g : isometryGroup (polarizedForm β)) (x : X) (y : Y) :
    isometryInv g (x, y) = (standardD g x + standardC g y, standardB g x + standardA g y) := by
  have : ((x, y) : X × Y) = (x, 0) + (0, y) := by simp
  rw [this, map_add]
  rfl

/-- The symplectic relation between the blocks: `β(d x, a y) - β(c y, b x) = β(x, y)`. -/
theorem pairing_standardD_standardA (g : isometryGroup (polarizedForm β)) (x : X) (y : Y) :
    β (standardD g x) (standardA g y) - β (standardC g y) (standardB g x) = β x y := by
  have h := polarizedForm_isometryInv g (x, 0) (0, y)
  simp only [polarizedForm_apply, map_zero, sub_zero] at h
  exact h

end Blocks

section Integrand

variable {F : Type u} [CommRing F] [Invertible (2 : F)] {X : Type v} {Y : Type w} [AddCommGroup X]
  [Module F X] [AddCommGroup Y] [Module F Y] {β : X →ₗ[F] Y →ₗ[F] F} (ψ : AddChar F ℂ)

/-- **The integrand of the standard operator**: `ψ(½ β(x', y') - ½ β(x, y)) φ(x')` with
`(x', y') = g⁻¹ (x, y)`; it is the induced function `f_φ` of GKT Theorem 1.13 at
`g⁻¹ · ((0, y) (x, 0))`. -/
def standardIntegrand (g : isometryGroup (polarizedForm β)) (φ : X → ℂ) (x : X) (y : Y) : ℂ :=
  ψ (⅟2 * β (isometryInv g (x, y)).1 (isometryInv g (x, y)).2 - ⅟2 * β x y) *
    φ (isometryInv g (x, y)).1

/-- The integrand is invariant under `ker c`. -/
theorem standardIntegrand_add_kernel (g : isometryGroup (polarizedForm β)) (φ : X → ℂ) (x : X)
    (y : Y) {k : Y} (hk : k ∈ standardKernel g) :
    standardIntegrand ψ g φ x (y + k) = standardIntegrand ψ g φ x y := by
  have e : isometryInv g (x, y + k) = isometryInv g (x, y) + isometryInv g (0, k) := by
    rw [← map_add]; simp
  have hk' : (isometryInv g (0, k)).1 = 0 := hk
  have hp := pairing_isometryInv_kernel g hk (x, y)
  simp only [standardIntegrand, e, Prod.fst_add, Prod.snd_add, hk', add_zero, map_add]
  congr 2
  rw [hp]
  ring

/-- **The integrand under the Schrödinger operators**: the integrand of `σ(h) φ` at `(x, y)` is
`ψ(t + β(x, y₁) + ½ β(x₁, y₁))` times the integrand of `φ` at `(x + x₁, y + y₁)`, where
`((x₁, y₁), t) = g · h`. -/
theorem standardIntegrand_schrodinger (g : isometryGroup (polarizedForm β))
    (h : HeisenbergGroup (polarizedForm β)) (φ : X → ℂ) (x : X) (y : Y) :
    standardIntegrand ψ g (schrodinger ψ β h φ) x y =
      ψ (h.cen + β x ((g : (X × Y) ≃ₗ[F] X × Y) h.vec).2 +
          ⅟2 * β ((g : (X × Y) ≃ₗ[F] X × Y) h.vec).1 ((g : (X × Y) ≃ₗ[F] X × Y) h.vec).2) *
        standardIntegrand ψ g φ (x + ((g : (X × Y) ≃ₗ[F] X × Y) h.vec).1)
          (y + ((g : (X × Y) ≃ₗ[F] X × Y) h.vec).2) := by
  set v := (g : (X × Y) ≃ₗ[F] X × Y) h.vec with hv
  have hinv : isometryInv g v = h.vec := by
    rw [hv]
    change ((g⁻¹ * g : isometryGroup (polarizedForm β)) : (X × Y) ≃ₗ[F] X × Y) h.vec = h.vec
    rw [inv_mul_cancel]; rfl
  have e : isometryInv g (x + v.1, y + v.2) = isometryInv g (x, y) + h.vec := by
    rw [← hinv, ← map_add]; rfl
  have hiso := polarizedForm_isometryInv g (x, y) v
  rw [hinv] at hiso
  simp only [polarizedForm_apply] at hiso
  have h2 : (⅟2 : F) + ⅟2 = 1 := by rw [← two_mul, mul_invOf_self]
  set X' := (isometryInv g (x, y)).1
  set Y' := (isometryInv g (x, y)).2
  have key : ⅟2 * β X' Y' - ⅟2 * β x y + (h.cen + (β X' h.vec.2 + ⅟2 * β h.vec.1 h.vec.2)) =
      h.cen + β x v.2 + ⅟2 * β v.1 v.2 +
        (⅟2 * β (X' + h.vec.1) (Y' + h.vec.2) - ⅟2 * β (x + v.1) (y + v.2)) := by
    simp only [map_add, LinearMap.add_apply]
    linear_combination (⅟2 : F) * hiso - (β X' h.vec.2 - β x v.2) * h2
  simp only [standardIntegrand, schrodinger_apply, schrodingerFun_apply, e, Prod.fst_add,
    Prod.snd_add, Pi.smul_apply, smul_eq_mul]
  calc ψ (⅟2 * β X' Y' - ⅟2 * β x y) *
        (ψ h.cen * (ψ (β X' h.vec.2 + ⅟2 * β h.vec.1 h.vec.2) * φ (X' + h.vec.1)))
      = ψ (⅟2 * β X' Y' - ⅟2 * β x y + (h.cen + (β X' h.vec.2 + ⅟2 * β h.vec.1 h.vec.2))) *
          φ (X' + h.vec.1) := by
        simp only [AddChar.map_add_eq_mul]; ring
    _ = _ := by rw [key]; simp only [AddChar.map_add_eq_mul]; ring

/-- **GKT (2.17)**: in terms of the blocks of `g⁻¹ = [[a, b], [c, d]]`, the integrand is
`ψ(½ β(dx, bx)) ψ(β(cy, bx) + ½ β(cy, ay)) φ(cy + dx)`. -/
theorem standardIntegrand_eq (g : isometryGroup (polarizedForm β)) (φ : X → ℂ) (x : X) (y : Y) :
    standardIntegrand ψ g φ x y =
      ψ (⅟2 * β (standardD g x) (standardB g x)) *
        ψ (β (standardC g y) (standardB g x) + ⅟2 * β (standardC g y) (standardA g y)) *
          φ (standardC g y + standardD g x) := by
  have h := pairing_standardD_standardA g x y
  rw [standardIntegrand, isometryInv_apply_eq, ← AddChar.map_add_eq_mul, add_comm (standardC g y)]
  congr 2
  simp only [map_add, LinearMap.add_apply]
  have h2 : (⅟2 : F) * 2 = 1 := invOf_mul_self 2
  linear_combination (⅟2 : F) * h + (β (standardC g y) (standardB g x)) * h2

end Integrand

section Local

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Invertible (2 : F)]
  {X : Type v} [AddCommGroup X] [Module F X] [FiniteDimensional F X] [TopologicalSpace X]
  [IsModuleTopology F X] [IsTopologicalAddGroup X]
  {Y : Type w} [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y] [TopologicalSpace Y]
  [IsModuleTopology F Y]
  {β : X →ₗ[F] Y →ₗ[F] F} {ψ : AddChar F ℂ}

variable (ψ) in
/-- The integrand on the quotient `Y ⧸ ker c` (the book's `ker(c) \ X`). -/
def standardIntegrandQ (g : isometryGroup (polarizedForm β)) (φ : X → ℂ) (x : X) :
    Y ⧸ standardKernel g → ℂ :=
  Quotient.lift (standardIntegrand ψ g φ x) fun a b hab => by
    have hab' : a - b ∈ standardKernel g := (Submodule.quotientRel_def _).1 hab
    rw [← standardIntegrand_add_kernel ψ g φ x b hab', add_sub_cancel]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F X]
  [TopologicalSpace X] [IsModuleTopology F X] [IsTopologicalAddGroup X] [FiniteDimensional F Y]
  [TopologicalSpace Y] [IsModuleTopology F Y] in
@[simp] theorem standardIntegrandQ_mk (g : isometryGroup (polarizedForm β)) (φ : X → ℂ) (x : X)
    (y : Y) : standardIntegrandQ ψ g φ x (Submodule.Quotient.mk y) = standardIntegrand ψ g φ x y :=
  rfl

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [Invertible (2 : F)] [FiniteDimensional F X]
  [IsTopologicalAddGroup X] [FiniteDimensional F Y] in
/-- `y ↦ g⁻¹ (x, y)` is continuous. -/
theorem continuous_isometryInv_mk (g : isometryGroup (polarizedForm β)) (x : X) :
    Continuous fun y : Y => isometryInv g (x, y) :=
  (continuous_of_linearMap' (isometryInv g).toLinearMap).comp
    (continuous_const.prodMk continuous_id)

omit [IsTopologicalAddGroup X] [FiniteDimensional F Y] in
theorem continuous_standardIntegrand (hψ : Continuous ψ) (g : isometryGroup (polarizedForm β))
    {φ : X → ℂ} (hφ : Continuous φ) (x : X) : Continuous (standardIntegrand ψ g φ x) := by
  have h1 := continuous_isometryInv_mk g x
  have hb := continuous_pairing β
  refine (hψ.comp ?_).mul (hφ.comp (continuous_fst.comp h1))
  exact (continuous_const.mul (hb.comp ((continuous_fst.comp h1).prodMk
    (continuous_snd.comp h1)))).sub (continuous_const.mul (hb.comp (continuous_const.prodMk
      continuous_id)))

omit [IsTopologicalAddGroup X] [FiniteDimensional F Y] in
theorem continuous_standardIntegrandQ (hψ : Continuous ψ) (g : isometryGroup (polarizedForm β))
    {φ : X → ℂ} (hφ : Continuous φ) (x : X) : Continuous (standardIntegrandQ ψ g φ x) :=
  (continuous_standardIntegrand hψ g hφ x).quotient_lift _

/-- The c-part on the quotient, `Y ⧸ ker c → X`, injective. -/
def standardCQ (g : isometryGroup (polarizedForm β)) : (Y ⧸ standardKernel g) →ₗ[F] X :=
  (standardKernel g).liftQ (standardC g) le_rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Invertible (2 : F)]
  [FiniteDimensional F X] [TopologicalSpace X] [IsModuleTopology F X] [IsTopologicalAddGroup X]
  [FiniteDimensional F Y] [TopologicalSpace Y] [IsModuleTopology F Y] in
@[simp] theorem standardCQ_mk (g : isometryGroup (polarizedForm β)) (y : Y) :
    standardCQ g (Submodule.Quotient.mk y) = standardC g y := rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Invertible (2 : F)]
  [FiniteDimensional F X] [TopologicalSpace X] [IsModuleTopology F X] [IsTopologicalAddGroup X]
  [FiniteDimensional F Y] [TopologicalSpace Y] [IsModuleTopology F Y] in
theorem standardCQ_injective (g : isometryGroup (polarizedForm β)) :
    Function.Injective (standardCQ g) :=
  LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)

omit [FiniteDimensional F Y] in
/-- **The integrand has compact support** on `Y ⧸ ker c`: it vanishes unless `c y` lies in a
translate of the support of `φ`. -/
theorem hasCompactSupport_standardIntegrandQ (g : isometryGroup (polarizedForm β))
    {φ : X → ℂ} (hφ : HasCompactSupport φ) (x : X) :
    HasCompactSupport (standardIntegrandQ ψ g φ x) := by
  have := t2Space_of_finiteDimensional F X
  set x₀ := (isometryInv g (x, 0)).1
  have hS : IsCompact ((fun z => z - x₀) '' tsupport φ) :=
    hφ.isCompact.image (continuous_id.sub continuous_const)
  refine HasCompactSupport.intro (isCompact_preimage_of_injective (standardCQ g)
    (standardCQ_injective g) hS) fun q hq => ?_
  induction q using Submodule.Quotient.induction_on with | H y => ?_
  rw [standardIntegrandQ_mk, standardIntegrand]
  have e : (isometryInv g (x, y)).1 = x₀ + standardC g y := by
    rw [standardC_apply, ← Prod.fst_add, ← map_add]; simp
  have h0 : φ (isometryInv g (x, y)).1 = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => hq ⟨_, h, by
      simp only [e, standardCQ_mk, add_sub_cancel_left]⟩
  rw [h0, mul_zero]

section Operator

variable [MeasurableSpace Y] [BorelSpace Y]

variable (ψ) in
/-- **The standard operator for a Haar measure `μ` on `Y ⧸ ker c`**, on functions:
`φ ↦ (x ↦ ∫_{Y / ker c} ψ(½ β(x', y') - ½ β(x, y)) φ(x') dμ(y))`, `(x', y') = g⁻¹ (x, y)` (GKT
(2.10), (2.16) through the restriction `R_{X,Y}`). -/
def standardOperatorFun (g : isometryGroup (polarizedForm β)) (μ : Measure (Y ⧸ standardKernel g))
    (φ : X → ℂ) : X → ℂ :=
  fun x => ∫ q, standardIntegrandQ ψ g φ x q ∂μ

omit [IsTopologicalAddGroup X] [FiniteDimensional F Y] in
theorem integrable_standardIntegrandQ (hψ : Continuous ψ) (g : isometryGroup (polarizedForm β))
    (μ : Measure (Y ⧸ standardKernel g)) [μ.IsAddHaarMeasure] {φ : X → ℂ}
    (hφ : φ ∈ schwartzBruhatSubmodule X) (x : X) : Integrable (standardIntegrandQ ψ g φ x) μ := by
  have := IsModuleTopology.isTopologicalAddGroup F X
  exact (continuous_standardIntegrandQ hψ g hφ.1.continuous x).integrable_of_hasCompactSupport
    (hasCompactSupport_standardIntegrandQ g hφ.2 x)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F X]
  [TopologicalSpace X] [IsModuleTopology F X] [IsTopologicalAddGroup X] [FiniteDimensional F Y]
  [TopologicalSpace Y] [IsModuleTopology F Y] [MeasurableSpace Y] [BorelSpace Y] in
theorem standardIntegrandQ_add (g : isometryGroup (polarizedForm β)) (φ φ' : X → ℂ) (x : X) :
    standardIntegrandQ ψ g (φ + φ') x =
      standardIntegrandQ ψ g φ x + standardIntegrandQ ψ g φ' x := by
  funext q
  induction q using Submodule.Quotient.induction_on with | H y => ?_
  simp [standardIntegrand, mul_add]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F X]
  [TopologicalSpace X] [IsModuleTopology F X] [IsTopologicalAddGroup X] [FiniteDimensional F Y]
  [TopologicalSpace Y] [IsModuleTopology F Y] [MeasurableSpace Y] [BorelSpace Y] in
theorem standardIntegrandQ_smul (g : isometryGroup (polarizedForm β)) (c : ℂ) (φ : X → ℂ) (x : X) :
    standardIntegrandQ ψ g (c • φ) x = c • standardIntegrandQ ψ g φ x := by
  funext q
  induction q using Submodule.Quotient.induction_on with | H y => ?_
  simp only [standardIntegrandQ_mk, standardIntegrand, Pi.smul_apply, smul_eq_mul]
  ring

omit [FiniteDimensional F X] [TopologicalSpace X] [IsModuleTopology F X]
  [IsTopologicalAddGroup X] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [FiniteDimensional F Y] in
/-- **The standard operator intertwines `σ` with `σ ∘ g`** (GKT Proposition 2.5 and (2.12)):
`r_μ(g) ∘ σ(h) = σ(g · h) ∘ r_μ(g)`, on all functions. -/
theorem standardOperatorFun_schrodinger (g : isometryGroup (polarizedForm β))
    (μ : Measure (Y ⧸ standardKernel g)) [μ.IsAddHaarMeasure]
    (h : HeisenbergGroup (polarizedForm β)) (φ : X → ℂ) :
    standardOperatorFun ψ g μ (schrodinger ψ β h φ) =
      schrodinger ψ β (isometryAction (polarizedForm β) g h) (standardOperatorFun ψ g μ φ) := by
  have := IsModuleTopology.isTopologicalAddGroup F Y
  funext x
  set v := (g : (X × Y) ≃ₗ[F] X × Y) h.vec
  have hI : standardIntegrandQ ψ g (schrodinger ψ β h φ) x = fun q =>
      ψ (h.cen + β x v.2 + ⅟2 * β v.1 v.2) *
        standardIntegrandQ ψ g φ (x + v.1) (q + Submodule.Quotient.mk v.2) := by
    funext q
    induction q using Submodule.Quotient.induction_on with | H y => ?_
    rw [standardIntegrandQ_mk, standardIntegrand_schrodinger, ← Submodule.Quotient.mk_add,
      standardIntegrandQ_mk]
  simp only [standardOperatorFun, hI, integral_const_mul]
  rw [integral_add_right_eq_self (μ := μ) (fun q => standardIntegrandQ ψ g φ (x + v.1) q)
    (Submodule.Quotient.mk v.2)]
  simp only [schrodinger_apply, isometryAction_apply, Pi.smul_apply, schrodingerFun_apply,
    smul_eq_mul, AddChar.map_add_eq_mul]
  change _ = ψ h.cen * (ψ (β x v.2) * ψ (⅟2 * β v.1 v.2) *
    ∫ q, standardIntegrandQ ψ g φ (x + v.1) q ∂μ)
  ring

omit [Invertible (2 : F)] [IsTopologicalAddGroup X] [MeasurableSpace Y] [BorelSpace Y] in
/-- `ψ ∘ β` is a perfect pairing for a perfect `β` and a non-trivial continuous `ψ`. -/
theorem isPerfectBicharacter_pairing [β.IsPerfPair] (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) :
    IsPerfectBicharacter fun x y => ψ (β x y) :=
  isPerfectBicharacter_of_nondegenerate hψ
    (SchrodingerIrreducible.Internal.norm_addChar_eq_one hψ) hψ1 β
    (fun y hy => (LinearMap.IsPerfPair.bijective_right β).1
      (LinearMap.ext fun x => by simpa using hy x))
    (fun x hx => (LinearMap.IsPerfPair.bijective_left β).1
      (LinearMap.ext fun y => by simpa using hx y))

/-- **The standard operator preserves the Schwartz–Bruhat functions.** The output is fixed by
`σ(g · h)` for `h` in an open subgroup fixing `φ` (smoothness of the model); invariance under small
translations makes it locally constant, invariance under the multiplications `ψ(β(·, y))` for small
`y` confines its support to a compact set (the pairing is perfect). -/
theorem standardOperatorFun_mem [β.IsPerfPair] (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (g : isometryGroup (polarizedForm β)) (μ : Measure (Y ⧸ standardKernel g))
    [μ.IsAddHaarMeasure] {φ : X → ℂ} (hφ : φ ∈ schwartzBruhatSubmodule X) :
    standardOperatorFun ψ g μ φ ∈ schwartzBruhatSubmodule X := by
  set Fφ := standardOperatorFun ψ g μ φ
  have hβ : ∀ y, Continuous fun x => β x y := fun y =>
    (continuous_pairing β).comp (continuous_id.prodMk continuous_const)
  obtain ⟨K₀, hK₀⟩ := isSmooth_schrodingerSB hψ hβ ⟨φ, hφ⟩
  have hinv : ∀ k ∈ K₀, Fφ = schrodinger ψ β (isometryAction _ g k) Fφ := fun k hk => by
    have h1 : schrodinger ψ β k φ = φ :=
      congrArg Subtype.val ((Representation.mem_invariants _ _).1 hK₀ ⟨k, hk⟩)
    rw [← standardOperatorFun_schrodinger, h1]
  set N := (isometryAction (polarizedForm β) g⁻¹) ⁻¹' (K₀ : Set (HeisenbergGroup (polarizedForm β)))
  have hNo : IsOpen N := K₀.isOpen.preimage (continuous_isometryAction g⁻¹)
  have hN1 : (1 : HeisenbergGroup (polarizedForm β)) ∈ N := by
    change isometryAction (polarizedForm β) g⁻¹ 1 ∈ K₀
    rw [map_one]; exact K₀.one_mem
  have hNsub : ∀ h' ∈ N, Fφ = schrodinger ψ β h' Fφ := fun h' hh' => by
    have := hinv _ hh'
    rwa [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at this
  have hX : ∀ᶠ x₀ in 𝓝 (0 : X), ofVec ((x₀, 0) : X × Y) ∈ N := by
    have hc : Continuous fun x₀ : X =>
        (ofVec ((x₀, 0) : X × Y) : HeisenbergGroup (polarizedForm β)) :=
      continuous_ofVec.comp (continuous_id.prodMk continuous_const)
    exact hc.tendsto 0 (hNo.mem_nhds (by rw [Prod.mk_zero_zero, ofVec_zero]; exact hN1))
  have hY : ∀ᶠ y₀ in 𝓝 (0 : Y), ofVec ((0, y₀) : X × Y) ∈ N := by
    have hc : Continuous fun y₀ : Y =>
        (ofVec ((0, y₀) : X × Y) : HeisenbergGroup (polarizedForm β)) :=
      continuous_ofVec.comp (continuous_const.prodMk continuous_id)
    exact hc.tendsto 0 (hNo.mem_nhds (by rw [Prod.mk_zero_zero, ofVec_zero]; exact hN1))
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    rw [← map_add_left_nhds_zero x, Filter.eventually_map]
    filter_upwards [hX] with x₀ hx₀
    have := congrFun (hNsub _ hx₀) x
    simp only [schrodinger_ofVec, schrodingerFun_apply, map_zero, mul_zero, add_zero,
      AddChar.map_zero_eq_one, one_mul] at this
    exact this.symm
  · obtain ⟨Kc, hKc, hKcx⟩ := (isPerfectBicharacter_pairing (β := β) hψ hψ1).big_right _ hY
    refine HasCompactSupport.intro hKc fun x hx => ?_
    by_contra hne
    refine hx (hKcx x fun y hy => ?_)
    have := congrFun (hNsub _ hy) x
    simp only [schrodinger_ofVec, schrodingerFun_apply, map_zero, LinearMap.zero_apply, mul_zero,
      add_zero] at this
    exact (mul_eq_right₀ hne).1 this.symm

/-- The Schrödinger model of `(β, ψ)` with the continuity of `β` read off the module topologies
(`schrodingerSB`). -/
abbrev schrodingerModel (hψ : Continuous ψ) :
    Representation ℂ (HeisenbergGroup (polarizedForm β)) (SchwartzBruhat X) :=
  schrodingerSB hψ fun _ => (continuous_pairing β).comp (continuous_id.prodMk continuous_const)

/-- **The standard operator for a Haar measure `μ` on `Y ⧸ ker c`**, as a linear map of `S(X)`. -/
def standardOperatorWith [β.IsPerfPair] (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (g : isometryGroup (polarizedForm β)) (μ : Measure (Y ⧸ standardKernel g))
    [μ.IsAddHaarMeasure] : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat X where
  toFun φ := ⟨standardOperatorFun ψ g μ φ, standardOperatorFun_mem hψ hψ1 g μ φ.2⟩
  map_add' φ φ' := Subtype.ext <| funext fun x => by
    change ∫ q, standardIntegrandQ ψ g ((φ : X → ℂ) + φ') x q ∂μ =
      (∫ q, standardIntegrandQ ψ g φ x q ∂μ) + ∫ q, standardIntegrandQ ψ g φ' x q ∂μ
    rw [standardIntegrandQ_add]
    exact integral_add (integrable_standardIntegrandQ hψ g μ φ.2 x)
      (integrable_standardIntegrandQ hψ g μ φ'.2 x)
  map_smul' c φ := Subtype.ext <| funext fun x => by
    change ∫ q, standardIntegrandQ ψ g (c • (φ : X → ℂ)) x q ∂μ =
      c * ∫ q, standardIntegrandQ ψ g φ x q ∂μ
    rw [standardIntegrandQ_smul]
    exact integral_smul c _

theorem standardOperatorWith_apply [β.IsPerfPair] (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (g : isometryGroup (polarizedForm β)) (μ : Measure (Y ⧸ standardKernel g))
    [μ.IsAddHaarMeasure] (φ : SchwartzBruhat X) (x : X) :
    (standardOperatorWith hψ hψ1 g μ φ : X → ℂ) x =
      ∫ q, standardIntegrandQ ψ g φ x q ∂μ := rfl

/-- The standard operator intertwines the Schrödinger model with its composition with `g`. -/
theorem standardOperatorWith_comp [β.IsPerfPair] (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (g : isometryGroup (polarizedForm β)) (μ : Measure (Y ⧸ standardKernel g))
    [μ.IsAddHaarMeasure] (h : HeisenbergGroup (polarizedForm β)) :
    standardOperatorWith hψ hψ1 g μ ∘ₗ schrodingerModel hψ h =
      schrodingerModel hψ (isometryAction (polarizedForm β) g h) ∘ₗ
        standardOperatorWith hψ hψ1 g μ :=
  LinearMap.ext fun φ => Subtype.ext (standardOperatorFun_schrodinger g μ h φ)

omit [FiniteDimensional F Y] in
/-- **The standard operator is not zero**: at `x = 0` it takes the indicator of a small compact
open subgroup `L` of `X` to the measure of `{q | c q ∈ L}` (the phase `ψ(½ β(c y, a y))` is `1`
there). -/
theorem exists_standardOperatorFun_apply_zero_ne_zero (hψ : Continuous ψ)
    (g : isometryGroup (polarizedForm β)) (μ : Measure (Y ⧸ standardKernel g))
    [μ.IsAddHaarMeasure] :
    ∃ φ ∈ schwartzBruhatSubmodule X, standardOperatorFun ψ g μ φ 0 ≠ 0 := by
  have := IsModuleTopology.isTopologicalAddGroup F Y
  have hψl : IsLocallyConstant ψ := isLocallyConstant_of_continuous_addChar ψ hψ
  set P : Y → ℂ := standardIntegrand ψ g (fun _ => 1) 0 with hP_def
  have hPc : IsLocallyConstant P := by
    have h1 := continuous_isometryInv_mk g (0 : X)
    have hb := continuous_pairing β
    refine (hψl.comp_continuous ?_).mul (IsLocallyConstant.const 1)
    exact (continuous_const.mul (hb.comp ((continuous_fst.comp h1).prodMk
      (continuous_snd.comp h1)))).sub (continuous_const.mul (hb.comp (continuous_const.prodMk
        continuous_id)))
  have hP0 : P 0 = 1 := by
    have h00 : isometryInv g ((0 : X), (0 : Y)) = 0 := by rw [Prod.mk_zero_zero, map_zero]
    rw [hP_def]
    unfold standardIntegrand
    rw [h00]
    simp
  set U₁ := (Submodule.Quotient.mk : Y → Y ⧸ standardKernel g) '' (P ⁻¹' {1})
  have hU₁o : IsOpen U₁ :=
    Submodule.isOpenMap_mkQ (standardKernel g) _ (hPc.isOpen_fiber 1)
  have hU₁0 : (0 : Y ⧸ standardKernel g) ∈ U₁ := ⟨0, hP0, rfl⟩
  obtain ⟨π, hπ⟩ := (standardCQ g).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (standardCQ_injective g))
  have hπc : Continuous π := continuous_of_linearMap' π
  have := compactOpenExhaustion_of_finiteDimensional F X
  obtain ⟨L, hLc, hLo, hLU⟩ := CompactOpenExhaustion.exists_subset _
    (hπc.tendsto 0 (by rw [map_zero]; exact hU₁o.mem_nhds hU₁0))
  refine ⟨(L : Set X).indicator fun _ => (1 : ℂ),
    HarmonicAnalysis.indicator_one_mem_schwartzBruhatSubmodule L hLc hLo, ?_⟩
  set S := (standardCQ g : Y ⧸ standardKernel g → X) ⁻¹' (L : Set X)
  have hI : standardIntegrandQ ψ g ((L : Set X).indicator fun _ => (1 : ℂ)) 0 =
      S.indicator fun _ => (1 : ℂ) := by
    funext q
    induction q using Submodule.Quotient.induction_on with | H y => ?_
    have e : standardIntegrand ψ g ((L : Set X).indicator fun _ => (1 : ℂ)) 0 y =
        P y * (L : Set X).indicator (fun _ => (1 : ℂ)) (standardC g y) := by
      simp [hP_def, standardIntegrand, standardC_apply]
    rw [standardIntegrandQ_mk, e]
    by_cases hy : standardC g y ∈ (L : Set X)
    · have hq : Submodule.Quotient.mk y ∈ S := hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hq, mul_one]
      have h1 : Submodule.Quotient.mk y ∈ U₁ := by
        have := hLU hy
        rwa [Set.mem_preimage, ← standardCQ_mk, ← LinearMap.comp_apply, hπ,
          LinearMap.id_apply] at this
      obtain ⟨y', hy', hyy'⟩ := h1
      have hk : y - y' ∈ standardKernel g := (Submodule.Quotient.eq _).1 hyy'.symm
      have : P y = P y' := by
        rw [hP_def, show y = y' + (y - y') by abel, standardIntegrand_add_kernel ψ g _ 0 y' hk]
      rw [this]; exact hy'
    · have hq : Submodule.Quotient.mk y ∉ S := hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hq, mul_zero]
  have hSo : IsOpen S := hLo.preimage (continuous_of_linearMap' (standardCQ g))
  have hS0 : (0 : Y ⧸ standardKernel g) ∈ S := by
    change standardCQ g 0 ∈ L; rw [map_zero]; exact L.zero_mem
  have := t2Space_of_finiteDimensional F X
  have hSc : IsCompact S := isCompact_preimage_of_injective (standardCQ g)
    (standardCQ_injective g) hLc
  have hpos : 0 < μ S := hSo.measure_pos μ ⟨0, hS0⟩
  have hfin : μ S < ⊤ := hSc.measure_lt_top
  change ∫ q, standardIntegrandQ ψ g _ 0 q ∂μ ≠ 0
  rw [hI, integral_indicator_const _ hSo.measurableSet, Complex.real_smul, mul_one]
  exact Complex.ofReal_ne_zero.2 (by
    rw [measureReal_def]; exact (ENNReal.toReal_pos hpos.ne' hfin.ne).ne')

theorem standardOperatorWith_ne_zero [β.IsPerfPair] (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (g : isometryGroup (polarizedForm β)) (μ : Measure (Y ⧸ standardKernel g))
    [μ.IsAddHaarMeasure] : standardOperatorWith hψ hψ1 g μ ≠ 0 := fun h0 => by
  obtain ⟨φ, hφ, hne⟩ := exists_standardOperatorFun_apply_zero_ne_zero hψ g μ
  apply hne
  have := congrArg (fun T : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat X =>
    ((T ⟨φ, hφ⟩ : SchwartzBruhat X) : X → ℂ) 0) h0
  exact this

end Operator

section Normalized

variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [Invertible (2 : F)] [FiniteDimensional F X]
  [IsModuleTopology F X] [IsTopologicalAddGroup X] [AddCommGroup X] in
/-- The `L²` form of `c • ν` is `c` times that of `ν`. -/
theorem schwartzBruhatInner_smul_measure (ν : Measure X) [IsFiniteMeasureOnCompacts ν] (c : ℝ≥0)
    (f f' : SchwartzBruhat X) :
    schwartzBruhatInner (c • ν) f f' = (c : ℂ) * schwartzBruhatInner ν f f' := by
  rw [schwartzBruhatInner_apply, schwartzBruhatInner_apply, integral_smul_nnreal_measure,
    NNReal.smul_def, Complex.real_smul]

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [Invertible (2 : F)] [FiniteDimensional F X]
  [IsModuleTopology F X] in
/-- A relation `⟨T φ, T φ'⟩_ν = C ⟨φ, φ'⟩_ν` for one Haar measure `ν` on `X` holds for all. -/
theorem schwartzBruhatInner_map_of_haar [LocallyCompactSpace X] [SecondCountableTopology X]
    (T : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat X) (C : ℂ)
    (ν₀ : Measure X) [ν₀.IsAddHaarMeasure]
    (h₀ : ∀ φ φ', schwartzBruhatInner ν₀ (T φ) (T φ') = C * schwartzBruhatInner ν₀ φ φ')
    (ν : Measure X) [ν.IsAddHaarMeasure] (φ φ' : SchwartzBruhat X) :
    schwartzBruhatInner ν (T φ) (T φ') = C * schwartzBruhatInner ν φ φ' := by
  obtain ⟨c, hν⟩ : ∃ c : ℝ≥0, ν = c • ν₀ := ⟨_, Measure.isAddLeftInvariant_eq_smul ν ν₀⟩
  have key : ∀ f f' : SchwartzBruhat X, schwartzBruhatInner ν f f' =
      (c : ℂ) * schwartzBruhatInner ν₀ f f' := by
    intro f f'
    rw [schwartzBruhatInner_apply, schwartzBruhatInner_apply, hν, integral_smul_nnreal_measure,
      NNReal.smul_def, Complex.real_smul]
  rw [key, key, h₀]
  ring

omit [MeasurableSpace X] [BorelSpace X] in
/-- Multiplying the Haar measure on `Y ⧸ ker c` by `c` multiplies the standard operator by `c`. -/
theorem standardOperatorWith_eq_smul [β.IsPerfPair] (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (g : isometryGroup (polarizedForm β)) (μ μ' : Measure (Y ⧸ standardKernel g))
    [μ.IsAddHaarMeasure] [μ'.IsAddHaarMeasure] {c : ℝ≥0} (h : μ' = c • μ) :
    standardOperatorWith hψ hψ1 g μ' = (c : ℂ) • standardOperatorWith hψ hψ1 g μ := by
  refine LinearMap.ext fun φ => Subtype.ext (funext fun x => ?_)
  change ∫ q, standardIntegrandQ ψ g φ x q ∂μ' = (c : ℂ) * ∫ q, standardIntegrandQ ψ g φ x q ∂μ
  rw [h, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

/-- The constant of the standard operator: `⟨r_μ φ, r_μ φ'⟩_ν = C ⟨φ, φ'⟩_ν` for every Haar measure
`ν` on `X`, with `C > 0`. -/
theorem exists_pos_standardOperatorWith_inner [β.IsPerfPair] (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (g : isometryGroup (polarizedForm β)) (μ : Measure (Y ⧸ standardKernel g))
    [μ.IsAddHaarMeasure] :
    ∃ C : ℝ, 0 < C ∧ ∀ (ν : Measure X) [ν.IsAddHaarMeasure] (φ φ' : SchwartzBruhat X),
      schwartzBruhatInner ν (standardOperatorWith hψ hψ1 g μ φ)
          (standardOperatorWith hψ hψ1 g μ φ') = (C : ℂ) * schwartzBruhatInner ν φ φ' := by
  have := locallyCompactSpace_of_finiteDimensional F X
  obtain ⟨C, hC, h⟩ := exists_pos_schwartzBruhatInner_map hψ
    (fun _ => (continuous_pairing β).comp (continuous_id.prodMk continuous_const))
    (Measure.addHaar : Measure X) hψ1 (isometryAction (polarizedForm β) g)
    (standardOperatorWith hψ hψ1 g μ) (fun h => standardOperatorWith_comp hψ hψ1 g μ h)
    (standardOperatorWith_ne_zero hψ hψ1 g μ)
  have := secondCountableTopology_of_finiteDimensional F X
  exact ⟨C, hC, fun ν _ φ φ' => schwartzBruhatInner_map_of_haar _ _ (Measure.addHaar) h ν φ φ'⟩

variable [β.IsPerfPair] (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)

/-- The constant `C(g) > 0` with `⟨r₀ φ, r₀ φ'⟩ = C(g) ⟨φ, φ'⟩`, for the operator `r₀` of the Haar
measure `addHaar` on `Y ⧸ ker c`. -/
def standardConstant (g : isometryGroup (polarizedForm β)) : ℝ :=
  (exists_pos_standardOperatorWith_inner hψ hψ1 g
    (Measure.addHaar : Measure (Y ⧸ standardKernel g))).choose

theorem standardConstant_pos (g : isometryGroup (polarizedForm β)) :
    0 < standardConstant hψ hψ1 g :=
  (exists_pos_standardOperatorWith_inner hψ hψ1 g Measure.addHaar).choose_spec.1

theorem standardOperatorWith_addHaar_inner (g : isometryGroup (polarizedForm β)) (ν : Measure X)
    [ν.IsAddHaarMeasure] (φ φ' : SchwartzBruhat X) :
    schwartzBruhatInner ν (standardOperatorWith hψ hψ1 g Measure.addHaar φ)
        (standardOperatorWith hψ hψ1 g Measure.addHaar φ') =
      (standardConstant hψ hψ1 g : ℂ) * schwartzBruhatInner ν φ φ' :=
  (exists_pos_standardOperatorWith_inner hψ hψ1 g Measure.addHaar).choose_spec.2 ν φ φ'

/-- The scalar `C(g)^{-1/2}` relating `d_g` to `addHaar`. -/
def standardScalar (g : isometryGroup (polarizedForm β)) : ℝ≥0 :=
  Real.toNNReal (standardConstant hψ hψ1 g ^ (-(1 : ℝ) / 2))

theorem standardScalar_pos (g : isometryGroup (polarizedForm β)) :
    0 < standardScalar hψ hψ1 g :=
  Real.toNNReal_pos.2 (Real.rpow_pos_of_pos (standardConstant_pos hψ hψ1 g) _)

theorem standardScalar_sq_mul (g : isometryGroup (polarizedForm β)) :
    ((standardScalar hψ hψ1 g : ℝ) ^ 2) * standardConstant hψ hψ1 g = 1 := by
  have hC := standardConstant_pos hψ hψ1 g
  rw [standardScalar, Real.coe_toNNReal _ (Real.rpow_nonneg hC.le _), ← Real.rpow_natCast,
    ← Real.rpow_mul hC.le]
  norm_num
  rw [Real.rpow_neg_one, inv_mul_cancel₀ hC.ne']

/-- **The measure `d_g`** on `Y ⧸ ker c` (GKT Proposition 2.13: the measure on `ker(c) \ X` "so
that `r(g)` is unitary"; uniqueness: `standardOperatorWith_inner_iff`). -/
def standardMeasure (g : isometryGroup (polarizedForm β)) : Measure (Y ⧸ standardKernel g) :=
  standardScalar hψ hψ1 g • Measure.addHaar

instance (g : isometryGroup (polarizedForm β)) : (standardMeasure hψ hψ1 g).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.nnreal_smul _ (standardScalar_pos hψ hψ1 g).ne'

/-- **The standard Weil operator** `r(g)` of the Schrödinger model (GKT Definition 2.9,
Proposition 2.13): the operator of the measure `d_g`. -/
def standardOperator (g : isometryGroup (polarizedForm β)) :
    SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat X :=
  standardOperatorWith hψ hψ1 g (standardMeasure hψ hψ1 g)

/-- **GKT Proposition 2.13** (in the form (2.16)): `r(g) φ (x)` is the integral of the integrand
over `Y ⧸ ker c` for the measure `d_g`. -/
theorem standardOperator_apply (g : isometryGroup (polarizedForm β)) (φ : SchwartzBruhat X)
    (x : X) : (standardOperator hψ hψ1 g φ : X → ℂ) x =
      ∫ q, standardIntegrandQ ψ g φ x q ∂(standardMeasure hψ hψ1 g) := rfl

theorem standardOperator_eq_smul (g : isometryGroup (polarizedForm β)) :
    standardOperator hψ hψ1 g =
      ((standardScalar hψ hψ1 g : ℝ≥0) : ℂ) • standardOperatorWith hψ hψ1 g Measure.addHaar :=
  standardOperatorWith_eq_smul hψ hψ1 g _ _ rfl

/-- **`r(g)` is unitary** for the `L²` form of every Haar measure on `X`. -/
theorem standardOperator_inner (g : isometryGroup (polarizedForm β)) (ν : Measure X)
    [ν.IsAddHaarMeasure] (φ φ' : SchwartzBruhat X) :
    schwartzBruhatInner ν (standardOperator hψ hψ1 g φ) (standardOperator hψ hψ1 g φ') =
      schwartzBruhatInner ν φ φ' := by
  rw [standardOperator_eq_smul]
  simp only [LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul, RingHom.id_apply,
    Complex.conj_ofReal]
  rw [standardOperatorWith_addHaar_inner]
  have h := standardScalar_sq_mul hψ hψ1 g
  calc _ = ((((standardScalar hψ hψ1 g : ℝ) ^ 2 * standardConstant hψ hψ1 g : ℝ) : ℂ)) *
        schwartzBruhatInner ν φ φ' := by push_cast; ring
    _ = _ := by rw [h, Complex.ofReal_one, one_mul]

/-- **Uniqueness of `d_g`** (GKT Proposition 2.13): `d_g` is the only Haar measure on `Y ⧸ ker c`
for which the standard operator is unitary. -/
theorem standardOperatorWith_inner_iff (g : isometryGroup (polarizedForm β))
    (μ : Measure (Y ⧸ standardKernel g)) [μ.IsAddHaarMeasure] :
    (∀ (ν : Measure X) [ν.IsAddHaarMeasure] (φ φ' : SchwartzBruhat X),
      schwartzBruhatInner ν (standardOperatorWith hψ hψ1 g μ φ)
          (standardOperatorWith hψ hψ1 g μ φ') = schwartzBruhatInner ν φ φ') ↔
      μ = standardMeasure hψ hψ1 g := by
  constructor
  · intro hu
    obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, μ = s • Measure.addHaar :=
      ⟨_, Measure.isAddLeftInvariant_eq_smul μ Measure.addHaar⟩
    have hT := standardOperatorWith_eq_smul hψ hψ1 g Measure.addHaar μ hs
    have := locallyCompactSpace_of_finiteDimensional F X
    have := compactOpenExhaustion_of_finiteDimensional F X
    obtain ⟨L, hLc, hLo, -⟩ := CompactOpenExhaustion.exists_subset (X := X) Set.univ univ_mem
    set e : SchwartzBruhat X :=
      ⟨_, HarmonicAnalysis.indicator_one_mem_schwartzBruhatSubmodule L hLc hLo⟩
    have he : schwartzBruhatInner (Measure.addHaar : Measure X) e e ≠ 0 := by
      rw [schwartzBruhatInner_self_eq_integral, Complex.ofReal_ne_zero]
      refine (integral_norm_sq_pos _ e (x := 0) ?_).ne'
      change (L : Set X).indicator (fun _ => (1 : ℂ)) 0 ≠ 0
      rw [Set.indicator_of_mem (show (0 : X) ∈ (L : Set X) from L.zero_mem)]
      exact one_ne_zero
    have h1 := hu Measure.addHaar e e
    rw [hT] at h1
    simp only [LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul, RingHom.id_apply,
      Complex.conj_ofReal] at h1
    rw [standardOperatorWith_addHaar_inner] at h1
    have h2 : ((((s : ℝ) ^ 2 * standardConstant hψ hψ1 g : ℝ)) : ℂ) *
        schwartzBruhatInner Measure.addHaar e e = 1 * schwartzBruhatInner Measure.addHaar e e := by
      calc ((((s : ℝ) ^ 2 * standardConstant hψ hψ1 g : ℝ)) : ℂ) *
            schwartzBruhatInner Measure.addHaar e e
          = (s : ℂ) * ((s : ℂ) * ((standardConstant hψ hψ1 g : ℂ) *
              schwartzBruhatInner Measure.addHaar e e)) := by push_cast; ring
        _ = _ := by rw [h1, one_mul]
    have h3 : (s : ℝ) ^ 2 * standardConstant hψ hψ1 g = 1 := by
      exact_mod_cast mul_right_cancel₀ he h2
    have h4 : (s : ℝ) = standardScalar hψ hψ1 g := by
      have hC := standardConstant_pos hψ hψ1 g
      have h5 := standardScalar_sq_mul hψ hψ1 g
      have : (s : ℝ) ^ 2 = (standardScalar hψ hψ1 g : ℝ) ^ 2 := by
        rw [← mul_right_cancel₀ hC.ne' (h3.trans h5.symm)]
      exact (pow_left_inj₀ (NNReal.coe_nonneg s) (NNReal.coe_nonneg _) two_ne_zero).1 this
    rw [hs, standardMeasure, NNReal.coe_inj.1 h4]
  · rintro rfl
    exact fun ν _ φ φ' => standardOperator_inner hψ hψ1 g ν φ φ'

/-- `r(g)` intertwines the Schrödinger model with its composition with `g`:
`r(g) ∘ σ(h) = σ(g · h) ∘ r(g)`. -/
theorem standardOperator_comp (g : isometryGroup (polarizedForm β))
    (h : HeisenbergGroup (polarizedForm β)) :
    standardOperator hψ hψ1 g ∘ₗ schrodingerModel hψ h =
      schrodingerModel hψ (isometryAction (polarizedForm β) g h) ∘ₗ standardOperator hψ hψ1 g :=
  standardOperatorWith_comp hψ hψ1 g _ h

/-- `r(g)` is injective (it is unitary). -/
theorem standardOperator_injective (g : isometryGroup (polarizedForm β)) :
    Function.Injective (standardOperator hψ hψ1 g) := by
  have := locallyCompactSpace_of_finiteDimensional F X
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hφ
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x, (φ : X → ℂ) x ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (Subtype.ext (funext h))
  have h := standardOperator_inner hψ hψ1 g Measure.addHaar φ φ
  rw [hφ, map_zero, schwartzBruhatInner_self_eq_integral] at h
  exact (integral_norm_sq_pos _ φ hx).ne' (by exact_mod_cast h.symm)

/-- `r(g)` is surjective: `r(g) r(g⁻¹)` commutes with the Schrödinger model, hence is a scalar
(Schur's lemma, `Renard.Smooth.sigmaCompactSchur`), not zero since both factors are injective. -/
theorem standardOperator_surjective (g : isometryGroup (polarizedForm β)) :
    Function.Surjective (standardOperator hψ hψ1 g) := by
  set T := standardOperator hψ hψ1 g
  set T' := standardOperator hψ hψ1 g⁻¹
  set ρ := schrodingerModel (β := β) hψ
  have hcomm : ∀ h, (T ∘ₗ T') ∘ₗ ρ h = ρ h ∘ₗ (T ∘ₗ T') := by
    intro h
    rw [LinearMap.comp_assoc, standardOperator_comp hψ hψ1 g⁻¹, ← LinearMap.comp_assoc,
      standardOperator_comp hψ hψ1 g, LinearMap.comp_assoc, ← MulAut.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, MulAut.one_apply]
  let f : ρ.IntertwiningMap ρ := ⟨T ∘ₗ T', hcomm⟩
  obtain ⟨c, hc⟩ := (Renard.Smooth.sigmaCompactSchur.{max u v w, v, v}
    (HeisenbergGroup (polarizedForm β)) (SchwartzBruhat X) ρ
    (isSmooth_schrodingerSB hψ _) (isIrreducible_schrodingerSB hψ hψ1 _)).1 f
  have hTT : ∀ φ, T (T' φ) = c • φ := fun φ =>
    congrArg (fun k : ρ.IntertwiningMap ρ => k φ) hc
  have := compactOpenExhaustion_of_finiteDimensional F X
  obtain ⟨L, hLc, hLo, -⟩ := CompactOpenExhaustion.exists_subset (X := X) Set.univ univ_mem
  set e : SchwartzBruhat X :=
    ⟨_, HarmonicAnalysis.indicator_one_mem_schwartzBruhatSubmodule L hLc hLo⟩
  have he : e ≠ 0 := fun h => by
    have := congrFun (congrArg Subtype.val h) 0
    change (L : Set X).indicator (fun _ => (1 : ℂ)) 0 = 0 at this
    rw [Set.indicator_of_mem (show (0 : X) ∈ (L : Set X) from L.zero_mem)] at this
    exact one_ne_zero this
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 := hTT e
    rw [zero_smul] at h1
    have h2 : T' e = 0 := standardOperator_injective hψ hψ1 g (h1.trans (map_zero T).symm)
    exact he (standardOperator_injective hψ hψ1 g⁻¹ (h2.trans (map_zero T').symm))
  intro φ
  refine ⟨c⁻¹ • T' φ, ?_⟩
  rw [map_smul, hTT, smul_smul, inv_mul_cancel₀ hc0, one_smul]

/-- `r(g)` as a linear automorphism of `S(X)`. -/
def standardOperatorEquiv (g : isometryGroup (polarizedForm β)) :
    SchwartzBruhat X ≃ₗ[ℂ] SchwartzBruhat X :=
  LinearEquiv.ofBijective (standardOperator hψ hψ1 g)
    ⟨standardOperator_injective hψ hψ1 g, standardOperator_surjective hψ hψ1 g⟩

@[simp] theorem standardOperatorEquiv_apply (g : isometryGroup (polarizedForm β))
    (φ : SchwartzBruhat X) : standardOperatorEquiv hψ hψ1 g φ = standardOperator hψ hψ1 g φ := rfl

/-- **The standard section** `s_r : g ↦ (g, r(g))` (GKT §2.3.1, p. 54, Definition 2.9): `(g, r(g))`
lies in the metaplectic group of pairs of the Schrödinger model. -/
def standardPair (g : isometryGroup (polarizedForm β)) :
    MetaplecticGroup (schrodingerModel (β := β) hψ) :=
  ⟨(g, standardOperatorEquiv hψ hψ1 g), fun h => standardOperator_comp hψ hψ1 g h⟩

@[simp] theorem proj_standardPair (g : isometryGroup (polarizedForm β)) :
    MetaplecticGroup.proj _ (standardPair hψ hψ1 g) = g := rfl

@[simp] theorem weil_standardPair (g : isometryGroup (polarizedForm β)) (φ : SchwartzBruhat X) :
    MetaplecticGroup.weil _ (standardPair hψ hψ1 g) φ = standardOperator hψ hψ1 g φ := rfl

/-- `(g, r(g))` lies in `Mp(W)^{ℂ¹}` (GKT p. 49, p. 54). -/
theorem standardPair_mem_unitary (g : isometryGroup (polarizedForm β)) (ν : Measure X)
    [ν.IsAddHaarMeasure] :
    standardPair hψ hψ1 g ∈ MetaplecticGroup.unitary _ (schwartzBruhatInner ν) :=
  fun f f' => standardOperator_inner hψ hψ1 g ν f f'

end Normalized

end Local

end Langlands.Theta
