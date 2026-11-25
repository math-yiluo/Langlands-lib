import Langlands.Theta.Metaplectic.SiegelParabolic
import Langlands.HarmonicAnalysis.Bicharacter.SelfDualMeasure

/-!
# The standard Weil operator at the Weyl element

GKT §2.3.3 (the elements `w_S` of a standard basis, (2.21), p. 61; **Proposition 2.24** and
**(2.24)**, pp. 63–64: the longest element `w_n` acts by the full Fourier transform; Lemma 2.25,
pp. 64–65: the measure is self-dual), for the standard Weil operator of
`Langlands.Theta.Metaplectic.StandardOperator`.

For a pairing `β : X →ₗ Y →ₗ F` and an isomorphism `J : Y ≃ X` for which `(y, y') ↦ β(J y, y')` is
symmetric (the datum of a standard basis: `J e_i = e^*_i`), the Weyl element is
`w_J (x, y) = (-J y, J⁻¹ x)` (`weylIsometry`; the book's `w_n = [[0, I], [-I, 0]]` with `I = J⁻¹`).

* `standardOperator_weylIsometry`: **`r(w_J) φ(x) = ∫_X ψ(-β(x, J⁻¹ u)) φ(u) du`** for the self-dual
  measure of the bicharacter `(x, u) ↦ ψ(-β(x, J⁻¹ u))` (the book's (2.24),
  `r(w_n) φ(y) = ∫_Y φ(z) ψ̄(⟨z, I y⟩) dz`);
* `map_standardMeasure_weylIsometry`: the measure `d_w` on `Y ⧸ ker c = Y ⧸ 0`, carried to `X` by
  `c = J`, is that self-dual measure (Proposition 2.24 with Lemma 2.25).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Langlands.Theta

open HeisenbergGroup Langlands.HarmonicAnalysis
open Langlands.LinearMap.BilinForm (isometryGroup)

universe u v w

section Group

variable {R : Type u} [CommRing R] {X : Type v} {Y : Type w} [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y] {β : X →ₗ[R] Y →ₗ[R] R}

variable (β) in
/-- **The Weyl element** `w_J (x, y) = (-J y, J⁻¹ x)` of the polarization `X × Y` of
`polarizedForm β`, for `J : Y ≃ X` with `β(J y, y') = β(J y', y)` (GKT (2.21) for `S` the whole
basis: `w(e_i) = -e^*_i`, `w(e^*_i) = e_i` with `e^*_i = J e_i`). -/
def weylIsometry (J : Y ≃ₗ[R] X) (hJ : ∀ y y', β (J y) y' = β (J y') y) :
    isometryGroup (polarizedForm β) :=
  ⟨{ toFun := fun w => (-J w.2, J.symm w.1)
     map_add' := fun w w' => by ext <;> simp [add_comm]
     map_smul' := fun c w => by ext <;> simp
     invFun := fun w => (J w.2, -J.symm w.1)
     left_inv := fun w => by ext <;> simp
     right_inv := fun w => by ext <;> simp },
   fun w w' => by
     change polarizedForm β (-J w.2, J.symm w.1) (-J w'.2, J.symm w'.1) = polarizedForm β w w'
     have h1 := hJ w.2 (J.symm w'.1)
     have h2 := hJ w'.2 (J.symm w.1)
     simp only [LinearEquiv.apply_symm_apply] at h1 h2
     simp only [polarizedForm_apply, map_neg, LinearMap.neg_apply, h1, h2]
     ring⟩

theorem weylIsometry_apply (J : Y ≃ₗ[R] X) (hJ : ∀ y y', β (J y) y' = β (J y') y) (w : X × Y) :
    (weylIsometry β J hJ : (X × Y) ≃ₗ[R] X × Y) w = (-J w.2, J.symm w.1) := rfl

theorem isometryInv_weylIsometry (J : Y ≃ₗ[R] X) (hJ : ∀ y y', β (J y) y' = β (J y') y)
    (w : X × Y) : isometryInv (weylIsometry β J hJ) w = (J w.2, -J.symm w.1) := rfl

/-- The c-part of `w_J⁻¹` is `J`. -/
theorem standardC_weylIsometry (J : Y ≃ₗ[R] X) (hJ : ∀ y y', β (J y) y' = β (J y') y) (y : Y) :
    standardC (weylIsometry β J hJ) y = J y := rfl

theorem standardKernel_weylIsometry (J : Y ≃ₗ[R] X) (hJ : ∀ y y', β (J y) y' = β (J y') y) :
    standardKernel (weylIsometry β J hJ) = ⊥ := by
  ext y
  simp only [mem_standardKernel, Submodule.mem_bot]
  exact J.map_eq_zero_iff

variable (β) in
/-- The symmetric form `(x, u) ↦ -β(x, J⁻¹ u)` of the Fourier transform at `w_J`. -/
def weylForm (J : Y ≃ₗ[R] X) : X →ₗ[R] X →ₗ[R] R :=
  -(β.compl₂ (J.symm : X →ₗ[R] Y))

theorem weylForm_apply (J : Y ≃ₗ[R] X) (x u : X) : weylForm β J x u = -β x (J.symm u) := rfl

theorem weylForm_symm (J : Y ≃ₗ[R] X) (hJ : ∀ y y', β (J y) y' = β (J y') y) (x u : X) :
    weylForm β J x u = weylForm β J u x := by
  have := hJ (J.symm x) (J.symm u)
  simp only [LinearEquiv.apply_symm_apply] at this
  rw [weylForm_apply, weylForm_apply, this]

end Group

section Local

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Invertible (2 : F)]
  {X : Type v} [AddCommGroup X] [Module F X] [FiniteDimensional F X] [TopologicalSpace X]
  [IsModuleTopology F X] [IsTopologicalAddGroup X]
  {Y : Type w} [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y] [TopologicalSpace Y]
  [IsModuleTopology F Y]
  {β : X →ₗ[F] Y →ₗ[F] F} {ψ : AddChar F ℂ}
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [β.IsPerfPair] (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)

/-- The bicharacter `(x, u) ↦ ψ(-β(x, J⁻¹ u))` of the Fourier transform at `w_J`. -/
def weylBicharacter (ψ : AddChar F ℂ) (β : X →ₗ[F] Y →ₗ[F] F) (J : Y ≃ₗ[F] X) : X → X → ℂ :=
  fun x u => ψ (weylForm β J x u)

omit [Invertible (2 : F)] [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace Y] [BorelSpace Y] [FiniteDimensional F Y] [TopologicalSpace Y]
  [IsModuleTopology F Y] in
include hψ hψ1 in
/-- `ψ ∘ weylForm` is a self-dual bicharacter of `X`. -/
theorem isSelfDualBicharacter_weylBicharacter (J : Y ≃ₗ[F] X)
    (hJ : ∀ y y', β (J y) y' = β (J y') y) :
    IsSelfDualBicharacter (weylBicharacter ψ β J) :=
  isSelfDualBicharacter_of_symm hψ (SchrodingerIrreducible.Internal.norm_addChar_eq_one hψ) hψ1
    (weylForm β J) (weylForm_symm J hJ) fun u hu => by
      have h : J.symm u = 0 := (LinearMap.IsPerfPair.bijective_right β).1
        (LinearMap.ext fun x => by simpa [weylForm_apply] using hu x)
      simpa using congrArg J h

omit [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]
  [BorelSpace Y] [β.IsPerfPair] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [FiniteDimensional F X] [TopologicalSpace X] [IsModuleTopology F X] [FiniteDimensional F Y]
  [TopologicalSpace Y] [IsModuleTopology F Y] in
/-- At `w_J` the integrand is `ψ(-β(x, y)) φ(J y) = ψ(-β(x, J⁻¹ (J y))) φ(J y)`. -/
theorem standardIntegrand_weylIsometry (J : Y ≃ₗ[F] X) (hJ : ∀ y y', β (J y) y' = β (J y') y)
    (φ : X → ℂ) (x : X) (y : Y) :
    standardIntegrand ψ (weylIsometry β J hJ) φ x y = weylBicharacter ψ β J x (J y) * φ (J y) := by
  have h := hJ y (J.symm x)
  simp only [LinearEquiv.apply_symm_apply] at h
  have h2 : (⅟2 : F) + ⅟2 = 1 := by rw [← two_mul, mul_invOf_self]
  rw [standardIntegrand, isometryInv_weylIsometry, weylBicharacter, weylForm_apply,
    LinearEquiv.symm_apply_apply]
  congr 2
  simp only [map_neg, h]
  linear_combination (-(β x y)) * h2

/-- **GKT (2.24) and Proposition 2.24 for the longest Weyl element**: `r(w_J)` is the Fourier
transform `φ ↦ (x ↦ ∫ ψ(-β(x, J⁻¹ u)) φ(u) du)` for the self-dual measure of this bicharacter. -/
theorem standardOperator_weylIsometry (J : Y ≃ₗ[F] X) (hJ : ∀ y y', β (J y) y' = β (J y') y)
    (φ : SchwartzBruhat X) (x : X) :
    (standardOperator hψ hψ1 (weylIsometry β J hJ) φ : X → ℂ) x =
      ∫ u, weylBicharacter ψ β J x u * (φ : X → ℂ) u
        ∂(selfDualMeasure (weylBicharacter ψ β J)) := by
  have := locallyCompactSpace_of_finiteDimensional F X
  have := secondCountableTopology_of_finiteDimensional F X
  have := compactOpenExhaustion_of_finiteDimensional F X
  have he := isSelfDualBicharacter_weylBicharacter hψ hψ1 J hJ
  have := isAddHaarMeasure_selfDualMeasure he
  set μsd := selfDualMeasure (weylBicharacter ψ β J)
  set T := bicharacterFourierSB μsd he
  have hT : ∀ (ν : Measure X) [ν.IsAddHaarMeasure] (f f' : SchwartzBruhat X),
      schwartzBruhatInner ν (T f) (T f') = schwartzBruhatInner ν f f' := by
    intro ν _ f f'
    have h0 : ∀ f f' : SchwartzBruhat X,
        schwartzBruhatInner μsd (T f) (T f') = 1 * schwartzBruhatInner μsd f f' := fun f f' => by
      rw [one_mul]
      exact schwartzBruhatInner_map μsd T
        (fun g => lintegral_enorm_bicharacterFourier_sq_selfDualMeasure he g.2) f f'
    rw [schwartzBruhatInner_map_of_haar T 1 μsd h0 ν f f', one_mul]
  set w := weylIsometry β J hJ
  set eq : (Y ⧸ standardKernel w) ≃ₗ[F] X :=
    (Submodule.quotEquivOfEqBot _ (standardKernel_weylIsometry J hJ)).trans J
  obtain ⟨s, hs, hmap⟩ := exists_map_eq_smul (standardMeasure hψ hψ1 w) μsd eq
  have hI : ∀ (f : SchwartzBruhat X) (x : X), standardIntegrandQ ψ w f x =
      fun q => weylBicharacter ψ β J x (eq q) * (f : X → ℂ) (eq q) := by
    intro f x
    funext q
    induction q using Submodule.Quotient.induction_on with | H y => ?_
    rw [standardIntegrandQ_mk, standardIntegrand_weylIsometry]
    rfl
  have hrel : standardOperator hψ hψ1 w = (s : ℂ) • T := by
    refine LinearMap.ext fun f => Subtype.ext (funext fun x => ?_)
    let E := (linearEquivToContinuousAddEquiv eq).toHomeomorph.toMeasurableEquiv
    change ∫ q, standardIntegrandQ ψ w f x q ∂(standardMeasure hψ hψ1 w) =
      (s : ℂ) * ∫ u, weylBicharacter ψ β J x u * (f : X → ℂ) u ∂μsd
    rw [hI]
    dsimp only
    have h3 : ∫ q, weylBicharacter ψ β J x (eq q) * (f : X → ℂ) (eq q)
        ∂(standardMeasure hψ hψ1 w) = ∫ u, weylBicharacter ψ β J x u * (f : X → ℂ) u
        ∂((standardMeasure hψ hψ1 w).map eq) :=
      (integral_map_equiv E (fun u => weylBicharacter ψ β J x u * (f : X → ℂ) u)).symm
    rw [h3, hmap, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have hEq := eq_of_eq_smul_of_inner (NNReal.coe_pos.2 hs) hrel Measure.addHaar
    (standardOperator_inner hψ hψ1 w Measure.addHaar) (hT Measure.addHaar)
  rw [hEq]
  rfl

end Local

end Langlands.Theta
