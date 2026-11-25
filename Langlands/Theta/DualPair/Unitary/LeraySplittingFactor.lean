import Langlands.Theta.DualPair.Unitary.StandardOperator
import Langlands.Theta.DualPair.Unitary.TypeI
import Langlands.Theta.Metaplectic.Transport
import Langlands.Theta.Metaplectic.RaoFunction

/-!
# The Leray splitting factor of `U(ν, ν)` on every Bruhat cell

GKT §11.2 (**(11.3)** and **Theorem 11.6**, p. 318; Corollary 11.7) in Case `3₊` with `W` split,
for the Weil representation `lerayWeil c ν ψ χ Q` of `U(ν, ν)` (the book's normalization `(⟪,⟫, ψ)`,
`Langlands.Theta.DualPair.Unitary.LeraySplitting`) and the standard Weil operator
`r(g ⊗ 1) = standardOperator … (toTraceIsometry g)` (GKT Definition 2.9).

* `leraySplittingFactor c ν ψ χ Q hc hQ : U(ν, ν) → Circle`, the function `β` of (11.3): the scalar
  with **`lerayWeil g = β(g) • r(g ⊗ 1)` for every `g`** (`lerayWeil_eq_leraySplittingFactor_smul`).
  It exists because both operators intertwine the Schrödinger model with its twist by `g ⊗ 1`
  (Schur's lemma, `MetaplecticGroup.exists_scalar_mul_eq`) and has absolute value `1` because both
  are unitary; it is unique because `r(g ⊗ 1) ≠ 0`. In the metaplectic group of pairs the Leray
  splitting is `g ↦ (g ⊗ 1, β(g) r(g ⊗ 1))` (`leraySplitting_eq_scalar_mul_standardPair`, the
  standard section `unitaryStandardPair` times the scalar `β(g)`).
* **Theorem 11.6 in cocycle form**: `standardOperator_comp_eq_leraySplittingFactor`,
  `r(g₁ ⊗ 1) r(g₂ ⊗ 1) = β(g₁ g₂) β(g₁)⁻¹ β(g₂)⁻¹ r(g₁ g₂ ⊗ 1)`; the scalar of the composition rule
  (`exists_standardOperator_comp`) is `β(g₁ g₂) β(g₁)⁻¹ β(g₂)⁻¹`
  (`eq_leraySplittingFactor_of_standardOperator_comp`).
* On the Siegel parabolic: `β(p₁ g p₂) = β(p₁) β(g) β(p₂)` (Proposition 2.17),
  `β(p) = χ(x(p))⁻¹` and `β(w) = γ(ψ_{1/2} ∘ Res_{E/F} V)^{|ν|}` (Proposition 12.29, in the
  normalization of `lerayWeil`).
* Blocks: for `σ : ν₁ ⊕ ν₂ ≃ ν`, `blockColsEquiv` splits `M_{α×ν}(E)` into column blocks, the image
  of `blockEmbedding c σ (g₁, g₂)` in the symplectic group is `diag(g₁ ⊗ 1, g₂ ⊗ 1)` carried along
  it (`toTraceIsometry_blockEmbedding`), and `β_ν(j(h, 1)) = β_{ν₁}(h)`
  (`leraySplittingFactor_blockEmbedding`): the quotient is a character of `U(ν₁, ν₁)` trivial on the
  Siegel parabolic, hence trivial (`UnitaryGroup.eq_one_of_siegelParabolic_le_ker`).
* **The cells**: `β(w_S) = γ^{|S|}` (`leraySplittingFactor_partialWeylElement`);
  `β(p₁ w_S p₂) = χ(x(p₁) x(p₂))⁻¹ γ^{|S|}` (`leraySplittingFactor_mul_partialWeylElement_mul`);
  with the Rao function of `Langlands.Theta.Metaplectic.RaoFunction` and `χ` on `Eˣ / 𝒩(Eˣ)`
  (`normQuotientCharacter`): `β(g) = χ(x(g))⁻¹ γ^{|S|}` on `P w_S P`
  (`leraySplittingFactor_eq_raoFunction`), and for every `g`,
  `β(g) = χ(x(g))⁻¹ γ^{|ν| - dim (X ∩ g X)}` (`leraySplittingFactor_eq`,
  `lerayWeil_eq_raoFunction_smul_standardOperator`).

`χ` enters as `χ⁻¹` because the Library's `lerayWeil` is the book's Leray splitting for the
character `χ^{book} = χ⁻¹` (`lerayWeil_eq_inv_smul_standardOperator_of_mem_siegelParabolic`).
-/

noncomputable section

open MeasureTheory Matrix

namespace Langlands.Theta

open Langlands.UnitaryGroup Langlands.HarmonicAnalysis Langlands.HeisenbergGroup
open Langlands.LinearMap.BilinForm (isometryGroup)

section Factor

variable {F : Type} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Invertible (2 : F)] {E : Type} [Field E] [Algebra F E]
  [TopologicalSpace E] [IsModuleTopology F E] [Algebra.IsQuadraticExtension F E]
  {c : E →ₐ[F] E} {δ : E} {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]
  {ψ : UnitaryAdditiveCharacter F} {χ : Eˣ →* Circle} {Q : Matrix α α E}
  [IsModuleTopology F (Matrix α ν E)] [IsTopologicalAddGroup (Matrix α ν E)]
  [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)]
  [(hermitianTracePairing (ν := ν) c Q).IsPerfPair]

omit [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Invertible (2 : F)] [TopologicalSpace E] [IsModuleTopology F E]
  [Algebra.IsQuadraticExtension F E] [DecidableEq α] [DecidableEq ν]
  [IsModuleTopology F (Matrix α ν E)] [IsTopologicalAddGroup (Matrix α ν E)]
  [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)]
  [(hermitianTracePairing (ν := ν) c Q).IsPerfPair] in
theorem finiteDimensional_matrix (hE : IsQuadraticInvolution c δ) :
    FiniteDimensional F (Matrix α ν E) := by
  have : FiniteDimensional F E := hE.finite
  infer_instance

/-- **`β` exists** (GKT Theorem 11.6, existence): `lerayWeil g` and `r(g ⊗ 1)` intertwine the
Schrödinger model with its twist by `g ⊗ 1`, so they differ by a scalar (Schur's lemma), of
absolute value `1` since both are unitary. -/
theorem exists_lerayWeil_eq_smul_standardOperator (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    (g : ofForm c (hyperbolicForm ν E)) :
    ∃ z : Circle, lerayWeil c ν ψ χ Q g = (z : ℂ) •
      standardOperator ψ.continuous_complex ψ.complex_ne_one
        (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ g) := by
  have := finiteDimensional_matrix (α := α) (ν := ν) hE
  have := locallyCompactSpace_of_finiteDimensional F (Matrix α ν E)
  have := compactOpenExhaustion_of_finiteDimensional F (Matrix α ν E)
  set ρ := hermitianTraceSchrodinger c ν Q ψ
  set x : MetaplecticGroup ρ := (leraySplitting (ψ := ψ) hE hQ hQu hχ hres).toMonoidHom g
  set y : MetaplecticGroup ρ := standardPair ψ.continuous_complex ψ.complex_ne_one
    (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ g)
  have hxy : MetaplecticGroup.proj ρ y = MetaplecticGroup.proj ρ x := by
    rw [show MetaplecticGroup.proj ρ x = _ from
      DFunLike.congr_fun (leraySplitting (ψ := ψ) hE hQ hQu hχ hres).proj_comp g]
    rfl
  obtain ⟨z, hz⟩ := MetaplecticGroup.exists_scalar_mul_eq (ρ := ρ)
    (isSmooth_schrodingerSB ψ.continuous_complex (continuous_hermitianTracePairing_left c Q))
    (isIrreducible_schrodingerSB ψ.continuous_complex ψ.complex_ne_one
      (continuous_hermitianTracePairing_left c Q)) hxy
  have hop : lerayWeil c ν ψ χ Q g = (z : ℂ) •
      standardOperator ψ.continuous_complex ψ.complex_ne_one
        (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ g) := LinearMap.ext fun φ => by
    have h := congrArg (fun k => MetaplecticGroup.weil ρ k φ) hz
    rw [map_mul, Module.End.mul_apply, MetaplecticGroup.weil_scalar] at h
    rw [← weil_leraySplitting hE hQ hQu hχ hres]
    exact h
  obtain ⟨e, he⟩ := exists_schwartzBruhatInner_ne_zero (Measure.addHaar : Measure (Matrix α ν E))
  have h1 := leraySplitting_mem_unitary (ψ := ψ) hE hQ hQu hχ hres Measure.addHaar g e e
  have h2 := standardOperator_inner ψ.continuous_complex ψ.complex_ne_one
    (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ g) Measure.addHaar e e
  change schwartzBruhatInner Measure.addHaar (lerayWeil c ν ψ χ Q g e)
    (lerayWeil c ν ψ χ Q g e) = _ at h1
  rw [hop] at h1
  simp only [LinearMap.smul_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    RingHom.id_apply, h2, ← mul_assoc, Complex.mul_conj'] at h1
  have h3 : ‖(z : ℂ)‖ = 1 := by
    have h4 : ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) = 1 := by
      have := mul_right_cancel₀ he (h1.trans (one_mul _).symm)
      exact_mod_cast this
    have h5 : ‖(z : ℂ)‖ ^ 2 = 1 ^ 2 := by rw [one_pow]; exact_mod_cast h4
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 h5
  exact ⟨⟨z, mem_sphere_zero_iff_norm.2 h3⟩, hop⟩

variable (c ν ψ χ Q) in
/-- **The Leray splitting factor** `β(g)` (GKT (11.3), the function `β^{V,χ}_{ψ,X}` of Theorem
11.6, Case `3₊` with `W` split): the scalar of absolute value `1` with
`lerayWeil g = β(g) • r(g ⊗ 1)` (`lerayWeil_eq_leraySplittingFactor_smul`); on the Bruhat cell
`P w_S P` it is `χ(x(g))⁻¹ γ^{|S|}` (`leraySplittingFactor_eq_of_mem_doubleCoset`). -/
def leraySplittingFactor (hc : Function.Involutive c) (hQ : Matrix.IsHermitianFor c Q)
    (g : ofForm c (hyperbolicForm ν E)) : Circle :=
  open Classical in
  if h : ∃ z : Circle, lerayWeil c ν ψ χ Q g = (z : ℂ) •
      standardOperator ψ.continuous_complex ψ.complex_ne_one
        (UnitaryGroup.toTraceIsometry (ν := ν) hc hQ g) then h.choose else 1

/-- **`lerayWeil g = β(g) • r(g ⊗ 1)`** for every `g ∈ U(ν, ν)` (GKT Theorem 11.6 and Corollary
11.7: the Leray splitting is `g ↦ (g ⊗ 1, β(g) r(g ⊗ 1))`). -/
theorem lerayWeil_eq_leraySplittingFactor_smul (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    (g : ofForm c (hyperbolicForm ν E)) :
    lerayWeil c ν ψ χ Q g = (leraySplittingFactor c ν ψ χ Q hE.involutive hQ g : ℂ) •
      standardOperator ψ.continuous_complex ψ.complex_ne_one
        (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ g) := by
  have h := exists_lerayWeil_eq_smul_standardOperator (ψ := ψ) hE hQ hQu hχ hres g
  rw [leraySplittingFactor, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

variable (ψ) in
/-- The standard section `s_r(g ⊗ 1) = (g ⊗ 1, r(g ⊗ 1))` (GKT Definition 2.9) of `U(ν, ν)`, in the
metaplectic group of pairs of the book's Schrödinger model `hermitianTraceSchrodinger c ν Q ψ`. -/
def unitaryStandardPair (hc : Function.Involutive c) (hQ : Matrix.IsHermitianFor c Q)
    (g : ofForm c (hyperbolicForm ν E)) : MetaplecticGroup (hermitianTraceSchrodinger c ν Q ψ) :=
  standardPair ψ.continuous_complex ψ.complex_ne_one (UnitaryGroup.toTraceIsometry (ν := ν) hc hQ g)

@[simp] theorem weil_unitaryStandardPair (hc : Function.Involutive c)
    (hQ : Matrix.IsHermitianFor c Q) (g : ofForm c (hyperbolicForm ν E))
    (φ : SchwartzBruhat (Matrix α ν E)) :
    MetaplecticGroup.weil _ (unitaryStandardPair ψ hc hQ g) φ =
      standardOperator ψ.continuous_complex ψ.complex_ne_one
        (UnitaryGroup.toTraceIsometry (ν := ν) hc hQ g) φ := rfl

/-- **The Leray splitting is `g ↦ (g ⊗ 1, β(g) r(g ⊗ 1))`** (GKT Theorem 11.6, Corollary 11.7): in
the metaplectic group of pairs, `leraySplitting g` is the scalar `β(g)` times the standard section
`standardPair (g ⊗ 1)`. -/
theorem leraySplitting_eq_scalar_mul_standardPair (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    (g : ofForm c (hyperbolicForm ν E)) :
    (leraySplitting (ψ := ψ) hE hQ hQu hχ hres).toMonoidHom g =
      MetaplecticGroup.scalar (hermitianTraceSchrodinger c ν Q ψ)
          (Units.mk0 (leraySplittingFactor c ν ψ χ Q hE.involutive hQ g : ℂ)
            (Circle.coe_ne_zero _)) *
        unitaryStandardPair ψ hE.involutive hQ g := by
  refine MetaplecticGroup.ext _ ?_ (LinearEquiv.ext fun φ => ?_)
  · have h1 := MetaplecticGroup.Splitting.proj_apply
      (leraySplitting (ψ := ψ) hE hQ hQu hχ hres) g
    have h2 : MetaplecticGroup.proj (hermitianTraceSchrodinger c ν Q ψ)
        (MetaplecticGroup.scalar _
          (Units.mk0 (leraySplittingFactor c ν ψ χ Q hE.involutive hQ g : ℂ)
            (Circle.coe_ne_zero _)) * unitaryStandardPair ψ hE.involutive hQ g) =
        UnitaryGroup.toTraceIsometry hE.involutive hQ g := by
      rw [map_mul, MetaplecticGroup.proj_scalar, one_mul]; rfl
    exact h1.trans h2.symm
  · change (leraySplitting (ψ := ψ) hE hQ hQu hχ hres).weil g φ =
      MetaplecticGroup.weil (hermitianTraceSchrodinger c ν Q ψ) (_ * _) φ
    rw [map_mul, Module.End.mul_apply, MetaplecticGroup.weil_scalar, weil_unitaryStandardPair,
      weil_leraySplitting, lerayWeil_eq_leraySplittingFactor_smul hE hQ hQu hχ hres g]
    rfl

/-- `r(g ⊗ 1) ≠ 0`. -/
theorem standardOperator_toTraceIsometry_ne_zero (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (g : ofForm c (hyperbolicForm ν E)) :
    standardOperator ψ.continuous_complex ψ.complex_ne_one
      (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ g) ≠ 0 := by
  have := finiteDimensional_matrix (α := α) (ν := ν) hE
  obtain ⟨φ, hφ⟩ := exists_schwartzBruhat_ne_zero (α := α) (ν := ν) hE
  intro h0
  apply hφ
  apply standardOperator_injective ψ.continuous_complex ψ.complex_ne_one
    (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ g)
  rw [h0, map_zero, LinearMap.zero_apply]

private theorem eq_of_smul_standardOperator (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (g : ofForm c (hyperbolicForm ν E)) {z z' : ℂ}
    (h : z • standardOperator ψ.continuous_complex ψ.complex_ne_one
      (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ g) =
      z' • standardOperator ψ.continuous_complex ψ.complex_ne_one
        (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ g)) : z = z' := by
  have hr := standardOperator_toTraceIsometry_ne_zero (ψ := ψ) hE hQ g
  obtain ⟨φ, hφ⟩ : ∃ φ, standardOperator ψ.continuous_complex ψ.complex_ne_one
      (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ g) φ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hr (LinearMap.ext hc)
  obtain ⟨x, hx⟩ : ∃ x, (standardOperator ψ.continuous_complex ψ.complex_ne_one
      (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ g) φ : Matrix α ν E → ℂ) x ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hφ (Subtype.ext (funext hc))
  have := congrArg (fun T : SchwartzBruhat (Matrix α ν E) →ₗ[ℂ] SchwartzBruhat (Matrix α ν E) =>
    ((T φ : SchwartzBruhat (Matrix α ν E)) : Matrix α ν E → ℂ) x) h
  simp only [LinearMap.smul_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hx this

/-- **`β` is unique**: if `lerayWeil g = z • r(g ⊗ 1)`, then `z = β(g)`. -/
theorem leraySplittingFactor_eq_of_lerayWeil_eq (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    {g : ofForm c (hyperbolicForm ν E)} {z : ℂ}
    (h : lerayWeil c ν ψ χ Q g = z • standardOperator ψ.continuous_complex ψ.complex_ne_one
      (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ g)) :
    (leraySplittingFactor c ν ψ χ Q hE.involutive hQ g : ℂ) = z :=
  eq_of_smul_standardOperator hE hQ g
    ((lerayWeil_eq_leraySplittingFactor_smul hE hQ hQu hχ hres g).symm.trans h)

/-- **GKT Theorem 11.6 in cocycle form** (Case `3₊`, `W` split): the composition rule of the
standard Weil operators at `(g₁ ⊗ 1, g₂ ⊗ 1)` has the scalar `β(g₁ g₂) β(g₁)⁻¹ β(g₂)⁻¹`, i.e. the
Leray cocycle restricted to `U(ν, ν)` is the coboundary of `β`. -/
theorem standardOperator_comp_eq_leraySplittingFactor (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    (g₁ g₂ : ofForm c (hyperbolicForm ν E)) :
    standardOperator ψ.continuous_complex ψ.complex_ne_one
        (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ g₁) ∘ₗ
      standardOperator ψ.continuous_complex ψ.complex_ne_one
        (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ g₂) =
      ((leraySplittingFactor c ν ψ χ Q hE.involutive hQ (g₁ * g₂) *
          (leraySplittingFactor c ν ψ χ Q hE.involutive hQ g₁)⁻¹ *
          (leraySplittingFactor c ν ψ χ Q hE.involutive hQ g₂)⁻¹ : Circle) : ℂ) •
        standardOperator ψ.continuous_complex ψ.complex_ne_one
          (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ g₁ *
            UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ g₂) := by
  set b := leraySplittingFactor c ν ψ χ Q hE.involutive hQ
  set r := fun g : ofForm c (hyperbolicForm ν E) => standardOperator ψ.continuous_complex
    ψ.complex_ne_one (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ g)
  have h12 := lerayWeil_eq_leraySplittingFactor_smul (ψ := ψ) hE hQ hQu hχ hres (g₁ * g₂)
  rw [map_mul, lerayWeil_eq_leraySplittingFactor_smul hE hQ hQu hχ hres g₁,
    lerayWeil_eq_leraySplittingFactor_smul hE hQ hQu hχ hres g₂, smul_mul_smul_comm] at h12
  rw [← map_mul (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ)]
  change r g₁ * r g₂ = _ • r (g₁ * g₂)
  have hb1 : (b g₁ : ℂ) * b g₂ ≠ 0 := mul_ne_zero (Circle.coe_ne_zero _) (Circle.coe_ne_zero _)
  rw [Circle.coe_mul, Circle.coe_mul, Circle.coe_inv, Circle.coe_inv,
    show (b (g₁ * g₂) : ℂ) * (b g₁ : ℂ)⁻¹ * (b g₂ : ℂ)⁻¹ = ((b g₁ : ℂ) * b g₂)⁻¹ * b (g₁ * g₂) by
      ring, mul_smul, ← h12, smul_smul, inv_mul_cancel₀ hb1, one_smul]

/-- **The scalar of the composition rule** (`exists_standardOperator_comp`) at `(g₁ ⊗ 1, g₂ ⊗ 1)`
is `β(g₁ g₂) β(g₁)⁻¹ β(g₂)⁻¹` (GKT Theorem 11.6). -/
theorem eq_leraySplittingFactor_of_standardOperator_comp (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    {g₁ g₂ : ofForm c (hyperbolicForm ν E)} {z : ℂ}
    (h : standardOperator ψ.continuous_complex ψ.complex_ne_one
        (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ g₁) ∘ₗ
      standardOperator ψ.continuous_complex ψ.complex_ne_one
        (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ g₂) =
      z • standardOperator ψ.continuous_complex ψ.complex_ne_one
          (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ g₁ *
            UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ g₂)) :
    z = ((leraySplittingFactor c ν ψ χ Q hE.involutive hQ (g₁ * g₂) *
        (leraySplittingFactor c ν ψ χ Q hE.involutive hQ g₁)⁻¹ *
        (leraySplittingFactor c ν ψ χ Q hE.involutive hQ g₂)⁻¹ : Circle) : ℂ) := by
  rw [standardOperator_comp_eq_leraySplittingFactor hE hQ hQu hχ hres,
    ← map_mul (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ)] at h
  exact eq_of_smul_standardOperator hE hQ (g₁ * g₂) h.symm

/-- **`β(p₁ g p₂) = β(p₁) β(g) β(p₂)`** for `p₁`, `p₂` in the Siegel parabolic (from GKT Proposition
2.17, `r(p₁ g p₂) = r(p₁) r(g) r(p₂)`). -/
theorem leraySplittingFactor_mul_mul_of_mem (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    {p₁ p₂ : ofForm c (hyperbolicForm ν E)} (hp₁ : p₁ ∈ siegelParabolic c ν)
    (hp₂ : p₂ ∈ siegelParabolic c ν) (g : ofForm c (hyperbolicForm ν E)) :
    leraySplittingFactor c ν ψ χ Q hE.involutive hQ (p₁ * g * p₂) =
      leraySplittingFactor c ν ψ χ Q hE.involutive hQ p₁ *
        leraySplittingFactor c ν ψ χ Q hE.involutive hQ g *
        leraySplittingFactor c ν ψ χ Q hE.involutive hQ p₂ := by
  set ι := UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ
  apply Circle.coe_injective
  refine leraySplittingFactor_eq_of_lerayWeil_eq hE hQ hQu hχ hres ?_
  have hr : standardOperator ψ.continuous_complex ψ.complex_ne_one (ι (p₁ * g * p₂)) =
      standardOperator ψ.continuous_complex ψ.complex_ne_one (ι p₁) ∘ₗ
        standardOperator ψ.continuous_complex ψ.complex_ne_one (ι g) ∘ₗ
        standardOperator ψ.continuous_complex ψ.complex_ne_one (ι p₂) := by
    rw [map_mul, map_mul]
    exact standardOperator_mul_mul_of_mem ψ.continuous_complex ψ.complex_ne_one _
      (toTraceIsometry_mem_siegelParabolicGroup hE.involutive hQ hp₁)
      (toTraceIsometry_mem_siegelParabolicGroup hE.involutive hQ hp₂)
  rw [hr, map_mul, map_mul, lerayWeil_eq_leraySplittingFactor_smul hE hQ hQu hχ hres p₁,
    lerayWeil_eq_leraySplittingFactor_smul hE hQ hQu hχ hres g,
    lerayWeil_eq_leraySplittingFactor_smul hE hQ hQu hχ hres p₂, smul_mul_smul_comm,
    smul_mul_smul_comm, Circle.coe_mul, Circle.coe_mul]
  rfl

/-- **`β` on the Siegel parabolic** (GKT Proposition 12.29): `β(p) = χ(x(p))⁻¹`,
`x(p) = det_E(p|_X)` the Rao value (`siegelParabolicRaoValue`). -/
theorem leraySplittingFactor_of_mem_siegelParabolic (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    {p : ofForm c (hyperbolicForm ν E)} (hp : p ∈ siegelParabolic c ν) :
    leraySplittingFactor c ν ψ χ Q hE.involutive hQ p = (χ (siegelParabolicRaoValue hp))⁻¹ :=
  Circle.coe_injective (leraySplittingFactor_eq_of_lerayWeil_eq hE hQ hQu hχ hres
    (lerayWeil_eq_inv_smul_standardOperator_of_mem_siegelParabolic hE hQ hQu hχ hres hp))

/-- **`β` at the Weyl element** (GKT Proposition 12.29, Case `3₊`): `β(w) = γ(ψ_{1/2} ∘ Res_{E/F}
V)^{|ν|}`. -/
theorem leraySplittingFactor_weylElement (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α) :
    (leraySplittingFactor c ν ψ χ Q hE.involutive hQ (weylElement c ν) : ℂ) =
      weilIndex (fun v : α → E => (ψ.scale (twoUnit F)⁻¹).complex (hermitianTraceForm c Q v v)) ^
        Fintype.card ν :=
  leraySplittingFactor_eq_of_lerayWeil_eq hE hQ hQu hχ hres
    (lerayWeil_weylElement_eq_smul_standardOperator hE hQ hQu hχ hres)

end Factor

/-! ### Block embeddings -/

section BlockAlgebra

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] {c : E →ₐ[F] E}
  {α ν ν₁ ν₂ : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν] [Fintype ν₁]
  [DecidableEq ν₁] [Fintype ν₂] [DecidableEq ν₂] {Q : Matrix α α E} (σ : ν₁ ⊕ ν₂ ≃ ν)

variable (F α E) in
/-- The columns of `ν₁` and of `ν₂`: `M_{α×ν₁}(E) × M_{α×ν₂}(E) ≃ M_{α×ν}(E)` along `σ`. -/
def blockColsEquiv : (Matrix α ν₁ E × Matrix α ν₂ E) ≃ₗ[F] Matrix α ν E where
  toFun x := Matrix.of fun i k => Sum.elim (x.1 i) (x.2 i) (σ.symm k)
  invFun x := (Matrix.of fun i k => x i (σ (.inl k)), Matrix.of fun i k => x i (σ (.inr k)))
  map_add' x y := by
    ext i k
    rcases hk : σ.symm k with k' | k' <;> simp [hk]
  map_smul' a x := by
    ext i k
    rcases hk : σ.symm k with k' | k' <;> simp [hk]
  left_inv x := by
    ext i k <;> simp
  right_inv x := by
    ext i k
    rcases hk : σ.symm k with k' | k' <;>
      (rw [σ.symm_apply_eq] at hk; subst hk; simp)

omit [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν] [Fintype ν₁] [DecidableEq ν₁]
  [Fintype ν₂] [DecidableEq ν₂] in
theorem blockColsEquiv_apply (x : Matrix α ν₁ E × Matrix α ν₂ E) (i : α) (k : ν) :
    blockColsEquiv F E α σ x i k = Sum.elim (x.1 i) (x.2 i) (σ.symm k) := rfl

omit [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν] [Fintype ν₁] [DecidableEq ν₁]
  [Fintype ν₂] [DecidableEq ν₂] in
/-- `fromCols` of two block-column matrices, in the coordinates of `blockIndexEquiv`. -/
theorem fromCols_blockColsEquiv (x y : Matrix α ν₁ E × Matrix α ν₂ E) :
    fromCols (blockColsEquiv F E α σ x) (blockColsEquiv F E α σ y) =
      (fromCols (fromCols x.1 y.1) (fromCols x.2 y.2)).submatrix id (blockIndexEquiv σ) := by
  ext i (k | k) <;> rcases hk : σ.symm k with k' | k' <;>
    simp [blockColsEquiv_apply, blockIndexEquiv, hk]

omit [Fintype α] [DecidableEq α] [DecidableEq ν] [DecidableEq ν₁] [DecidableEq ν₂] in
theorem blockColsEquiv_mul_transpose_map (x y : Matrix α ν₁ E × Matrix α ν₂ E) :
    blockColsEquiv F E α σ x * ((blockColsEquiv F E α σ y).map c)ᵀ =
      x.1 * (y.1.map c)ᵀ + x.2 * (y.2.map c)ᵀ := by
  ext i j
  simp only [mul_apply, transpose_apply, map_apply, blockColsEquiv_apply, Matrix.add_apply]
  rw [σ.symm.sum_comp (fun k => Sum.elim (x.1 i) (x.2 i) k * c (Sum.elim (y.1 j) (y.2 j) k)),
    Fintype.sum_sum_type]
  simp

omit [DecidableEq ν] [DecidableEq ν₁] [DecidableEq ν₂] in
/-- **The pairing of `M_{α×ν}(E)` is the sum of the pairings of the column blocks.** -/
theorem hermitianTracePairing_blockColsEquiv [NeZero (2 : F)]
    (x y : Matrix α ν₁ E × Matrix α ν₂ E) :
    hermitianTracePairing c Q (blockColsEquiv F E α σ x) (blockColsEquiv F E α σ y) =
      sumPairing (hermitianTracePairing c Q) (hermitianTracePairing c Q) x y := by
  rw [sumPairing_apply, hermitianTracePairing_apply, hermitianTracePairing_apply,
    hermitianTracePairing_apply, blockColsEquiv_mul_transpose_map, Matrix.mul_add, trace_add,
    map_add]

/-- **`U(ν₁, ν₁) × U(ν₂, ν₂) ⊆ U(ν, ν)` on `𝕎`**: the image of `blockEmbedding c σ (g₁, g₂)` in
the symplectic group of `M_{α×ν}(E)²` is `diag(g₁ ⊗ 1, g₂ ⊗ 1)` (`blockDiag`) carried along
`blockColsEquiv`. -/
theorem toTraceIsometry_blockEmbedding [NeZero (2 : F)] (hc : Function.Involutive c)
    (hQ : Matrix.IsHermitianFor c Q)
    (g : ofForm c (hyperbolicForm ν₁ E) × ofForm c (hyperbolicForm ν₂ E)) :
    UnitaryGroup.toTraceIsometry (ν := ν) hc hQ (blockEmbedding c σ g) =
      isometryGroupCongr (blockColsEquiv F E α σ) (blockColsEquiv F E α σ)
        (hermitianTracePairing_blockColsEquiv σ)
        (blockDiag (hermitianTracePairing c Q) (hermitianTracePairing c Q)
          (UnitaryGroup.toTraceIsometry hc hQ g.1, UnitaryGroup.toTraceIsometry hc hQ g.2)) := by
  refine Subtype.ext (LinearEquiv.ext fun w' => ?_)
  obtain ⟨w, rfl⟩ := ((blockColsEquiv F E α σ).prodCongr (blockColsEquiv F E α σ)).surjective w'
  rw [isometryGroupCongr_apply]
  have hinv : (((blockEmbedding c σ g)⁻¹ : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) =
      (blockMatrix σ (((g.1⁻¹ : ofForm c (hyperbolicForm ν₁ E)) : GL (ν₁ ⊕ ν₁) E) :
        Matrix (ν₁ ⊕ ν₁) (ν₁ ⊕ ν₁) E) (((g.2⁻¹ : ofForm c (hyperbolicForm ν₂ E)) :
          GL (ν₂ ⊕ ν₂) E) : Matrix (ν₂ ⊕ ν₂) (ν₂ ⊕ ν₂) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) := by
    rw [← map_inv, Prod.inv_mk]; rfl
  change UnitaryGroup.rightMulInvEquiv c (blockEmbedding c σ g) _ = _
  rw [UnitaryGroup.rightMulInvEquiv_apply, LinearEquiv.prodCongr_apply, blockDiag_apply,
    blockDiagEquiv_apply, LinearEquiv.prodCongr_apply]
  simp only [UnitaryGroup.toTraceIsometry_apply, UnitaryGroup.rightMulInvEquiv_apply]
  have key : ∀ p q : Matrix α ν E × Matrix α ν E, fromCols p.1 p.2 = fromCols q.1 q.2 → p = q :=
    fun p q h => Prod.ext (fromCols_inj h).1 (fromCols_inj h).2
  apply key
  simp only [fromCols_toCols, fromCols_blockColsEquiv, hinv, blockMatrix, submatrix_mul_equiv,
    fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero, zero_add]

omit [DecidableEq α] in
/-- The Rao value of an embedded block: `x(j(p₁, p₂)) = x(p₁) x(p₂)`. -/
theorem siegelParabolicRaoValue_blockEmbedding
    {p : ofForm c (hyperbolicForm ν₁ E) × ofForm c (hyperbolicForm ν₂ E)}
    (h₁ : p.1 ∈ siegelParabolic c ν₁) (h₂ : p.2 ∈ siegelParabolic c ν₂) :
    siegelParabolicRaoValue (blockEmbedding_mem_siegelParabolic c σ h₁ h₂) =
      siegelParabolicRaoValue h₁ * siegelParabolicRaoValue h₂ := by
  refine Units.ext ?_
  have hinv : Unitary.Internal.mat c (blockEmbedding c σ p)⁻¹ =
      blockMatrix σ (Unitary.Internal.mat c p.1⁻¹) (Unitary.Internal.mat c p.2⁻¹) := by
    rw [← map_inv]; rfl
  rw [Units.val_mul, siegelParabolicRaoValue, siegelParabolicRaoValue, siegelParabolicRaoValue,
    Units.val_mk0, Units.val_mk0, Units.val_mk0, hinv, det_toBlocks₂₂_blockMatrix]

end BlockAlgebra

/-! ### Characters of `U(ν, ν)` trivial on the Siegel parabolic -/

section Character

variable {F : Type} [Field F] [Infinite F] {E : Type} [Field E] [Algebra F E] {c : E →ₐ[F] E}
  {δ : E} {ν : Type} [Fintype ν] [DecidableEq ν]

open Unitary.Internal in
/-- **A homomorphism of `U(ν, ν)` that is trivial on the Siegel parabolic is trivial**: from the
relation `w n(1) w = p₀ w n(-1)` of the big cell, `f(w)² = f(w)`; then `P` and `w` generate. -/
theorem _root_.Langlands.UnitaryGroup.eq_one_of_siegelParabolic_le_ker
    (hE : IsQuadraticInvolution c δ) {G : Type*} [Group G] (f : ofForm c (hyperbolicForm ν E) →* G)
    (hf : siegelParabolic c ν ≤ f.ker) : f = 1 := by
  have h1 : ((1 : Matrix ν ν E).map c)ᵀ = 1 := by
    rw [Matrix.map_one _ (map_zero c) (map_one c), transpose_one]
  have h1' := WeylCellRel.herm_neg_inv c (1 : Matrix ν ν E) h1 (by simp)
  set w := weylElement c ν
  set n := siegelUnipotent c (1 : Matrix ν ν E) h1
  set n' := siegelUnipotent c (-(1 : Matrix ν ν E)⁻¹) h1'
  set p₀ := w * n * w * n'⁻¹ * w⁻¹
  have hp₀ : p₀ ∈ siegelParabolic c ν := by
    rw [mem_sieg, WeylCellRel.splitUnitaryElementMatrix_bigCell_product c 1 h1 (by simp) h1']
    simp
  have hn : n ∈ siegelParabolic c ν := by rw [mem_sieg, WeylCellRel.mat_unip]; simp
  have hn' : n' ∈ siegelParabolic c ν := by rw [mem_sieg, WeylCellRel.mat_unip]; simp
  have hrel : w * n * w = p₀ * w * n' := by simp only [p₀]; group
  have hw : f w = 1 := by
    have := congrArg f hrel
    rw [map_mul, map_mul, map_mul, map_mul, (MonoidHom.mem_ker).1 (hf hn),
      (MonoidHom.mem_ker).1 (hf hn'), (MonoidHom.mem_ker).1 (hf hp₀), mul_one, mul_one,
      one_mul] at this
    exact mul_eq_left.1 this
  have htop := eq_top_of_siegelParabolic_le_of_weylElement_mem hE hf ((MonoidHom.mem_ker).2 hw)
  exact MonoidHom.ext fun g => (MonoidHom.mem_ker).1 (htop ▸ Subgroup.mem_top g)

end Character

/-! ### `β` on embedded blocks -/

section BlockFactor

variable {F : Type} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Invertible (2 : F)] {E : Type} [Field E] [Algebra F E]
  [TopologicalSpace E] [IsModuleTopology F E] [Algebra.IsQuadraticExtension F E]
  {c : E →ₐ[F] E} {δ : E} {α ν ν₁ ν₂ : Type} [Fintype α] [DecidableEq α] [Fintype ν]
  [DecidableEq ν] [Fintype ν₁] [DecidableEq ν₁] [Fintype ν₂] [DecidableEq ν₂]
  {ψ : UnitaryAdditiveCharacter F} {χ : Eˣ →* Circle} {Q : Matrix α α E}
  [IsModuleTopology F (Matrix α ν E)] [IsTopologicalAddGroup (Matrix α ν E)]
  [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)]
  [(hermitianTracePairing (ν := ν) c Q).IsPerfPair]
  [IsModuleTopology F (Matrix α ν₁ E)] [IsTopologicalAddGroup (Matrix α ν₁ E)]
  [MeasurableSpace (Matrix α ν₁ E)] [BorelSpace (Matrix α ν₁ E)]
  [(hermitianTracePairing (ν := ν₁) c Q).IsPerfPair] [SecondCountableTopology (Matrix α ν₁ E)]
  [IsModuleTopology F (Matrix α ν₂ E)] [IsTopologicalAddGroup (Matrix α ν₂ E)]
  [MeasurableSpace (Matrix α ν₂ E)] [BorelSpace (Matrix α ν₂ E)]
  [(hermitianTracePairing (ν := ν₂) c Q).IsPerfPair]
  (σ : ν₁ ⊕ ν₂ ≃ ν)

omit [IsModuleTopology F E] in
/-- **The composition scalars on an embedded block**: the scalar of the composition rule at
`(j(g, 1), j(g', 1))` in `U(ν, ν)` is that at `(g, g')` in `U(ν₁, ν₁)` (GKT Corollary 2.29,
carried along `blockColsEquiv`). -/
theorem standardOperator_comp_blockEmbedding (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (g g' : ofForm c (hyperbolicForm ν₁ E)) {z : ℂ}
    (h : standardOperator ψ.continuous_complex ψ.complex_ne_one
        (UnitaryGroup.toTraceIsometry (ν := ν₁) hE.involutive hQ g) ∘ₗ
      standardOperator ψ.continuous_complex ψ.complex_ne_one
        (UnitaryGroup.toTraceIsometry (ν := ν₁) hE.involutive hQ g') =
      z • standardOperator ψ.continuous_complex ψ.complex_ne_one
          (UnitaryGroup.toTraceIsometry (ν := ν₁) hE.involutive hQ g *
            UnitaryGroup.toTraceIsometry (ν := ν₁) hE.involutive hQ g')) :
    standardOperator ψ.continuous_complex ψ.complex_ne_one
        (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ (blockEmbedding c σ (g, 1))) ∘ₗ
      standardOperator ψ.continuous_complex ψ.complex_ne_one
        (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ (blockEmbedding c σ (g', 1))) =
      z • standardOperator ψ.continuous_complex ψ.complex_ne_one
          (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ (blockEmbedding c σ (g, 1)) *
            UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ
              (blockEmbedding c σ (g', 1))) := by
  have := finiteDimensional_matrix (α := α) (ν := ν₁) hE
  have := finiteDimensional_matrix (α := α) (ν := ν₂) hE
  have := finiteDimensional_matrix (α := α) (ν := ν) hE
  have h₂ : standardOperator ψ.continuous_complex ψ.complex_ne_one
      (1 : isometryGroup (polarizedForm (hermitianTracePairing (ν := ν₂) c Q))) ∘ₗ
      standardOperator ψ.continuous_complex ψ.complex_ne_one
        (1 : isometryGroup (polarizedForm (hermitianTracePairing (ν := ν₂) c Q))) =
      (1 : ℂ) • standardOperator ψ.continuous_complex ψ.complex_ne_one
        (1 * 1 : isometryGroup (polarizedForm (hermitianTracePairing (ν := ν₂) c Q))) := by
    rw [one_smul, mul_one, standardOperator_one, LinearMap.id_comp]
  have hb := standardOperator_blockDiag_comp ψ.continuous_complex ψ.complex_ne_one
    (β₁ := hermitianTracePairing (ν := ν₁) c Q) (β₂ := hermitianTracePairing (ν := ν₂) c Q)
    (UnitaryGroup.toTraceIsometry hE.involutive hQ g, 1)
    (UnitaryGroup.toTraceIsometry hE.involutive hQ g', 1) h h₂
  rw [mul_one] at hb
  have ht := standardOperator_comp_isometryGroupCongr (blockColsEquiv F E α σ)
    (blockColsEquiv F E α σ) (hermitianTracePairing_blockColsEquiv σ) ψ.continuous_complex
    ψ.complex_ne_one hb
  rw [toTraceIsometry_blockEmbedding, toTraceIsometry_blockEmbedding, ← map_mul, ← map_mul]
  rw [← map_mul] at ht
  simpa only [map_one] using ht

/-- **`β` on an embedded block** (`U(ν₁, ν₁) ⊆ U(ν, ν)` along `σ : ν₁ ⊕ ν₂ ≃ ν`):
`β_ν(j(h, 1)) = β_{ν₁}(h)`. The quotient `h ↦ β_ν(j(h, 1)) β_{ν₁}(h)⁻¹` is a character of
`U(ν₁, ν₁)` (the composition scalars agree, `standardOperator_comp_blockEmbedding`), trivial on the
Siegel parabolic (both are `χ(x(p))⁻¹` and `x(j(p, 1)) = x(p)`), hence trivial
(`UnitaryGroup.eq_one_of_siegelParabolic_le_ker`). -/
theorem leraySplittingFactor_blockEmbedding (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    (h : ofForm c (hyperbolicForm ν₁ E)) :
    leraySplittingFactor c ν ψ χ Q hE.involutive hQ (blockEmbedding c σ (h, 1)) =
      leraySplittingFactor c ν₁ ψ χ Q hE.involutive hQ h := by
  have : Infinite F := Infinite.of_injective _ Nat.cast_injective
  set β := leraySplittingFactor c ν ψ χ Q hE.involutive hQ
  set β₁ := leraySplittingFactor c ν₁ ψ χ Q hE.involutive hQ
  have hmul : ∀ g g' : ofForm c (hyperbolicForm ν₁ E),
      β (blockEmbedding c σ (g * g', 1)) * (β₁ (g * g'))⁻¹ =
        β (blockEmbedding c σ (g, 1)) * (β₁ g)⁻¹ *
          (β (blockEmbedding c σ (g', 1)) * (β₁ g')⁻¹) := by
    intro g g'
    have h₁ := standardOperator_comp_eq_leraySplittingFactor (ν := ν₁) (ψ := ψ) hE hQ hQu hχ hres
      g g'
    have hb := standardOperator_comp_blockEmbedding σ hE hQ g g' h₁
    have hc := eq_leraySplittingFactor_of_standardOperator_comp hE hQ hQu hχ hres hb
    rw [← map_mul, Prod.mk_mul_mk, mul_one] at hc
    apply Circle.coe_injective
    simp only [Circle.coe_mul, Circle.coe_inv] at hc ⊢
    have n1 : (β₁ g : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have n2 : (β₁ g' : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have n3 : (β₁ (g * g') : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have n4 : (β (blockEmbedding c σ (g, 1)) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have n5 : (β (blockEmbedding c σ (g', 1)) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    field_simp at hc ⊢
    linear_combination -hc
  let d : ofForm c (hyperbolicForm ν₁ E) →* Circle :=
    MonoidHom.mk' (fun g => β (blockEmbedding c σ (g, 1)) * (β₁ g)⁻¹) hmul
  have hP : siegelParabolic c ν₁ ≤ d.ker := by
    intro p hp
    have h₂ : (1 : ofForm c (hyperbolicForm ν₂ E)) ∈ siegelParabolic c ν₂ :=
      (siegelParabolic c ν₂).one_mem
    rw [MonoidHom.mem_ker]
    change β (blockEmbedding c σ (p, 1)) * (β₁ p)⁻¹ = 1
    simp only [β, β₁]
    rw [leraySplittingFactor_of_mem_siegelParabolic hE hQ hQu hχ hres
      (blockEmbedding_mem_siegelParabolic c σ (h := (p, 1)) hp h₂),
      siegelParabolicRaoValue_blockEmbedding σ (p := (p, 1)) hp h₂,
      leraySplittingFactor_of_mem_siegelParabolic hE hQ hQu hχ hres hp]
    have hx1 : siegelParabolicRaoValue h₂ = 1 := Units.ext (by
      have e : (1 : Matrix (ν₂ ⊕ ν₂) (ν₂ ⊕ ν₂) E).toBlocks₂₂ = 1 := by
        ext i j; simp [toBlocks₂₂, one_apply]
      rw [siegelParabolicRaoValue, Units.val_mk0, Units.val_one, inv_one]
      change (1 : Matrix (ν₂ ⊕ ν₂) (ν₂ ⊕ ν₂) E).toBlocks₂₂.det = 1
      rw [e, det_one])
    rw [hx1, mul_one, mul_inv_cancel]
  have hd := UnitaryGroup.eq_one_of_siegelParabolic_le_ker hE d hP
  have := DFunLike.congr_fun hd h
  change β (blockEmbedding c σ (h, 1)) * (β₁ h)⁻¹ = 1 at this
  exact mul_inv_eq_one.1 this

end BlockFactor

section NormQuotient

variable {F : Type} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type} [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {c : E →ₐ[F] E} {δ : E} {α : Type} [Fintype α]
  {χ : Eˣ →* Circle}

variable (χ) in
/-- A character `χ` with `χ|_{Fˣ} = η^{|α|}` is trivial on the norms `a c(a)`. -/
theorem normSubgroup_le_ker (hE : IsQuadraticInvolution c δ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α) :
    RingInvo.normSubgroup (UnitaryGroup.ringInvo c hE.involutive) ≤ χ.ker := by
  rintro _ ⟨a, rfl⟩
  have h := hres (Units.map (Algebra.norm F : E →* F) a)
  rw [LocalClassField.normResidueSign_norm, Units.val_one, Int.cast_one, one_pow] at h
  have e : RingInvo.normHom (UnitaryGroup.ringInvo c hE.involutive) a =
      Units.map (algebraMap F E : F →* E) (Units.map (Algebra.norm F : E →* F) a) :=
    Units.ext (by
      rw [RingInvo.coe_normHom, UnitaryGroup.conj_ringInvo]
      exact (hE.algebraMap_norm (a : E)).symm)
  rw [MonoidHom.mem_ker, e]
  exact Circle.coe_eq_one.1 h

variable (χ) in
/-- **`χ` on `Eˣ / 𝒩_{E/F}(Eˣ)`** (the values of the Rao function): the character `χ`, trivial on
norms by (11.2) (`normSubgroup_le_ker`), descended to the quotient. -/
def normQuotientCharacter (hE : IsQuadraticInvolution c δ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α) :
    Eˣ ⧸ RingInvo.normSubgroup (UnitaryGroup.ringInvo c hE.involutive) →* Circle :=
  QuotientGroup.lift _ χ (normSubgroup_le_ker χ hE hres)

@[simp] theorem normQuotientCharacter_mk (hE : IsQuadraticInvolution c δ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α) (a : Eˣ) :
    normQuotientCharacter χ hE hres (QuotientGroup.mk a) = χ a := rfl

end NormQuotient

/-! ### `β` on the Bruhat cells -/

section Cells

variable {F : Type} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Invertible (2 : F)] {E : Type} [Field E] [Algebra F E]
  [TopologicalSpace E] [IsModuleTopology F E] [Algebra.IsQuadraticExtension F E]
  {c : E →ₐ[F] E} {δ : E} {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]
  {ψ : UnitaryAdditiveCharacter F} {χ : Eˣ →* Circle} {Q : Matrix α α E}
  [IsModuleTopology F (Matrix α ν E)] [IsTopologicalAddGroup (Matrix α ν E)]
  [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)]
  [(hermitianTracePairing (ν := ν) c Q).IsPerfPair]

/-- **`β` at the Weyl element `w_S`** (GKT (11.3), Case `3₊`): `β(w_S) = γ(ψ_{1/2} ∘ Res_{E/F}
V)^{|S|}`. The element `w_S` is the Weyl element of `U(S, S)` embedded in `U(ν, ν)`
(`partialWeylElement_eq_blockEmbedding`), and `β` is compatible with the embedding
(`leraySplittingFactor_blockEmbedding`). -/
theorem leraySplittingFactor_partialWeylElement (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    (S : Finset ν) :
    (leraySplittingFactor c ν ψ χ Q hE.involutive hQ (UnitaryGroup.partialWeylElement c S) : ℂ) =
      weilIndex (fun v : α → E => (ψ.scale (twoUnit F)⁻¹).complex (hermitianTraceForm c Q v v)) ^
        S.card := by
  have : FiniteDimensional F E := hE.finite
  let _ : IsModuleTopology F (Matrix α {i // i ∈ S} E) := isModuleTopology_matrix F α _
  have : IsTopologicalAddGroup (Matrix α {i // i ∈ S} E) :=
    IsModuleTopology.isTopologicalAddGroup F _
  let _ : MeasurableSpace (Matrix α {i // i ∈ S} E) := borel _
  have : BorelSpace (Matrix α {i // i ∈ S} E) := ⟨rfl⟩
  have : (hermitianTracePairing (ν := {i // i ∈ S}) c Q).IsPerfPair :=
    isPerfPair_hermitianTracePairing hE hQ hQu
  have : SecondCountableTopology (Matrix α {i // i ∈ S} E) :=
    secondCountableTopology_of_finiteDimensional F _
  let _ : IsModuleTopology F (Matrix α {i // i ∉ S} E) := isModuleTopology_matrix F α _
  have : IsTopologicalAddGroup (Matrix α {i // i ∉ S} E) :=
    IsModuleTopology.isTopologicalAddGroup F _
  let _ : MeasurableSpace (Matrix α {i // i ∉ S} E) := borel _
  have : BorelSpace (Matrix α {i // i ∉ S} E) := ⟨rfl⟩
  have : (hermitianTracePairing (ν := {i // i ∉ S}) c Q).IsPerfPair :=
    isPerfPair_hermitianTracePairing hE hQ hQu
  rw [UnitaryGroup.partialWeylElement_eq_blockEmbedding,
    leraySplittingFactor_blockEmbedding _ hE hQ hQu hχ hres,
    leraySplittingFactor_weylElement hE hQ hQu hχ hres, Fintype.card_coe]

/-- **`β` on the cell `P w_S P`** (GKT (11.3), Case `3₊`, `W` split): for `g = p₁ w_S p₂` with
`p₁`, `p₂` in the Siegel parabolic, `β(g) = χ(x(p₁) x(p₂))⁻¹ γ(ψ_{1/2} ∘ Res_{E/F} V)^{|S|}`, where
`x(p) = det_E(p|_X)` (`siegelParabolicRaoValue`). -/
theorem leraySplittingFactor_mul_partialWeylElement_mul (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    {p₁ p₂ : ofForm c (hyperbolicForm ν E)} (hp₁ : p₁ ∈ siegelParabolic c ν)
    (hp₂ : p₂ ∈ siegelParabolic c ν) (S : Finset ν) :
    (leraySplittingFactor c ν ψ χ Q hE.involutive hQ
        (p₁ * UnitaryGroup.partialWeylElement c S * p₂) : ℂ) =
      (((χ (siegelParabolicRaoValue hp₁ * siegelParabolicRaoValue hp₂))⁻¹ : Circle) : ℂ) *
        weilIndex (fun v : α → E => (ψ.scale (twoUnit F)⁻¹).complex
          (hermitianTraceForm c Q v v)) ^ S.card := by
  rw [leraySplittingFactor_mul_mul_of_mem hE hQ hQu hχ hres hp₁ hp₂, Circle.coe_mul,
    Circle.coe_mul, leraySplittingFactor_partialWeylElement hE hQ hQu hχ hres,
    leraySplittingFactor_of_mem_siegelParabolic hE hQ hQu hχ hres hp₁,
    leraySplittingFactor_of_mem_siegelParabolic hE hQ hQu hχ hres hp₂, map_mul, mul_inv,
    Circle.coe_mul]
  ring

omit [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Invertible (2 : F)] [TopologicalSpace E] [IsModuleTopology F E]
  [Algebra.IsQuadraticExtension F E] [Fintype α] [DecidableEq α]
  [IsModuleTopology F (Matrix α ν E)] [IsTopologicalAddGroup (Matrix α ν E)]
  [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)]
  [(hermitianTracePairing (ν := ν) c Q).IsPerfPair] in
/-- **The Rao value is the determinant of `p|_X`** (GKT (4.15)): for `p` in the Siegel parabolic,
`siegelDet` of its image in `U(W)` is `siegelParabolicRaoValue p`. -/
theorem siegelDet_toIsometryGroup {p : ofForm c (hyperbolicForm ν E)}
    (hp : p ∈ siegelParabolic c ν) (hc : Function.Involutive c) :
    (hyperbolicHermitianForm c hc ν).siegelDet (hyperbolicStandardBasis c hc ν).lagrangianFst
        ⟨toIsometryGroup c hc p, (toIsometryGroup_mem_siegelParabolic_iff c hc).2 hp⟩ =
      siegelParabolicRaoValue hp :=
  Units.ext (by
    rw [EpsilonHermitianForm.coe_siegelDet, siegelParabolicRaoValue, Units.val_mk0]
    exact det_restrictLagrangianFst c hc hp)

/-- **`β` on the Bruhat cells, through the Rao function** (GKT (11.3), Case `3₊`, `W` split, in
the normalization of `lerayWeil`): if the image of `g` in `U(W)` lies in the cell `P w_S P` of
the standard basis `eᵢ = (0, εᵢ)`, `eᵢ* = -(εᵢ, 0)`, then
`β(g) = χ(x(g))⁻¹ γ(ψ_{1/2} ∘ Res_{E/F} V)^{|S|}`, with `x(g)` the Rao function
(`StandardBasis.raoFunction`, GKT Definition 4.37) and `χ` read on `Eˣ / 𝒩(Eˣ)`. -/
theorem leraySplittingFactor_eq_raoFunction [NeZero (2 : E)] (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    (g : ofForm c (hyperbolicForm ν E)) (S : Finset ν)
    (hg : ∃ p₁ ∈ (hyperbolicHermitianForm c hE.involutive ν).siegelParabolic
        (hyperbolicStandardBasis c hE.involutive ν).lagrangianFst,
      ∃ p₂ ∈ (hyperbolicHermitianForm c hE.involutive ν).siegelParabolic
        (hyperbolicStandardBasis c hE.involutive ν).lagrangianFst,
      toIsometryGroup c hE.involutive g =
        p₁ * (hyperbolicStandardBasis c hE.involutive ν).weylElement S * p₂) :
    (leraySplittingFactor c ν ψ χ Q hE.involutive hQ g : ℂ) =
      (((normQuotientCharacter χ hE hres ((hyperbolicStandardBasis c hE.involutive ν).raoFunction
          (toIsometryGroup c hE.involutive g)))⁻¹ : Circle) : ℂ) *
        weilIndex (fun v : α → E => (ψ.scale (twoUnit F)⁻¹).complex
          (hermitianTraceForm c Q v v)) ^ S.card := by
  obtain ⟨p₁, hp₁, p₂, hp₂, hg⟩ := hg
  obtain ⟨q₁, rfl⟩ := (toIsometryGroup c hE.involutive).surjective p₁
  obtain ⟨q₂, rfl⟩ := (toIsometryGroup c hE.involutive).surjective p₂
  have hq₁ := (toIsometryGroup_mem_siegelParabolic_iff c hE.involutive).1 hp₁
  have hq₂ := (toIsometryGroup_mem_siegelParabolic_iff c hE.involutive).1 hp₂
  rw [EpsilonHermitianForm.StandardBasis.raoFunction_eq _ S ⟨_, hp₁⟩ ⟨_, hp₂⟩ hg,
    normQuotientCharacter_mk, siegelDet_toIsometryGroup hq₁, siegelDet_toIsometryGroup hq₂]
  have hgq : g = q₁ * UnitaryGroup.partialWeylElement c S * q₂ :=
    (toIsometryGroup c hE.involutive).injective (by
      rw [map_mul, map_mul, toIsometryGroup_partialWeylElement, hg])
  subst hgq
  exact leraySplittingFactor_mul_partialWeylElement_mul hE hQ hQu hχ hres hq₁ hq₂ S

/-- **The function `β` of GKT (11.3) on all of `U(ν, ν)`** (Case `3₊`, `W` split):
`β(g) = χ(x(g))⁻¹ γ(ψ_{1/2} ∘ Res_{E/F} V)^{s(g)}`, `s(g) = |ν| - dim (X ∩ g X)` the index of the
Bruhat cell of `g` (GKT §4.4.2) and `x(g)` the Rao function. -/
theorem leraySplittingFactor_eq [NeZero (2 : E)] (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    (g : ofForm c (hyperbolicForm ν E)) :
    (leraySplittingFactor c ν ψ χ Q hE.involutive hQ g : ℂ) =
      (((normQuotientCharacter χ hE hres ((hyperbolicStandardBasis c hE.involutive ν).raoFunction
          (toIsometryGroup c hE.involutive g)))⁻¹ : Circle) : ℂ) *
        weilIndex (fun v : α → E => (ψ.scale (twoUnit F)⁻¹).complex
          (hermitianTraceForm c Q v v)) ^ (Fintype.card ν - Module.finrank E
            ((hyperbolicStandardBasis c hE.involutive ν).lagrangianFst ⊓
              (hyperbolicStandardBasis c hE.involutive ν).lagrangianFst.map
                ((toIsometryGroup c hE.involutive g :
                  (hyperbolicHermitianForm c hE.involutive ν).isometryGroup) :
                    (ν ⊕ ν → E) ≃ₗ[E] (ν ⊕ ν → E)).toLinearMap : Submodule E (ν ⊕ ν → E))) := by
  obtain ⟨S, hS⟩ := (hyperbolicStandardBasis c hE.involutive ν).exists_mem_doubleCoset
    (toIsometryGroup c hE.involutive g)
  have hcard := ((hyperbolicStandardBasis c hE.involutive ν).mem_doubleCoset_weylElement_iff S
    (toIsometryGroup c hE.involutive g)).1 hS
  rw [leraySplittingFactor_eq_raoFunction hE hQ hQu hχ hres g S hS,
    show S.card = Fintype.card ν - _ from (Nat.sub_eq_of_eq_add' hcard.symm).symm]

/-- **The Leray splitting on every Bruhat cell** (GKT Theorem 11.6, (11.3) and Corollary 11.7 in
Case `3₊`, `W` split): for every `g ∈ U(ν, ν)`,
`lerayWeil g = χ(x(g))⁻¹ γ(ψ_{1/2} ∘ Res_{E/F} V)^{s(g)} • r(g ⊗ 1)`. -/
theorem lerayWeil_eq_raoFunction_smul_standardOperator [NeZero (2 : E)]
    (hE : IsQuadraticInvolution c δ) (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det)
    (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    (g : ofForm c (hyperbolicForm ν E)) :
    lerayWeil c ν ψ χ Q g =
      ((((normQuotientCharacter χ hE hres ((hyperbolicStandardBasis c hE.involutive ν).raoFunction
          (toIsometryGroup c hE.involutive g)))⁻¹ : Circle) : ℂ) *
        weilIndex (fun v : α → E => (ψ.scale (twoUnit F)⁻¹).complex
          (hermitianTraceForm c Q v v)) ^ (Fintype.card ν - Module.finrank E
            ((hyperbolicStandardBasis c hE.involutive ν).lagrangianFst ⊓
              (hyperbolicStandardBasis c hE.involutive ν).lagrangianFst.map
                ((toIsometryGroup c hE.involutive g :
                  (hyperbolicHermitianForm c hE.involutive ν).isometryGroup) :
                    (ν ⊕ ν → E) ≃ₗ[E] (ν ⊕ ν → E)).toLinearMap : Submodule E (ν ⊕ ν → E)))) •
        standardOperator ψ.continuous_complex ψ.complex_ne_one
          (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ g) := by
  rw [← leraySplittingFactor_eq hE hQ hQu hχ hres g]
  exact lerayWeil_eq_leraySplittingFactor_smul hE hQ hQu hχ hres g

end Cells

end Langlands.Theta
