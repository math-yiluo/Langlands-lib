import Langlands.Automorphic.UnitaryCharacterPairing
import Langlands.Global.AdelicLocalWavePacketStatement
import Langlands.Global.AdelicSplitCenterHaar
import Langlands.Global.AdelicRestrictionSplitCentreCanonical
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # Sesquilinearity of the induced inner product `(·,·)_P`

Proof of `InducedInnerProductSesquilinearStatement` (premise (D) of the reduction of Lapid 2011,
Lemma 10). The integrand `β(y(m)) δ_P(m)⁻¹ φ(m k) conj ψ(m k)` of `(φ, ψ)_P` is shown to be
integrable on `K × M(F) \ M(𝔸)` for `φ, ψ ∈ A^2_P`; Fubini then gives sesquilinearity.

Integrability: on the fundamental domain `A × D¹` of `M(F)` in `M(𝔸) = A × M(𝔸)¹` (`A` the
positive points of the canonical split component of `M`, `D¹` the chosen fundamental domain of
`M(F)` in `M(𝔸)¹`), `|β(y(a n)) δ_P(a n)⁻¹ φ(a n k)²| = |β(y(a))| δ_P(n)⁻¹ |φ(n k)|²`, so the
integral over `M(F) \ M(𝔸)` is `c · ∫_A |β(y(a))| da · ∫_{[M]} δ_P⁻¹ |φ|²`, where `μ_M = c · haar`.
The first factor is finite since the Levi projection `π` makes `a ↦ y(a)` an injective linear map
in logarithmic coordinates, so `a ↦ β(y(a))` has compact support; the second is the `A^2_P`
condition. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct ENNReal NNReal
open Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.InducedInnerProductSesquilinear

section Abstract

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {κ : Measure α} {ν : Measure β} [SFinite κ] [SFinite ν]

/-- Iterated integrals of a finite linear combination of functions integrable for the
product measure split into the linear combination of the iterated integrals. -/
theorem integral_integral_sum_sum {k : ℕ} (I : Fin k → Fin k → α → β → ℂ)
    (hI : ∀ j j', Integrable (fun q : α × β => I j j' q.1 q.2) (κ.prod ν))
    (c : Fin k → Fin k → ℂ) :
    ∫ a, ∫ b, ∑ j, ∑ j', c j j' * I j j' a b ∂ν ∂κ =
      ∑ j, ∑ j', c j j' * ∫ a, ∫ b, I j j' a b ∂ν ∂κ := by
  have hae : ∀ᵐ a ∂κ, ∀ j j', Integrable (fun b => I j j' a b) ν := by
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro j'
    exact (hI j j').prod_right_ae
  have h1 : ∀ᵐ a ∂κ, ∫ b, ∑ j, ∑ j', c j j' * I j j' a b ∂ν =
      ∑ j, ∑ j', c j j' * ∫ b, I j j' a b ∂ν := by
    filter_upwards [hae] with a ha
    rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _
      (fun j' _ => (ha j j').const_mul (c j j')))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_finsetSum _ (fun j' _ => (ha j j').const_mul (c j j'))]
    exact Finset.sum_congr rfl (fun j' _ => integral_const_mul _ _)
  rw [integral_congr_ae h1, integral_finsetSum _ (fun j _ => integrable_finsetSum _
    (fun j' _ => (hI j j').integral_prod_left.const_mul (c j j')))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_finsetSum _ (fun j' _ => (hI j j').integral_prod_left.const_mul (c j j'))]
  exact Finset.sum_congr rfl (fun j' _ => integral_const_mul _ _)

end Abstract

section Descent

variable {X H E : Type*} [TopologicalSpace X] [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H] [TopologicalSpace E] (Γ : Subgroup H)

omit [TopologicalSpace H] [IsTopologicalGroup H] in
/-- The chosen representative of the coset of `m` is a left `Γ`-translate of `m`. -/
theorem out_mk_eq_mul (m : H) :
    ∃ g₀ ∈ Γ, (LeftCosetSpace.mk Γ m).out = g₀ * m := by
  have h : LeftCosetSpace.mk Γ m = LeftCosetSpace.mk Γ (LeftCosetSpace.mk Γ m).out :=
    (Quotient.out_eq _).symm
  rw [LeftCosetSpace.mk_eq_mk_iff] at h
  exact ⟨_, h, by group⟩

/-- A continuous function on `X × H`, left `Γ`-invariant in the second variable, evaluated at
the chosen representatives, is continuous on `X × Γ \ H`. -/
theorem continuous_prod_out (f : X × H → E) (hf : Continuous f)
    (hinv : ∀ x, ∀ g₀ ∈ Γ, ∀ m, f (x, g₀ * m) = f (x, m)) :
    Continuous (fun q : X × LeftCosetSpace Γ => f (q.1, q.2.out)) := by
  have hq : IsQuotientMap (Prod.map (id : X → X) (LeftCosetSpace.mk Γ)) :=
    (IsOpenQuotientMap.id.prodMap (LeftCosetSpace.isOpenQuotientMap_mk Γ)).isQuotientMap
  rw [hq.continuous_iff]
  convert hf using 1
  funext q
  obtain ⟨g₀, hg₀, h⟩ := out_mk_eq_mul Γ q.2
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id]
  rw [h, hinv q.1 g₀ hg₀ q.2]

/-- A continuous left `Γ`-invariant function, evaluated at the chosen representatives, is
continuous on `Γ \ H`. -/
theorem continuous_out (f : H → E) (hf : Continuous f)
    (hinv : ∀ g₀ ∈ Γ, ∀ m, f (g₀ * m) = f m) :
    Continuous (fun x : LeftCosetSpace Γ => f x.out) := by
  rw [(LeftCosetSpace.isQuotientMap_mk Γ).continuous_iff]
  convert hf using 1
  funext m
  obtain ⟨g₀, hg₀, h⟩ := out_mk_eq_mul Γ m
  simp only [Function.comp_apply]
  rw [h, hinv g₀ hg₀ m]

omit [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace E] in
/-- Evaluation at chosen representatives of a left `Γ`-invariant function. -/
theorem out_mk_apply (f : H → E) (hinv : ∀ g₀ ∈ Γ, ∀ m, f (g₀ * m) = f m) (m : H) :
    f (LeftCosetSpace.mk Γ m).out = f m := by
  obtain ⟨g₀, hg₀, h⟩ := out_mk_eq_mul Γ m
  rw [h, hinv g₀ hg₀ m]

end Descent

section Stabilizer

variable {H E : Type*} [Group H]

end Stabilizer

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
  Langlands.Global.AdelicGroupPoints

section Parameters

variable (F : Type) [Field F] (P : GroupScheme (Spec (CommRingCat.of F)))

theorem continuous_realParameterPairing (μ₀ : RealCharacterParameter F P) :
    Continuous (realParameterPairing F P μ₀) := by
  induction μ₀ using TensorProduct.inductionOn with
  | tmul t χ =>
    have h : ⇑(realParameterPairing F P (t ⊗ₜ[ℤ] χ)) = fun H => t * H χ := by
      funext H
      rfl
    rw [h]
    exact continuous_const.mul (continuous_dualEval F P χ)
  | add x y hx hy =>
    have h : ⇑(realParameterPairing F P (x + y)) =
        fun H => realParameterPairing F P x H + realParameterPairing F P y H := by
      funext H
      simp
    rw [h]
    exact hx.add hy

theorem continuous_complexParameterPairing (lam : ComplexCharacterParameter F P) :
    Continuous (complexParameterPairing F P lam) := by
  induction lam using TensorProduct.inductionOn with
  | tmul t χ =>
    have h : ⇑(complexParameterPairing F P (t ⊗ₜ[ℤ] χ)) = fun H => t * (H χ : ℂ) := by
      funext H
      rfl
    rw [h]
    exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_dualEval F P χ))
  | add x y hx hy =>
    have h : ⇑(complexParameterPairing F P (x + y)) =
        fun H => complexParameterPairing F P x H + complexParameterPairing F P y H := by
      funext H
      simp
    rw [h]
    exact hx.add hy

variable [NumberField F]

theorem continuous_parameterCoordinates {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) :
    Continuous (parameterCoordinates F P e) :=
  continuous_pi fun _ => continuous_realParameterPairing F P _

theorem continuous_parameterPower (lam : ComplexCharacterParameter F P) :
    Continuous (parameterPower F P lam) :=
  Complex.continuous_exp.comp
    ((continuous_complexParameterPairing F P lam).comp (continuous_characterLog F P))

theorem parameterPower_mul (lam : ComplexCharacterParameter F P)
    (x y : AdelicGroupPoints F P) :
    parameterPower F P lam (x * y) = parameterPower F P lam x * parameterPower F P lam y := by
  simp [parameterPower, characterLog_mul, Complex.exp_add]

variable [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]

/-- `|δ_P(x)⁻¹| |x^{ρ_P}|² = 1`. -/
theorem norm_modulus_mul_sq (x : AdelicGroupPoints F P) :
    ‖parameterPower F P (-modulusParameter F P) x‖ *
      ‖parameterPower F P (halfModulusParameter F P) x‖ ^ 2 = 1 := by
  simp only [parameterPower, modulusParameter, halfModulusParameter, Complex.norm_exp, map_neg,
    LinearMap.neg_apply, complexParameterPairing_tmul]
  rw [sq, ← Real.exp_add, ← Real.exp_add]
  convert Real.exp_zero using 2
  simp
  ring

end Parameters

section Kernel

variable {F : Type} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  (p : P ⟶ G) (l : M ⟶ P) {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
  (β : (Fin n → ℝ) → ℝ)

/-- The weight `β(y(m)) δ_P(m)⁻¹` of the integrand of `(·,·)_P`. -/
def weight (m : AdelicGroupPoints F M) : ℂ :=
  (β (parameterCoordinates F P e (characterLog F P (map F M P l m))) : ℂ) *
    parameterPower F P (-modulusParameter F P) (map F M P l m)

/-- The integrand `β(y(m)) δ_P(m)⁻¹ φ(m g) conj ψ(m g)` of `(φ, ψ)_P`. -/
def kernel (φ ψ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G)
    (m : AdelicGroupPoints F M) : ℂ :=
  weight l e β m * φ (map F P G p (map F M P l m) * g) *
    (starRingEnd ℂ) (ψ (map F P G p (map F M P l m) * g))

/-- The integrand `δ_P(m)⁻¹ |φ(m g)|²` of the `A^2_P` condition. -/
def normWeight (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G)
    (m : AdelicGroupPoints F M) : ℝ :=
  ‖parameterPower F P (-modulusParameter F P) (map F M P l m)‖ *
    ‖φ (map F P G p (map F M P l m) * g)‖ ^ 2

omit [LocallyOfFiniteType G.X.hom] in
theorem inducedInnerProduct_eq_kernel (K : Subgroup (AdelicGroupPoints F G))
    (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) (μM : Measure (AdelicGroupPoints F M))
    (φ ψ : AdelicGroupPoints F G → ℂ) :
    inducedInnerProduct K hKc p l μM e β φ ψ =
      ∫ k : K, ∫ x : RationalQuotient F M, kernel p l e β φ ψ k x.out
        ∂(LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
          (isDiscrete_rationalSubgroup F M) μM)
        ∂(compactHaarProbability F G K hKc) :=
  rfl

theorem kernel_sum {k : ℕ} (v : Fin k → AdelicGroupPoints F G → ℂ) (z z' : Fin k → ℂ)
    (g : AdelicGroupPoints F G) (m : AdelicGroupPoints F M) :
    kernel p l e β (fun x => ∑ j, z j * v j x) (fun x => ∑ j, z' j * v j x) g m =
      ∑ j, ∑ j', z j * (starRingEnd ℂ) (z' j') * kernel p l e β (v j) (v j') g m := by
  simp only [kernel, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  ring

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
  [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] in
theorem map_comp_apply (x : AdelicGroupPoints F M) :
    map F M G (l ≫ p) x = map F P G p (map F M P l x) := by
  simp [map_apply, Category.assoc]

theorem characterLog_map_normOne {x : AdelicGroupPoints F M} (hx : x ∈ normOneSubgroup F M) :
    characterLog F P (map F M P l x) = 0 := by
  rw [characterLog_map, (characterLog_eq_zero_iff F M x).mpr hx, map_zero]

theorem characterLog_map_normOne_mul {x : AdelicGroupPoints F M}
    (hx : x ∈ normOneSubgroup F M) (m : AdelicGroupPoints F M) :
    characterLog F P (map F M P l (x * m)) = characterLog F P (map F M P l m) := by
  rw [map_mul, characterLog_mul, characterLog_map_normOne l hx, zero_add]

theorem characterLog_map_mul_normOne {x : AdelicGroupPoints F M}
    (hx : x ∈ normOneSubgroup F M) (m : AdelicGroupPoints F M) :
    characterLog F P (map F M P l (m * x)) = characterLog F P (map F M P l m) := by
  rw [map_mul, characterLog_mul, characterLog_map_normOne l hx, add_zero]

theorem weight_normOne_mul {x : AdelicGroupPoints F M} (hx : x ∈ normOneSubgroup F M)
    (m : AdelicGroupPoints F M) : weight l e β (x * m) = weight l e β m := by
  simp only [weight, parameterPower, characterLog_map_normOne_mul l hx]

theorem mem_parabolicLeviRationalImage {x : AdelicGroupPoints F M}
    (hx : x ∈ rationalSubgroup F M) :
    map F P G p (map F M P l x) ∈ parabolicLeviRationalImage F p l := by
  obtain ⟨q, rfl⟩ := hx
  exact ⟨q, map_comp_apply p l _⟩

variable {p l}

theorem kernel_rational_mul {φ ψ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicLeviRationalImage F p l) φ)
    (hψ : IsLeftInvariantUnder F G (parabolicLeviRationalImage F p l) ψ)
    {x : AdelicGroupPoints F M} (hx : x ∈ rationalSubgroup F M)
    (g : AdelicGroupPoints F G) (m : AdelicGroupPoints F M) :
    kernel p l e β φ ψ g (x * m) = kernel p l e β φ ψ g m := by
  have hpt : map F P G p (map F M P l (x * m)) * g =
      map F P G p (map F M P l x) * (map F P G p (map F M P l m) * g) := by
    rw [map_mul, map_mul, mul_assoc]
  simp only [kernel, weight_normOne_mul l e β (rationalSubgroup_le_normOneSubgroup F M hx), hpt,
    hφ _ (mem_parabolicLeviRationalImage p l hx), hψ _ (mem_parabolicLeviRationalImage p l hx)]

theorem normWeight_rational_mul {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicLeviRationalImage F p l) φ)
    {x : AdelicGroupPoints F M} (hx : x ∈ rationalSubgroup F M)
    (g : AdelicGroupPoints F G) (m : AdelicGroupPoints F M) :
    normWeight p l φ g (x * m) = normWeight p l φ g m := by
  have hpt : map F P G p (map F M P l (x * m)) * g =
      map F P G p (map F M P l x) * (map F P G p (map F M P l m) * g) := by
    rw [map_mul, map_mul, mul_assoc]
  simp only [normWeight, parameterPower,
    characterLog_map_normOne_mul l (rationalSubgroup_le_normOneSubgroup F M hx), hpt,
    hφ _ (mem_parabolicLeviRationalImage p l hx)]

theorem normWeight_splitComponent_mul {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSplitComponentEquivariant p l φ)
    {a : AdelicGroupPoints F M} (ha : a ∈ RestrictionSplitCentre.canonicalSubgroup F M)
    (g : AdelicGroupPoints F G) (m : AdelicGroupPoints F M) :
    normWeight p l φ g (a * m) = normWeight p l φ g m := by
  have hpt : map F P G p (map F M P l (a * m)) * g =
      map F P G p (map F M P l a) * (map F P G p (map F M P l m) * g) := by
    rw [map_mul, map_mul, mul_assoc]
  have h1 := norm_modulus_mul_sq F P (map F M P l a)
  rw [normWeight, normWeight, hpt, hφ a ha, map_mul (map F M P l) a m, parameterPower_mul,
    norm_mul, norm_mul, mul_pow]
  linear_combination (‖parameterPower F P (-modulusParameter F P) (map F M P l m)‖ *
    ‖φ (map F P G p (map F M P l m) * g)‖ ^ 2) * h1

variable (p l)

theorem continuous_weight (hβ : Continuous β) : Continuous (weight l e β) :=
  (Complex.continuous_ofReal.comp (hβ.comp ((continuous_parameterCoordinates F P e).comp
    ((continuous_characterLog F P).comp (map F M P l).continuous)))).mul
    ((continuous_parameterPower F P _).comp (map F M P l).continuous)

theorem continuous_point {X : Type*} [TopologicalSpace X] {ξ : X → AdelicGroupPoints F G}
    {τ : X → AdelicGroupPoints F M} (hξ : Continuous ξ) (hτ : Continuous τ) :
    Continuous (fun x => map F P G p (map F M P l (τ x)) * ξ x) :=
  (((map F P G p).continuous.comp (map F M P l).continuous).comp hτ).mul hξ

theorem continuous_kernel {X : Type*} [TopologicalSpace X] {ξ : X → AdelicGroupPoints F G}
    {τ : X → AdelicGroupPoints F M} (hξ : Continuous ξ) (hτ : Continuous τ)
    (hβ : Continuous β) {φ ψ : AdelicGroupPoints F G → ℂ}
    (hφ : Continuous φ) (hψ : Continuous ψ) :
    Continuous (fun x => kernel p l e β φ ψ (ξ x) (τ x)) :=
  (((continuous_weight l e β hβ).comp hτ).mul (hφ.comp (continuous_point p l hξ hτ))).mul
    (Complex.continuous_conj.comp (hψ.comp (continuous_point p l hξ hτ)))

theorem continuous_normWeight {X : Type*} [TopologicalSpace X] {ξ : X → AdelicGroupPoints F G}
    {τ : X → AdelicGroupPoints F M} (hξ : Continuous ξ) (hτ : Continuous τ)
    {φ : AdelicGroupPoints F G → ℂ} (hφ : Continuous φ) :
    Continuous (fun x => normWeight p l φ (ξ x) (τ x)) :=
  ((continuous_parameterPower F P _).comp ((map F M P l).continuous.comp hτ)).norm.mul
    ((hφ.comp (continuous_point p l hξ hτ)).norm.pow 2)

theorem norm_kernel_le (φ ψ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G)
    (m : AdelicGroupPoints F M) :
    ‖kernel p l e β φ ψ g m‖ ≤ ‖kernel p l e β φ φ g m‖ + ‖kernel p l e β ψ ψ g m‖ := by
  simp only [kernel, norm_mul, Complex.norm_conj]
  have hw := norm_nonneg (weight l e β m)
  have ha := norm_nonneg (φ (map F P G p (map F M P l m) * g))
  have hb := norm_nonneg (ψ (map F P G p (map F M P l m) * g))
  nlinarith [mul_nonneg hw (sq_nonneg (‖φ (map F P G p (map F M P l m) * g)‖ -
    ‖ψ (map F P G p (map F M P l m) * g)‖)), mul_nonneg hw (mul_nonneg ha hb)]

theorem norm_kernel_self (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G)
    (m : AdelicGroupPoints F M) :
    ‖kernel p l e β φ φ g m‖ =
      |β (parameterCoordinates F P e (characterLog F P (map F M P l m)))| *
        normWeight p l φ g m := by
  simp only [kernel, weight, normWeight, norm_mul, Complex.norm_conj, Complex.norm_real,
    Real.norm_eq_abs]
  ring

end Kernel

section Coordinates

variable {F : Type} [Field F] [NumberField F]
  {P M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  (l : M ⟶ P) {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)

/-- The coordinates `H ↦ (⟨e(b_j), H⟩)_j` as a linear map. -/
def coordinateMap : RealCharacterDual F P →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.pi fun j => realParameterPairing F P (e (Pi.single j 1))

omit [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left]
  [LocallyOfFiniteType M.X.hom] in
/-- The coordinates dual to a basis of `X^*(P) ⊗ ℝ` determine `H`. -/
theorem coordinateMap_injective : Function.Injective (coordinateMap e) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro H hH
  have hj : ∀ j, realParameterPairing F P (e (Pi.single j 1)) H = 0 := fun j =>
    congrFun hH j
  have h0 : (realParameterPairing F P).flip H ∘ₗ e.toLinearMap = 0 :=
    (Pi.basisFun ℝ (Fin n)).ext fun j => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearMap.flip_apply, Pi.basisFun_apply, LinearMap.zero_apply]
      exact hj j
  have hall : ∀ x : Fin n → ℝ, realParameterPairing F P (e x) H = 0 := fun x =>
    LinearMap.congr_fun h0 x
  apply AddMonoidHom.ext
  intro χ
  have h := hall (e.symm ((1 : ℝ) ⊗ₜ[ℤ] χ))
  rw [LinearEquiv.apply_symm_apply, realParameterPairing_tmul, one_mul] at h
  exact h

omit [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left]
  [LocallyOfFiniteType M.X.hom] in
/-- A Levi projection `π` with `l ≫ π = 𝟙` is a left inverse on real duals. -/
theorem realCharacterDualMap_injective {π : P ⟶ M} (hlπ : l ≫ π = 𝟙 M) :
    Function.Injective (realCharacterDualMap F M P l) := by
  intro H H' h
  apply AddMonoidHom.ext
  intro χ
  have h1 := DFunLike.congr_fun h (characterRestrict π χ)
  change H (characterRestrict l (characterRestrict π χ)) =
    H' (characterRestrict l (characterRestrict π χ)) at h1
  rwa [← AddMonoidHom.comp_apply, ← characterRestrict_comp, hlπ, characterRestrict_id,
    AddMonoidHom.id_apply] at h1

variable (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ M)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type) [Fintype I] (e₀ : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)

/-- The coordinates `y(m)` on the positive torus, as an injective linear map of the
logarithm coordinates. -/
def torusCoordinateMap : (I → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  coordinateMap e ∘ₗ realCharacterDualMap F M P l ∘ₗ realCharacterDualMap F T.toGrp M i ∘ₗ
    (PositiveRealTorus.dualCoordinatesContinuousEquiv F T I e₀).symm.toLinearEquiv.toLinearMap

include hi in
theorem torusCoordinateMap_injective {π : P ⟶ M} (hlπ : l ≫ π = 𝟙 M) :
    Function.Injective (torusCoordinateMap l e T i I e₀) :=
  (coordinateMap_injective e).comp ((realCharacterDualMap_injective l hlπ).comp
    ((realCharacterDualRestrictionEquiv F M T.toGrp i hi).injective.comp
      (PositiveRealTorus.dualCoordinatesContinuousEquiv F T I e₀).symm.injective))

/-- Logarithm coordinates on the positive torus `A`. -/
def positiveCoordinates :
    PositiveRealTorus.intrinsicSubgroup F T ≃ₜ (I → ℝ) where
  toFun a := PositiveRealTorus.dualCoordinatesContinuousEquiv F T I e₀
    (characterLog F T.toGrp a.val)
  invFun v := PositiveRealTorus.positiveExp F T I e₀
    ((PositiveRealTorus.dualCoordinatesContinuousEquiv F T I e₀).symm v)
  left_inv a := by
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    exact (PositiveRealTorus.positiveLogEquiv F T I e₀).symm_apply_apply a
  right_inv v := by
    have h := (PositiveRealTorus.positiveLogEquiv F T I e₀).apply_symm_apply
      (Multiplicative.ofAdd ((PositiveRealTorus.dualCoordinatesContinuousEquiv F T I e₀).symm v))
    have h' := congrArg Multiplicative.toAdd h
    change characterLog F T.toGrp (PositiveRealTorus.positiveExp F T I e₀
      ((PositiveRealTorus.dualCoordinatesContinuousEquiv F T I e₀).symm v)).val =
        (PositiveRealTorus.dualCoordinatesContinuousEquiv F T I e₀).symm v at h'
    simp only [h', ContinuousLinearEquiv.apply_symm_apply]
  continuous_toFun := (PositiveRealTorus.dualCoordinatesContinuousEquiv F T I e₀).continuous.comp
    ((continuous_characterLog F T.toGrp).comp continuous_subtype_val)
  continuous_invFun := (PositiveRealTorus.continuous_positiveExp F T I e₀).comp
    (PositiveRealTorus.dualCoordinatesContinuousEquiv F T I e₀).symm.continuous

theorem parameterCoordinates_positivePointMap (a : PositiveRealTorus.intrinsicSubgroup F T) :
    parameterCoordinates F P e (characterLog F P
      (map F M P l (PositiveRealTorus.positivePointMap F M T i a))) =
      torusCoordinateMap l e T i I e₀ (positiveCoordinates T I e₀ a) := by
  rw [PositiveRealTorus.positivePointMap_apply, characterLog_map, characterLog_map]
  change _ = coordinateMap e (realCharacterDualMap F M P l (realCharacterDualMap F T.toGrp M i
    ((PositiveRealTorus.dualCoordinatesContinuousEquiv F T I e₀).symm
      (PositiveRealTorus.dualCoordinatesContinuousEquiv F T I e₀ (characterLog F T.toGrp a.val)))))
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

include hi e₀ in
/-- `a ↦ β(y(a))` has compact support on the positive torus `A`. -/
theorem hasCompactSupport_positive {π : P ⟶ M} (hlπ : l ≫ π = 𝟙 M) {β : (Fin n → ℝ) → ℝ}
    (hβc : HasCompactSupport β) :
    HasCompactSupport (fun a : PositiveRealTorus.intrinsicSubgroup F T =>
      β (parameterCoordinates F P e (characterLog F P
        (map F M P l (PositiveRealTorus.positivePointMap F M T i a))))) := by
  have hL : IsClosedEmbedding (torusCoordinateMap l e T i I e₀) :=
    LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr (torusCoordinateMap_injective l e T i hi I e₀ hlπ))
  have h := (hβc.comp_isClosedEmbedding hL).comp_isClosedEmbedding
    (positiveCoordinates T I e₀).isClosedEmbedding
  convert h using 1
  funext a
  simp only [Function.comp_apply, parameterCoordinates_positivePointMap l e T i I e₀ a]

include hi e₀ in
theorem lintegral_positive_lt_top {π : P ⟶ M} (hlπ : l ≫ π = 𝟙 M) {β : (Fin n → ℝ) → ℝ}
    (hβ : Continuous β) (hβc : HasCompactSupport β)
    (ν : Measure (PositiveRealTorus.intrinsicSubgroup F T)) [IsFiniteMeasureOnCompacts ν] :
    ∫⁻ a, ‖β (parameterCoordinates F P e (characterLog F P
        (map F M P l (PositiveRealTorus.positivePointMap F M T i a))))‖ₑ ∂ν < ∞ := by
  have hcont : Continuous (fun a : PositiveRealTorus.intrinsicSubgroup F T =>
      β (parameterCoordinates F P e (characterLog F P
        (map F M P l (PositiveRealTorus.positivePointMap F M T i a))))) :=
    hβ.comp ((continuous_parameterCoordinates F P e).comp ((continuous_characterLog F P).comp
      ((map F M P l).continuous.comp (PositiveRealTorus.positivePointMap F M T i).continuous)))
  exact (hcont.integrable_of_hasCompactSupport
    (hasCompactSupport_positive l e T i hi I e₀ hlπ hβc)).hasFiniteIntegral

end Coordinates

section Decomposition

open PositiveRealTorus

variable {F : Type} [Field F] [NumberField F] {M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ M)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type) [Fintype I] (e₀ : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)

/-- The chosen fundamental domain `D¹` for `M(F)` in `M(𝔸)¹`. -/
abbrev normOneDomain : Set (normOneSubgroup F M) :=
  LeftCosetSpace.fundamentalDomain (rationalNormOneSubgroup F M)
    (isDiscrete_rationalNormOneSubgroup F M)

/-- The fundamental domain `A × D¹` for `M(F)` in `M(𝔸) = A × M(𝔸)¹`. -/
def productDomain : Set (AdelicGroupPoints F M) :=
  normOneFactor F M T i hi I e₀ ⁻¹' normOneDomain (M := M)

theorem measurableSet_productDomain : MeasurableSet (productDomain T i hi I e₀) :=
  (continuous_normOneFactor F M T i hi I e₀).measurable
    (LeftCosetSpace.measurableSet_fundamentalDomain _ _)

theorem normOneFactor_mul_of_mem (hc : IsCentral i) {x : AdelicGroupPoints F M}
    (hx : x ∈ normOneSubgroup F M) (m : AdelicGroupPoints F M) :
    (normOneFactor F M T i hi I e₀ (x * m) : AdelicGroupPoints F M) =
      x * normOneFactor F M T i hi I e₀ m := by
  have hx1 : positiveFactor F M T i hi I e₀ x = 1 :=
    positiveFactor_normOne F M T i hi I e₀ ⟨x, hx⟩
  have hpf : positiveFactor F M T i hi I e₀ (x * m) = positiveFactor F M T i hi I e₀ m := by
    rw [map_mul, hx1, one_mul]
  rw [normOneFactor_val, normOneFactor_val, hpf, ← mul_assoc, ← mul_assoc]
  congr 1
  exact ((positivePointMap_commute F M T i hc _ x).inv_left).eq

theorem normOneFactor_positivePointMap_mul (a : intrinsicSubgroup F T)
    (n : normOneSubgroup F M) :
    normOneFactor F M T i hi I e₀ (positivePointMap F M T i a * n) = n := by
  have h := (normOneDecomposition F M T i hi I e₀).symm_apply_apply (a, n)
  exact congrArg Prod.snd h

/-- `A × D¹` is a fundamental domain for `M(F)` in `M(𝔸)`. -/
theorem isFundamentalDomain_productDomain (hc : IsCentral i)
    (ν : Measure (AdelicGroupPoints F M)) :
    IsFundamentalDomain (rationalSubgroup F M) (productDomain T i hi I e₀) ν := by
  refine IsFundamentalDomain.mk' (measurableSet_productDomain T i hi I e₀).nullMeasurableSet ?_
  intro x
  let toN : rationalSubgroup F M → rationalNormOneSubgroup F M := fun g =>
    ⟨⟨g.1, rationalSubgroup_le_normOneSubgroup F M g.2⟩, by
      obtain ⟨q, hq⟩ := g.2
      exact ⟨q, Subtype.ext hq⟩⟩
  have hkey : ∀ g : rationalSubgroup F M, (g : AdelicGroupPoints F M) * x ∈
      productDomain T i hi I e₀ ↔
        ((toN g : normOneSubgroup F M) * normOneFactor F M T i hi I e₀ x) ∈
          normOneDomain (M := M) := by
    intro g
    have h : normOneFactor F M T i hi I e₀ ((g : AdelicGroupPoints F M) * x) =
        (toN g : normOneSubgroup F M) * normOneFactor F M T i hi I e₀ x :=
      Subtype.ext (normOneFactor_mul_of_mem T i hi I e₀ hc
        (rationalSubgroup_le_normOneSubgroup F M g.2) x)
    rw [productDomain, Set.mem_preimage, h]
  obtain ⟨δ, hδ, huniq⟩ := LeftCosetSpace.fundamentalDomain_unique
    (rationalNormOneSubgroup F M) (isDiscrete_rationalNormOneSubgroup F M)
    (normOneFactor F M T i hi I e₀ x)
  have hδ' : toN (rationalNormOneSubgroupInclusion F M δ) = δ := Subtype.ext (Subtype.ext rfl)
  refine ⟨rationalNormOneSubgroupInclusion F M δ, (hkey _).mpr (by rw [hδ']; exact hδ), ?_⟩
  intro g hg
  have h1 := huniq (toN g) ((hkey g).mp hg)
  apply Subtype.ext
  exact congrArg (fun z : rationalNormOneSubgroup F M => ((z : normOneSubgroup F M) :
    AdelicGroupPoints F M)) h1

/-- Lebesgue integrals over `M(F) \ M(𝔸)` for Haar measure of left `M(F)`-invariant functions
that factor as `b(a) w(n)` on `A × M(𝔸)¹`. -/
theorem lintegral_rationalQuotient_haar (hc : IsCentral i) (f : AdelicGroupPoints F M → ℝ≥0∞)
    (b : intrinsicSubgroup F T → ℝ≥0∞) (w : normOneSubgroup F M → ℝ≥0∞)
    (hf : ∀ a (n : normOneSubgroup F M), f (positivePointMap F M T i a * n) = b a * w n)
    (hfinv : ∀ g ∈ rationalSubgroup F M, ∀ m, f (g * m) = f m)
    (hfmeas : Measurable (fun x : RationalQuotient F M => f x.out))
    (hb : Measurable b) (hw : Measurable w) :
    ∫⁻ x : RationalQuotient F M, f x.out
        ∂(LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
          (isDiscrete_rationalSubgroup F M) Measure.haar) =
      (∫⁻ a, b a ∂normalizedPositiveHaarMeasure F M T i hi I e₀ hc) *
        ∫⁻ n : normOneSubgroup F M in normOneDomain (M := M), w n ∂Measure.haar := by
  have := normalizedPositiveHaarMeasure_sigmaFinite F M T i hi I e₀ hc
  rw [LeftCosetSpace.discreteQuotientMeasure_eq _ _ _
      (isFundamentalDomain_productDomain T i hi I e₀ hc _),
    LeftCosetSpace.quotientMeasure, lintegral_map hfmeas (LeftCosetSpace.measurable_mk _)]
  have h1 : ∀ m, f (LeftCosetSpace.mk (rationalSubgroup F M) m).out = f m :=
    out_mk_apply (rationalSubgroup F M) f hfinv
  simp_rw [h1]
  rw [← (measurePreserving_normOneDecomposition F M T i hi I e₀ hc).setLIntegral_comp_preimage_emb
    (normOneDecomposition F M T i hi I e₀).measurableEmbedding]
  have hpre : (normOneDecomposition F M T i hi I e₀) ⁻¹' productDomain T i hi I e₀ =
      Set.univ ×ˢ normOneDomain (M := M) := by
    ext q
    simp only [Set.mem_preimage, productDomain, normOneDecomposition_apply,
      normOneFactor_positivePointMap_mul, Set.mem_prod, Set.mem_univ, true_and]
  rw [hpre, ← Measure.prod_restrict, Measure.restrict_univ]
  simp_rw [normOneDecomposition_apply, hf]
  exact lintegral_prod_mul hb.aemeasurable hw.aemeasurable

/-- Lebesgue integrals over `[M]` for the canonical measure, as integrals over `D¹`. -/
theorem lintegral_canonical (W : AdelicGroupPoints F M → ℝ≥0∞)
    (hWinv : ∀ g ∈ RestrictionSplitCentre.canonicalRationalSubgroup F M, ∀ m, W (g * m) = W m)
    (hWmeas : Measurable (fun x : RestrictionSplitCentre.CanonicalQuotient F M => W x.out)) :
    ∫⁻ x : RestrictionSplitCentre.CanonicalQuotient F M, W x.out
        ∂(RestrictionSplitCentre.canonicalMeasure F M) =
      ∫⁻ n : normOneSubgroup F M in normOneDomain (M := M), W n ∂Measure.haar := by
  unfold RestrictionSplitCentre.canonicalMeasure RestrictionSplitCentre.quotientHaarMeasure
  rw [lintegral_map hWmeas (RestrictionSplitCentre.measurable_normOneToQuotient _ _ _ _)]
  unfold normOneRationalQuotientHaarMeasure LeftCosetSpace.haarQuotientMeasure
    LeftCosetSpace.discreteQuotientMeasure LeftCosetSpace.quotientMeasure
  rw [lintegral_map (f := fun y => W (RestrictionSplitCentre.normOneToQuotient F M _ _ y).out)
    (hWmeas.comp (RestrictionSplitCentre.measurable_normOneToQuotient _ _ _ _))
    (LeftCosetSpace.measurable_mk _)]
  refine lintegral_congr fun n => ?_
  simp only [RestrictionSplitCentre.normOneToQuotient_mk]
  exact out_mk_apply _ W hWinv n

end Decomposition

section Integrability

open PositiveRealTorus RestrictionSplitCentre

variable {F : Type} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
  {β : (Fin n → ℝ) → ℝ}

theorem mem_canonicalSubgroup_positivePointMap (a : intrinsicSubgroup F (canonicalTorus F M)) :
    positivePointMap F M (canonicalTorus F M) (canonicalComponent F M) a ∈
      canonicalSubgroup F M := by
  rw [canonicalSubgroup_eq_imageSubgroup]
  exact ⟨a.val, a.property, rfl⟩

theorem canonicalRationalSubgroup_le_leftStabilizer {φ : AdelicGroupPoints F G → ℂ}
    (hφinv : IsLeftInvariantUnder F G (parabolicLeviRationalImage F p l) φ)
    (hφeq : IsSplitComponentEquivariant p l φ) (g : AdelicGroupPoints F G) :
    canonicalRationalSubgroup F M ≤ Langlands.Automorphic.UnitaryCharacterPairing.leftStabilizer (normWeight p l φ g) :=
  sup_le (fun _ ha m => normWeight_splitComponent_mul hφeq ha g m)
    (fun _ hx m => normWeight_rational_mul hφinv hx g m)

/-- For fixed `g`, the integral of `|β(y(m)) δ_P(m)⁻¹ φ(m g)²|` over `M(F) \ M(𝔸)` is a fixed
finite constant times the integral of `δ_P(m)⁻¹ |φ(m g)|²` over `[M]`. -/
theorem exists_lintegral_rationalQuotient_kernel (hM : IsConnectedReductive M) {π : P ⟶ M}
    (hlπ : l ≫ π = 𝟙 M) (hβ : Continuous β) (hβc : HasCompactSupport β)
    {φ : AdelicGroupPoints F G → ℂ} (hφc : Continuous φ)
    (hφinv : IsLeftInvariantUnder F G (parabolicLeviRationalImage F p l) φ)
    (hφeq : IsSplitComponentEquivariant p l φ) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ g : AdelicGroupPoints F G,
      ∫⁻ x : RationalQuotient F M, ‖kernel p l e β φ φ g x.out‖ₑ
          ∂(LeftCosetSpace.discreteQuotientMeasure (AdelicGroupPoints.rationalSubgroup F M)
            (isDiscrete_rationalSubgroup F M) Measure.haar) =
        C * ∫⁻ x : CanonicalQuotient F M, ‖normWeight p l φ g x.out‖ₑ
          ∂(canonicalMeasure F M) := by
  have hs₀ := isSplitComponent_canonicalComponent F M
  have hi := canonical_characterRestrict_injective F M centralSplitTorusCharacter hM
  have := canonical_finiteIndex F M hM
  have := canonicalQuotient_borelSpace F M centralSplitTorusCharacter hM
  obtain ⟨I, hIfin, ⟨e₀⟩⟩ := hs₀.1.1.1
  have hc : IsCentral (canonicalComponent F M) := hs₀.1.2
  let := Fintype.ofFinite I
  let := positiveIsTopologicalGroup F (canonicalTorus F M) I e₀
  have := normalizedPositiveHaarMeasure_isHaarMeasure F M (canonicalTorus F M)
    (canonicalComponent F M) hi I e₀ hc
  refine ⟨_, lintegral_positive_lt_top l e (canonicalTorus F M) (canonicalComponent F M) hi I e₀
    hlπ hβ hβc (normalizedPositiveHaarMeasure F M (canonicalTorus F M)
      (canonicalComponent F M) hi I e₀ hc), fun g => ?_⟩
  have hcontk : Continuous (fun m : AdelicGroupPoints F M => kernel p l e β φ φ g m) :=
    continuous_kernel p l e β continuous_const continuous_id hβ hφc hφc
  have hcontw : Continuous (fun m : AdelicGroupPoints F M => normWeight p l φ g m) :=
    continuous_normWeight p l continuous_const continuous_id hφc
  have hstab := canonicalRationalSubgroup_le_leftStabilizer hφinv hφeq g
  have hf : ∀ a (m : normOneSubgroup F M), ‖kernel p l e β φ φ g
      (positivePointMap F M (canonicalTorus F M) (canonicalComponent F M) a * m)‖ₑ =
      ‖β (parameterCoordinates F P e (characterLog F P (map F M P l
        (positivePointMap F M (canonicalTorus F M) (canonicalComponent F M) a))))‖ₑ *
        ‖normWeight p l φ g m‖ₑ := by
    intro a m
    rw [← enorm_norm, norm_kernel_self, enorm_mul,
      characterLog_map_mul_normOne l m.property,
      normWeight_splitComponent_mul hφeq (mem_canonicalSubgroup_positivePointMap a) g m,
      Real.enorm_abs]
  have hfinv : ∀ x ∈ AdelicGroupPoints.rationalSubgroup F M, ∀ m,
      ‖kernel p l e β φ φ g (x * m)‖ₑ = ‖kernel p l e β φ φ g m‖ₑ := by
    intro x hx m
    rw [kernel_rational_mul e β hφinv hφinv hx g m]
  have hfmeas : Measurable (fun x : RationalQuotient F M => ‖kernel p l e β φ φ g x.out‖ₑ) :=
    (continuous_out (AdelicGroupPoints.rationalSubgroup F M) _ hcontk.enorm hfinv).measurable
  have hb : Measurable (fun a : intrinsicSubgroup F (canonicalTorus F M) =>
      ‖β (parameterCoordinates F P e (characterLog F P (map F M P l
        (positivePointMap F M (canonicalTorus F M) (canonicalComponent F M) a))))‖ₑ) :=
    (hβ.comp ((continuous_parameterCoordinates F P e).comp ((continuous_characterLog F P).comp
      ((map F M P l).continuous.comp (positivePointMap F M (canonicalTorus F M)
        (canonicalComponent F M)).continuous)))).enorm.measurable
  have hw : Measurable (fun m : normOneSubgroup F M => ‖normWeight p l φ g m‖ₑ) :=
    (hcontw.enorm.comp continuous_subtype_val).measurable
  have hWinv : ∀ x ∈ canonicalRationalSubgroup F M, ∀ m,
      ‖normWeight p l φ g (x * m)‖ₑ = ‖normWeight p l φ g m‖ₑ := by
    intro x hx m
    rw [hstab hx m]
  have hWmeas : Measurable (fun x : CanonicalQuotient F M => ‖normWeight p l φ g x.out‖ₑ) :=
    (continuous_out (canonicalRationalSubgroup F M) _ hcontw.enorm hWinv).measurable
  refine (lintegral_rationalQuotient_haar (canonicalTorus F M) (canonicalComponent F M) hi I e₀ hc
    (fun m => ‖kernel p l e β φ φ g m‖ₑ) _ (fun m : normOneSubgroup F M => ‖normWeight p l φ g m‖ₑ)
    hf hfinv hfmeas hb hw).trans ?_
  congr 1
  exact (lintegral_canonical (fun m => ‖normWeight p l φ g m‖ₑ) hWinv hWmeas).symm

variable (K : Subgroup (AdelicGroupPoints F G))
  (hKc : IsCompact (K : Set (AdelicGroupPoints F G)))
  {U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine U.X.left] {iU : U ⟶ P}
  {N d : ℕ} {rho : MatrixRepresentation G (Fin N)} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  {hcalc : AdelicDifferentialCommutator F G hsmooth}

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
  [LocallyOfFiniteType P.X.hom] [IsAffine U.X.left] in
theorem sFinite_discreteQuotientMeasure (μM : Measure (AdelicGroupPoints F M))
    [μM.IsHaarMeasure] :
    SFinite (LeftCosetSpace.discreteQuotientMeasure (AdelicGroupPoints.rationalSubgroup F M)
      (isDiscrete_rationalSubgroup F M) μM) := by
  unfold LeftCosetSpace.discreteQuotientMeasure LeftCosetSpace.quotientMeasure
  infer_instance

/-- The integrand of `(φ, φ)_P` is integrable on `K × M(F) \ M(𝔸)` for `φ ∈ A^2_P`. -/
theorem integrable_kernel_self (hM : IsConnectedReductive M) {π : P ⟶ M} (hlπ : l ≫ π = 𝟙 M)
    (hβ : Continuous β) (hβc : HasCompactSupport β)
    (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure] {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc p iU l φ) :
    Integrable (fun q : K × RationalQuotient F M => kernel p l e β φ φ q.1 q.2.out)
      ((compactHaarProbability F G K hKc).prod
        (LeftCosetSpace.discreteQuotientMeasure (AdelicGroupPoints.rationalSubgroup F M)
          (isDiscrete_rationalSubgroup F M) μM)) := by
  have hφc : Continuous φ := hφ.1.2.1.1
  have hφinv : IsLeftInvariantUnder F G (parabolicLeviRationalImage F p l) φ := fun x hx g' =>
    hφ.1.1 x (Subgroup.mem_sup_right hx) g'
  have hφeq : IsSplitComponentEquivariant p l φ := hφ.2.1
  have := canonicalQuotient_borelSpace F M centralSplitTorusCharacter hM
  obtain ⟨C, hC, hEq⟩ := exists_lintegral_rationalQuotient_kernel e hM hlπ hβ hβc hφc hφinv hφeq
  have hcont : Continuous (fun q : K × RationalQuotient F M => kernel p l e β φ φ q.1 q.2.out) :=
    continuous_prod_out (AdelicGroupPoints.rationalSubgroup F M)
      (fun q : K × AdelicGroupPoints F M => kernel p l e β φ φ q.1 q.2)
      (continuous_kernel p l e β (ξ := fun q : K × AdelicGroupPoints F M => (q.1 : AdelicGroupPoints F G))
        (τ := Prod.snd) continuous_fst.subtype_val continuous_snd hβ
        hφc hφc)
      (fun _ x hx m => kernel_rational_mul e β hφinv hφinv hx _ m)
  have hcont2 : Continuous (fun q : K × CanonicalQuotient F M =>
      normWeight p l φ q.1 q.2.out) :=
    continuous_prod_out (canonicalRationalSubgroup F M)
      (fun q : K × AdelicGroupPoints F M => normWeight p l φ q.1 q.2)
      (continuous_normWeight p l (ξ := fun q : K × AdelicGroupPoints F M => (q.1 : AdelicGroupPoints F G))
        (τ := Prod.snd) continuous_fst.subtype_val continuous_snd hφc)
      (fun _ x hx m => canonicalRationalSubgroup_le_leftStabilizer hφinv hφeq _ hx m)
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  have := sFinite_discreteQuotientMeasure μM
  have : SFinite (canonicalMeasure F M) := by
    unfold canonicalMeasure quotientHaarMeasure normOneRationalQuotientHaarMeasure
      LeftCosetSpace.haarQuotientMeasure LeftCosetSpace.discreteQuotientMeasure
      LeftCosetSpace.quotientMeasure
    infer_instance
  set c := Measure.haarScalarFactor μM (Measure.haar : Measure (AdelicGroupPoints F M)) with hcdef
  have hμ : μM = c • (Measure.haar : Measure (AdelicGroupPoints F M)) :=
    Measure.isMulLeftInvariant_eq_smul μM Measure.haar
  have hν : LeftCosetSpace.discreteQuotientMeasure (AdelicGroupPoints.rationalSubgroup F M)
      (isDiscrete_rationalSubgroup F M) μM =
      c • LeftCosetSpace.discreteQuotientMeasure (AdelicGroupPoints.rationalSubgroup F M)
        (isDiscrete_rationalSubgroup F M) Measure.haar := by
    rw [hμ]
    unfold LeftCosetSpace.discreteQuotientMeasure LeftCosetSpace.quotientMeasure
    rw [Measure.restrict_smul, Measure.map_smul _ (LeftCosetSpace.measurable_mk _).aemeasurable]
  have hlhs : ∀ k : K, ∫⁻ x : RationalQuotient F M, ‖kernel p l e β φ φ k x.out‖ₑ
      ∂(LeftCosetSpace.discreteQuotientMeasure (AdelicGroupPoints.rationalSubgroup F M)
        (isDiscrete_rationalSubgroup F M) μM) =
      (c : ℝ≥0∞) * (C * ∫⁻ x : CanonicalQuotient F M, ‖normWeight p l φ k x.out‖ₑ
        ∂(canonicalMeasure F M)) := by
    intro k
    rw [hν, lintegral_smul_measure, hEq, ENNReal.smul_def, smul_eq_mul]
  unfold HasFiniteIntegral
  rw [lintegral_prod _ hcont.enorm.aemeasurable]
  simp only [hlhs]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_const_mul' _ _ hC.ne]
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top hC ?_)
  refine lt_of_eq_of_lt (lintegral_prod _ hcont2.enorm.aemeasurable).symm ?_
  exact hφ.2.2.hasFiniteIntegral

/-- The integrand of `(φ, ψ)_P` is integrable on `K × M(F) \ M(𝔸)` for `φ, ψ ∈ A^2_P`. -/
theorem integrable_kernel (hM : IsConnectedReductive M) {π : P ⟶ M} (hlπ : l ≫ π = 𝟙 M)
    (hβ : Continuous β) (hβc : HasCompactSupport β)
    (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure] {φ ψ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc p iU l φ)
    (hψ : IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc p iU l ψ) :
    Integrable (fun q : K × RationalQuotient F M => kernel p l e β φ ψ q.1 q.2.out)
      ((compactHaarProbability F G K hKc).prod
        (LeftCosetSpace.discreteQuotientMeasure (AdelicGroupPoints.rationalSubgroup F M)
          (isDiscrete_rationalSubgroup F M) μM)) := by
  have hφinv : IsLeftInvariantUnder F G (parabolicLeviRationalImage F p l) φ := fun x hx g' =>
    hφ.1.1 x (Subgroup.mem_sup_right hx) g'
  have hψinv : IsLeftInvariantUnder F G (parabolicLeviRationalImage F p l) ψ := fun x hx g' =>
    hψ.1.1 x (Subgroup.mem_sup_right hx) g'
  have hcont : Continuous (fun q : K × RationalQuotient F M => kernel p l e β φ ψ q.1 q.2.out) :=
    continuous_prod_out (AdelicGroupPoints.rationalSubgroup F M)
      (fun q : K × AdelicGroupPoints F M => kernel p l e β φ ψ q.1 q.2)
      (continuous_kernel p l e β (ξ := fun q : K × AdelicGroupPoints F M => (q.1 : AdelicGroupPoints F G))
        (τ := Prod.snd) continuous_fst.subtype_val continuous_snd hβ
        hφ.1.2.1.1 hψ.1.2.1.1)
      (fun _ x hx m => kernel_rational_mul e β hφinv hψinv hx _ m)
  exact Integrable.mono'
    ((integrable_kernel_self e K hKc hM hlπ hβ hβc μM hφ).norm.add
      (integrable_kernel_self e K hKc hM hlπ hβ hβc μM hψ).norm)
    hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => norm_kernel_le p l e β φ ψ q.1 q.2.out)

end Integrability

end Langlands.Global.InducedInnerProductSesquilinear

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  InducedInnerProductSesquilinear

/-- **Sesquilinearity of `(·,·)_P`** (premise (D) of the reduction of Lapid 2011, Lemma 10):
the integral defining `(φ, ψ)_P` converges absolutely on `K × M(F) \ M(𝔸)` for `φ, ψ ∈ A^2_P`,
so `(·,·)_P` is sesquilinear on finite linear combinations. -/
theorem inducedInnerProductSesquilinear : InducedInnerProductSesquilinearStatement := by
  intro F _ _ G P M U A _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ hA hT π hG hU hlπ K hK N d rho hsmooth
    hcalc hKmax hrho μM _ hμM n e β hβ hβc _ k v hv z z'
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  have hM : IsConnectedReductive M := r.isCompatible.levi.isConnectedReductive
  have := sFinite_discreteQuotientMeasure μM
  simp only [inducedInnerProduct_eq_kernel p l e β K hK.isCompact μM, kernel_sum]
  exact integral_integral_sum_sum
    (fun j j' (q : K) (x : RationalQuotient F M) => kernel p l e β (v j) (v j') q x.out)
    (fun j j' => integrable_kernel e K hK.isCompact hM hlπ hβ hβc μM (hv j) (hv j'))
    (fun j j' => z j * (starRingEnd ℂ) (z' j'))

end Langlands.Global
