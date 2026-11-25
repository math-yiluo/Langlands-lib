import Langlands.Theta.DualPair.Unitary.LeraySplitting
import Langlands.Theta.WeilIndex.Defs

/-!
# The scalar at the Weyl element of the Leray splitting of `U(ν, ν)`

GKT Proposition 12.29 (p. 375) in Case `3₊` with `W` split: `β(w) = γ(ψ_{1/2} ∘ Res_{E/F} V)^{n/2}`,
`n/2 = |ν|`, with `Res_{E/F} V` the symmetric bilinear space of Corollary 11.4 (p. 315) and the
function `β` of (11.3) (p. 318); the measure `d𝐱` of Proposition 12.27 (1) (p. 372) is the
self-dual one.

The Weil representation `lerayWeil c ν ψ χ Q` of `U(ν, ν)` acts at the Weyl element by
`lerayScalar c ψ χ Q μ` times the Fourier transform `φ ↦ ∫ ψ(⟪x, y⟫) φ(y) dμ(y)`
(`lerayWeil_weylElement_apply`). Here:

`lerayScalar c ψ χ Q μ = C(μ)^{-1/2} · γ(ψ_{1/2} ∘ Res_{E/F} V)^{|ν|}` (`lerayScalar_eq`),

`C(μ)` the constant of Fourier inversion of `ψ ∘ ⟪,⟫` for `μ`; so for the self-dual measure the
scalar is the Weil index `γ(ψ_{1/2} ∘ Res_{E/F} V)^{|ν|}` (`lerayScalar_selfDualMeasure`), the
book's `β(w)`, and nothing existential is left: the representation is determined by its formulas
on the Siegel parabolic and at the Weyl element (`IsLerayWeil.unique`), with definite scalars.

Proof. For a representation `IsLerayWeil c ψ' χ Q μ κ ω` (the Library's character `ψ' = ψ(2 ·)`),
the relation `w n(1) w = p₀ w n(-1)` of the big cell gives `κ X = Y`, and the braid relation gives
`s(det(-1_ν)) X = γ₀ Y` with `γ₀` the Gauss integral of `f(x) = ψ(½ ⟪x, x⟫)`; so
`κ γ₀ = s(det(-1_ν))` (`Unitary.Internal.mul_gaussIntegral_eq`). The Gauss integral of
`f(-·) = conj f` is `γ₀ s(det(-1_ν))⁻¹` (the Hermitian Gauss integrals, `b = -1`) and also
`conj γ₀`.
Hence `κ C(μ) = κ γ₀ conj γ₀ = γ₀`, and `γ₀ = C(μ)^{1/2} γ(f)` (`hasGaussIntegral_weilIndex`).
Finally `f(x) = ∏_j ψ(½ tr(x_j, x_j))` over the columns `x_j` of `x`, so
`γ(f) = γ(ψ_{1/2} ∘ Res_{E/F} V)^{|ν|}` (GKT Proposition 3.13 (a), (d)).
-/

noncomputable section

open MeasureTheory Matrix
open scoped NNReal

namespace Langlands.Theta

open Langlands.UnitaryGroup Langlands.HarmonicAnalysis

/-! ### The symmetric bilinear space `Res_{E/F} V` -/

section Form

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α : Type} [Fintype α]

/-- **`Res_{E/F} V`** (GKT Corollary 11.4): for the Hermitian space `V = E^α` with the form
`(v, w) = vᵀ Q c(w)`, the `F`-bilinear form `(v, w) ↦ tr_{E/F}(v, w)` on `V` viewed as an
`F`-vector space (symmetric for a Hermitian `Q`: `hermitianTraceForm_symm`). Its quadratic form in
GKT's convention is `q(v) = tr_{E/F}(v, v) = 2 (v, v)`. -/
def hermitianTraceForm (Q : Matrix α α E) : LinearMap.BilinForm F (α → E) :=
  LinearMap.mk₂ F (fun v w => Algebra.trace F E (v ⬝ᵥ (Q *ᵥ fun i => c (w i))))
    (fun v v' w => by rw [add_dotProduct, map_add])
    (fun t v w => by rw [smul_dotProduct, map_smul])
    (fun v w w' => by
      have : (fun i => c ((w + w') i)) = (fun i => c (w i)) + fun i => c (w' i) := by
        funext i; simp
      rw [this, mulVec_add, dotProduct_add, map_add])
    (fun t v w => by
      have : (fun i => c ((t • w) i)) = t • fun i => c (w i) := by
        funext i; simp [map_smul]
      rw [this, mulVec_smul, dotProduct_smul, map_smul])

theorem hermitianTraceForm_apply (Q : Matrix α α E) (v w : α → E) :
    hermitianTraceForm c Q v w = Algebra.trace F E (v ⬝ᵥ (Q *ᵥ fun i => c (w i))) := rfl

/-- **The book's pairing of `𝕏^*` and `𝕏` is `Res_{E/F} V` on the columns**:
`⟪x, y⟫ = ∑_j tr_{E/F}(x_j, y_j)` (GKT 11.1.1 with `W = E^{2ν}`, `𝕏^* = (E^ν)^* ⊗ V`). -/
theorem hermitianTracePairing_eq_sum [DecidableEq α] [NeZero (2 : F)] {ν : Type} [Fintype ν]
    (Q : Matrix α α E) (x y : Matrix α ν E) :
    hermitianTracePairing c Q x y =
      ∑ j, hermitianTraceForm c Q (fun i => x i j) (fun i => y i j) := by
  rw [hermitianTracePairing_apply]
  simp only [hermitianTraceForm_apply]
  rw [← map_sum]
  congr 1
  simp only [Matrix.trace, diag_apply, mul_apply, transpose_apply, map_apply, dotProduct, mulVec,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

end Form

namespace Unitary.Internal

theorem addChar_sum {F ι : Type*} [AddCommGroup F] (ψ : AddChar F ℂ) (s : Finset ι) (g : ι → F) :
    ψ (∑ i ∈ s, g i) = ∏ i ∈ s, ψ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

end Unitary.Internal

section FormLocal

open Unitary.Internal

variable {F : Type} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type} [Field E] [Algebra F E] [TopologicalSpace E]
  [IsModuleTopology F E] {c : E →ₐ[F] E} {δ : E} {α : Type} [Fintype α] [DecidableEq α]
  {Q : Matrix α α E}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [TopologicalSpace E]
  [IsModuleTopology F E] in
/-- `Res_{E/F} V` through the matrices with one column: `tr_{E/F}(v, w) = 2 pr(v, w)`. -/
private theorem hermitianTraceForm_eq_pr (v w : α → E) :
    hermitianTraceForm c Q v w =
      2 * pr c Q (Matrix.of fun i (_ : Unit) => v i) (Matrix.of fun i (_ : Unit) => w i) := by
  have h := hermitianTracePairing_eq_sum c Q (Matrix.of fun i (_ : Unit) => v i)
    (Matrix.of fun i (_ : Unit) => w i)
  simp only [Fintype.sum_unique, Matrix.of_apply] at h
  rw [← h, hermitianTracePairing_eq_mul, hermitianPairing_eq_hermitianSymplecticForm]
  rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [TopologicalSpace E]
  [IsModuleTopology F E] in
/-- `Res_{E/F} V` is symmetric for a Hermitian `Q`. -/
theorem hermitianTraceForm_symm (hE : IsQuadraticInvolution c δ) (hQ : Matrix.IsHermitianFor c Q)
    (hQu : IsUnit Q.det) (v w : α → E) :
    hermitianTraceForm c Q v w = hermitianTraceForm c Q w v := by
  obtain ⟨β, hβ, hs, -, -, -⟩ := pr_alg F E c δ hE α Unit Q ⟨hQ, hQu⟩
  rw [hermitianTraceForm_eq_pr, hermitianTraceForm_eq_pr, ← hβ, ← hβ, hs]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [TopologicalSpace E]
  [IsModuleTopology F E] in
/-- `Res_{E/F} V` is non-degenerate for an invertible Hermitian `Q`. -/
theorem hermitianTraceForm_nondegenerate (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (w : α → E)
    (hw : ∀ v, hermitianTraceForm c Q v w = 0) : w = 0 := by
  obtain ⟨β, hβ, -, hnd, -, -⟩ := pr_alg F E c δ hE α Unit Q ⟨hQ, hQu⟩
  have h0 := hnd (Matrix.of fun i (_ : Unit) => w i) fun x => by
    have := hw fun i => x i ()
    rw [hermitianTraceForm_eq_pr, mul_eq_zero] at this
    rw [hβ]
    convert this.resolve_left two_ne_zero
    ext i j
    rfl
  funext i
  exact congrFun (congrFun h0 i) ()

/-- **`v ↦ ψ(½ tr_{E/F}(v, v)) = ψ((v, v))` is a character of second degree**, the one whose Weil
index is the book's `γ(ψ_{1/2} ∘ Res_{E/F} V)` ((11.3), Corollary 11.4); its bicharacter is
`ψ ∘ Res_{E/F} V`. -/
theorem isCharacterOfSecondDegree_hermitianTraceForm (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) {ψ : AddChar F ℂ} (hψ : Continuous ψ)
    (hn : ∀ t, ‖ψ t‖ = 1) (h1 : ψ ≠ 1) :
    IsCharacterOfSecondDegree fun v : α → E => ψ ((2 : F)⁻¹ * hermitianTraceForm c Q v v) := by
  have : FiniteDimensional F E := hE.finite
  have he := isSelfDualBicharacter_of_symm (V := α → E) hψ hn h1 (hermitianTraceForm c Q)
    (hermitianTraceForm_symm hE hQ hQu) (hermitianTraceForm_nondegenerate hE hQ hQu)
  refine IsCharacterOfSecondDegree.of_bicharacter he (fun v => hn _)
    ((isLocallyConstant_of_continuous_addChar ψ hψ).comp_continuous
      (continuous_const.mul ((IsModuleTopology.continuous_bilinear_of_finite_left
        (hermitianTraceForm c Q)).comp (continuous_id.prodMk continuous_id)))) fun v w => ?_
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  simp only [map_add, LinearMap.add_apply, hermitianTraceForm_symm hE hQ hQu w v]
  ring

end FormLocal

/-! ### The scalar -/

section Scalar

open Unitary.Internal

variable {F : Type} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type} [Field E] [Algebra F E] [TopologicalSpace E]
  [IsModuleTopology F E] {c : E →ₐ[F] E} {δ : E} {α ν : Type} [Fintype α] [DecidableEq α]
  [Fintype ν] [DecidableEq ν] {Q : Matrix α α E} {χ : Eˣ →* Circle}

omit [CharZero F] [IsModuleTopology F E] [TopologicalSpace E] [DecidableEq α] in
private theorem siegelParabolicOp_smul' (ψ : AddChar F ℂ) (g : Matrix (ν ⊕ ν) (ν ⊕ ν) E) (k : ℂ)
    (f : Matrix α ν E → ℂ) :
    siegelParabolicOp c ψ χ Q g (k • f) = k • siegelParabolicOp c ψ χ Q g f := by
  funext x; simp only [siegelParabolicOp, Pi.smul_apply, smul_eq_mul]; ring

omit [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsModuleTopology F E] [DecidableEq α] in
private theorem hermitianFourier_smul' [MeasurableSpace (Matrix α ν E)] (ψ : AddChar F ℂ)
    (μ : Measure (Matrix α ν E)) (k : ℂ) (f : Matrix α ν E → ℂ) :
    hermitianFourier c ψ Q μ (k • f) = k • hermitianFourier c ψ Q μ f := by
  funext x
  simp only [hermitianFourier, bicharacterFourier, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]; congr 1; funext y; ring

/-- **`κ γ₀ = s(det(-1_ν))`**: for a representation `IsLerayWeil c ψ χ Q μ κ ω` and the Gauss
integral `γ₀` of `x ↦ ψ(½ pr(x, x))`, from the relation `w n(1) w = p₀ w n(-1)` of the big cell
(`κ² X = κ Y`) and the braid relation (`s(det(-1)) X = γ₀ Y`). -/
theorem Unitary.Internal.mul_gaussIntegral_eq (hE : IsQuadraticInvolution c δ) (hQ : IsHerm c Q)
    {ψ : AddChar F ℂ} (hψ : Continuous ψ) (hn : ∀ t, ‖ψ t‖ = 1) (h1 : ψ ≠ 1) (hχ : Continuous χ)
    (hres : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)]
    [BorelSpace (Matrix α ν E)] {μ : Measure (Matrix α ν E)} [μ.IsAddHaarMeasure] {κ : ℂ}
    {ω : Representation ℂ (ofForm c (hyperbolicForm ν E)) (SchwartzBruhat (Matrix α ν E))}
    (h : IsLerayWeil c ψ χ Q μ κ ω) {γ : ℂ}
    (hG : HasGaussIntegral μ (fun x => ψ (2⁻¹ * pr c Q x (x * (1 : Matrix ν ν E)))) γ) :
    κ * γ = splittingScalar F χ (Fintype.card α) (-(1 : Matrix ν ν E)⁻¹).det := by
  have h1m : ((1 : Matrix ν ν E).map c)ᵀ = 1 := by
    rw [Matrix.map_one _ (map_zero c) (map_one c), transpose_one]
  have h1' := WeylCellRel.herm_neg_inv c (1 : Matrix ν ν E) h1m (by simp)
  set w := weylElement c ν
  set n := siegelUnipotent c (1 : Matrix ν ν E) h1m
  set n' := siegelUnipotent c (-(1 : Matrix ν ν E)⁻¹) h1'
  set p₀ := w * n * w * n'⁻¹ * w⁻¹
  have hp₀m : mat c p₀ = fromBlocks (-(1 : Matrix ν ν E)⁻¹) 1 0 (-1) :=
    WeylCellRel.splitUnitaryElementMatrix_bigCell_product c 1 h1m (by simp) h1'
  have hp₀ : p₀ ∈ siegelParabolic c ν := by rw [mem_sieg, hp₀m]; simp
  have hnP : n ∈ siegelParabolic c ν := by rw [mem_sieg, WeylCellRel.mat_unip]; simp
  have hn'P : n' ∈ siegelParabolic c ν := by rw [mem_sieg, WeylCellRel.mat_unip]; simp
  have hrel : w * n * w = p₀ * w * n' := by simp only [p₀]; group
  obtain ⟨φ, hφ⟩ := exists_schwartzBruhat_ne_zero (α := α) (ν := ν) hE
  set X := hermitianFourier c ψ Q μ (siegelParabolicOp c ψ χ Q (mat c n)
    (hermitianFourier c ψ Q μ φ))
  set Y := siegelParabolicOp c ψ χ Q (mat c p₀)
    (hermitianFourier c ψ Q μ (siegelParabolicOp c ψ χ Q (mat c n') φ))
  have e1 : (ω (w * n * w) φ : Matrix α ν E → ℂ) = (κ * κ) • X := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h.weylElement_apply,
      h.apply_of_mem_siegelParabolic n hnP, h.weylElement_apply, siegelParabolicOp_smul',
      hermitianFourier_smul', smul_smul]
  have e2 : (κ * κ) • X = κ • Y := by
    rw [← e1, hrel, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      h.apply_of_mem_siegelParabolic p₀ hp₀, h.weylElement_apply,
      h.apply_of_mem_siegelParabolic n' hn'P, siegelParabolicOp_smul']
  have hκ := h.ne_zero hE
  have hX : X ≠ 0 := by
    intro hX0
    rw [hX0, smul_zero] at e1
    apply hφ
    have : ω (w * n * w) φ = 0 := Subtype.ext e1
    have h2 := congrArg (ω (w * n * w)⁻¹) this
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      map_zero] at h2
  have hXY : κ • X = Y := by
    rw [← smul_smul] at e2
    exact smul_right_injective _ hκ e2
  -- the braid relation for `b = 1`
  have br := braid_relation F E c δ hE α ν Q hQ ψ hψ hn h1 χ hχ hres μ 1 γ h1m (by simp) hG φ φ.2
  rw [← WeylCellRel.mat_unip c 1 h1m, ← WeylCellRel.mat_unip c (-(1 : Matrix ν ν E)⁻¹) h1',
    ← hp₀m] at br
  change splittingScalar F χ (Fintype.card α) (-(1 : Matrix ν ν E)⁻¹).det • X = γ • Y at br
  rw [← hXY, smul_smul] at br
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hX
  have := congrFun br x
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this hx
  rw [mul_comm]
  exact (mul_right_cancel₀ hx this).symm

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [TopologicalSpace E] [IsModuleTopology F E] [DecidableEq ν] in
/-- `⟪,⟫` is symmetric for a Hermitian `Q`. -/
theorem hermitianTracePairing_symm (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (x y : Matrix α ν E) :
    hermitianTracePairing c Q x y = hermitianTracePairing c Q y x := by
  rw [hermitianTracePairing_eq_sum, hermitianTracePairing_eq_sum]
  exact Finset.sum_congr rfl fun j _ => hermitianTraceForm_symm hE hQ hQu _ _

/-- **`ψ ∘ ⟪,⟫` is a self-dual bicharacter** of `M_{α×ν}(E)` (the pairing of the Fourier transform
at the Weyl element, GKT Proposition 12.27 (1)). -/
theorem isSelfDualBicharacter_hermitianTracePairing
    (hE : IsQuadraticInvolution c δ) (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det)
    {ψ : AddChar F ℂ} (hψ : Continuous ψ) (hn : ∀ t, ‖ψ t‖ = 1) (h1 : ψ ≠ 1) :
    IsSelfDualBicharacter fun x y : Matrix α ν E => ψ (hermitianTracePairing c Q x y) := by
  have : FiniteDimensional F E := hE.finite
  have : IsModuleTopology F (Matrix α ν E) := isModuleTopology_matrix F (E := E) α ν
  refine isSelfDualBicharacter_of_symm (V := Matrix α ν E) hψ hn h1 (hermitianTracePairing c Q)
    (hermitianTracePairing_symm hE hQ hQu) fun y hy => ?_
  obtain ⟨β, hβ, -, hnd, -, -⟩ := pr_alg F E c δ hE α ν Q ⟨hQ, hQu⟩
  refine hnd y fun x => ?_
  have := hy x
  rw [hermitianTracePairing_eq_mul, hermitianPairing_eq_hermitianSymplecticForm,
    mul_eq_zero] at this
  rw [hβ]
  exact this.resolve_left two_ne_zero

variable [Invertible (2 : F)] [Algebra.IsQuadraticExtension F E]

/-- **The scalar at the Weyl element** (GKT Proposition 12.29, Case `3₊`, with the measure):
for every Haar measure `μ` on `M_{α×ν}(E)`,
`lerayScalar c ψ χ Q μ = C(μ)^{-1/2} γ(ψ_{1/2} ∘ Res_{E/F} V)^{|ν|}`, where `C(μ)` is the constant
of Fourier inversion of `ψ ∘ ⟪,⟫` for `μ` (`bicharacterFourierConstant`) and
`γ(ψ_{1/2} ∘ Res_{E/F} V)` the Weil index of `v ↦ ψ_{1/2}(tr_{E/F}(v, v))`. -/
theorem lerayScalar_eq (hE : IsQuadraticInvolution c δ) (hQ : Matrix.IsHermitianFor c Q)
    (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    (ψ : UnitaryAdditiveCharacter F) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)]
    (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] :
    lerayScalar c ψ χ Q μ =
      (((Real.sqrt (bicharacterFourierConstant μ
        fun x y => ψ.complex (hermitianTracePairing c Q x y)))⁻¹ : ℝ) : ℂ) *
        weilIndex (fun v : α → E => (ψ.scale (twoUnit F)⁻¹).complex (hermitianTraceForm c Q v v)) ^
          Fintype.card ν := by
  classical
  -- instances
  have : FiniteDimensional F E := hE.finite
  have := IsModuleTopology.isTopologicalAddGroup F E
  have : IsModuleTopology F (Matrix α ν E) := isModuleTopology_matrix F (E := E) α ν
  have := IsModuleTopology.isTopologicalAddGroup F (Matrix α ν E)
  have := t2Space_of_finiteDimensional F (Matrix α ν E)
  have := locallyCompactSpace_of_finiteDimensional F (Matrix α ν E)
  have := secondCountableTopology_of_finiteDimensional F (Matrix α ν E)
  have := compactOpenExhaustion_of_finiteDimensional F (Matrix α ν E)
  have := t2Space_of_finiteDimensional F E
  have := locallyCompactSpace_of_finiteDimensional F E
  have := secondCountableTopology_of_finiteDimensional F E
  have := compactOpenExhaustion_of_finiteDimensional F E
  have : CompactOpenExhaustion (α → E) := CompactOpenExhaustion.pi
  have : CompactOpenExhaustion (ν → α → E) := CompactOpenExhaustion.pi
  -- the Library's character `ψ' = ψ(2 ·)`
  set ψ' := (ψ.scale (twoUnit F)).complex with hψ'def
  have hψ' : Continuous ψ' := (ψ.scale (twoUnit F)).continuous_complex
  have hn' : ∀ t, ‖ψ' t‖ = 1 := (ψ.scale (twoUnit F)).norm_complex
  have h1' : ψ' ≠ 1 := (ψ.scale (twoUnit F)).complex_ne_one
  have hres' := resEtaPow_of_normResidueSign hres
  have hQ' : IsHerm c Q := ⟨hQ, hQu⟩
  have hL := isLerayWeil_lerayWeil (ν := ν) (ψ := ψ) hE hQ hQu hχ hres μ
  set κ := lerayScalar c ψ χ Q μ
  -- the character of second degree `f(x) = ψ(½ ⟪x, x⟫)`
  have hψc : ψ.complex ≠ 1 := ψ.complex_ne_one
  have he := isSelfDualBicharacter_hermitianTracePairing (ν := ν) hE hQ hQu ψ.continuous_complex
    ψ.norm_complex hψc
  obtain ⟨f, hfdef⟩ : ∃ f : Matrix α ν E → ℂ,
      f = fun x => ψ.complex ((2 : F)⁻¹ * hermitianTracePairing c Q x x) := ⟨_, rfl⟩
  have hprb : ∀ (x : Matrix α ν E) (b : Matrix ν ν E),
      ψ' (2⁻¹ * pr c Q x (x * b)) = ψ.complex (pr c Q x (x * b)) := by
    intro x b
    simp only [hψ'def, UnitaryAdditiveCharacter.complex_apply,
      UnitaryAdditiveCharacter.scale_apply, coe_twoUnit]
    rw [← mul_assoc, mul_inv_cancel₀ (two_ne_zero' F), one_mul]
  have hf1 : (fun x : Matrix α ν E => ψ' (2⁻¹ * pr c Q x (x * (1 : Matrix ν ν E)))) = f := by
    funext x
    rw [hprb, Matrix.mul_one, hfdef]
    simp only [hermitianTracePairing_eq_mul, hermitianPairing_eq_hermitianSymplecticForm]
    rw [← mul_assoc, inv_mul_cancel₀ (two_ne_zero' F), one_mul]
    rfl
  have hfm1 : (fun x : Matrix α ν E => ψ' (2⁻¹ * pr c Q x (x * (-1 : Matrix ν ν E)))) =
      fun x => starRingEnd ℂ (f x) := by
    funext x
    obtain ⟨β, hβ, -, -, -, -⟩ := pr_alg F E c δ hE α ν Q hQ'
    rw [hprb, Matrix.mul_neg, Matrix.mul_one, ← hβ, map_neg, hβ, hfdef]
    simp only [hermitianTracePairing_eq_mul, hermitianPairing_eq_hermitianSymplecticForm]
    rw [← mul_assoc, inv_mul_cancel₀ (two_ne_zero' F), one_mul, AddChar.map_neg_eq_inv,
      UnitaryAdditiveCharacter.complex_apply, UnitaryAdditiveCharacter.complex_apply,
      ← Circle.coe_inv_eq_conj]
    rfl
  have hfe : ∀ x y, f (x + y) = f x * f y * ψ.complex (hermitianTracePairing c Q x y) := by
    intro x y
    rw [hfdef]
    simp only
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    have hs : hermitianTracePairing c Q y x = hermitianTracePairing c Q x y := by
      rw [hermitianTracePairing_eq_sum, hermitianTracePairing_eq_sum]
      exact Finset.sum_congr rfl fun j _ => hermitianTraceForm_symm hE hQ hQu _ _
    simp only [map_add, LinearMap.add_apply, hs]
    ring
  have hfn : ∀ x, ‖f x‖ = 1 := fun x => by rw [hfdef]; exact ψ.norm_complex _
  have hcont : Continuous fun x : Matrix α ν E => hermitianTracePairing c Q x x := by
    have hB : Continuous fun v : α → E => hermitianTraceForm c Q v v :=
      (IsModuleTopology.continuous_bilinear_of_finite_left (hermitianTraceForm c Q)).comp
        (continuous_id.prodMk continuous_id)
    simp_rw [hermitianTracePairing_eq_sum]
    exact continuous_finsetSum _ fun j _ =>
      hB.comp (continuous_pi fun i => (continuous_apply j).comp (continuous_apply i))
  have hflc : IsLocallyConstant f := by
    rw [hfdef]
    exact (isLocallyConstant_of_continuous_addChar _ ψ.continuous_complex).comp_continuous
      (continuous_const.mul hcont)
  have hf : IsCharacterOfSecondDegree f :=
    IsCharacterOfSecondDegree.of_bicharacter he hfn hflc hfe
  have hbich : secondDegreeBicharacter f = fun x y => ψ.complex (hermitianTracePairing c Q x y) :=
    secondDegreeBicharacter_eq hf.ne_zero hfe
  -- the Gauss integrals
  obtain ⟨sc1, scmul, -⟩ := sc_basic F E c δ hE (Fintype.card α) χ hres'
  obtain ⟨γ₀, hγ₀⟩ := GaussMain.hasGauss_herm F E c δ hE α ν Q hQ' ψ' hψ' hn' h1' χ hχ hres' μ
  have hm1m : (((-1 : Matrix ν ν E)).map c)ᵀ = -1 := by
    rw [Matrix.map_neg _ (map_neg c), Matrix.map_one _ (map_zero c) (map_one c), transpose_neg,
      transpose_one]
  have hG1 : HasGaussIntegral μ f γ₀ := by
    have := hγ₀ 1 (by rw [Matrix.map_one _ (map_zero c) (map_one c), transpose_one]) (by simp)
    rwa [det_one, inv_one, sc1, mul_one, hf1] at this
  have hGm1 := hγ₀ (-1) hm1m (by simp [det_neg])
  rw [hfm1] at hGm1
  set d := (-(1 : Matrix ν ν E)).det
  have hd : d ≠ 0 := by simp [d, det_neg]
  have hconj : starRingEnd ℂ γ₀ = γ₀ * splittingScalar F χ (Fintype.card α) d⁻¹ :=
    hf.conj.hasGaussIntegral_unique μ (HasGaussIntegral.conj hG1) hGm1
  have hκγ : κ * γ₀ = splittingScalar F χ (Fintype.card α) d := by
    have := mul_gaussIntegral_eq hE hQ' hψ' hn' h1' hχ hres' hL (by rwa [hf1])
    rwa [inv_one] at this
  have hsd : splittingScalar F χ (Fintype.card α) d * splittingScalar F χ (Fintype.card α) d⁻¹ =
      1 := by rw [← scmul, mul_inv_cancel₀ hd, sc1]
  have hmod := hf.hasGaussIntegral_mul_conj μ hG1
  rw [hbich] at hmod
  set C := bicharacterFourierConstant μ fun x y => ψ.complex (hermitianTracePairing c Q x y)
  have hC : 0 < C := bicharacterFourierConstant_pos _ _
  -- `κ C = γ₀`
  have hκC : κ * (C : ℂ) = γ₀ := by
    linear_combination (-κ) * hmod + starRingEnd ℂ γ₀ * hκγ +
      splittingScalar F χ (Fintype.card α) d * hconj + γ₀ * hsd
  have hγw : γ₀ = (Real.sqrt C : ℂ) * weilIndex f := by
    have := hasGaussIntegral_weilIndex hf μ
    rw [hbich] at this
    exact hf.hasGaussIntegral_unique μ hG1 this
  -- `γ(f) = γ(ψ_{1/2} ∘ Res V)^{|ν|}`
  set fV : (α → E) → ℂ := fun v => (ψ.scale (twoUnit F)⁻¹).complex (hermitianTraceForm c Q v v)
  have hfV' : fV = fun v => ψ.complex ((2 : F)⁻¹ * hermitianTraceForm c Q v v) := by
    funext v
    simp [fV, UnitaryAdditiveCharacter.scale_apply, coe_twoUnit]
  have hfV : IsCharacterOfSecondDegree fV := by
    rw [hfV']
    exact isCharacterOfSecondDegree_hermitianTraceForm hE hQ hQu ψ.continuous_complex
      ψ.norm_complex hψc
  let T : Matrix α ν E ≃ₜ+ (ν → α → E) :=
    { toFun := fun x j i => x i j
      invFun := fun y i j => y j i
      left_inv := fun x => rfl
      right_inv := fun y => rfl
      map_add' := fun x y => rfl
      continuous_toFun := continuous_pi fun j => continuous_pi fun i =>
        (continuous_apply j).comp (continuous_apply i)
      continuous_invFun := continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply i).comp (continuous_apply j) }
  have hfT : f = fun x => (fun y : ν → α → E => ∏ j, fV (y j)) (T x) := by
    funext x
    rw [hfdef, hfV']
    dsimp only
    rw [hermitianTracePairing_eq_sum, Finset.mul_sum, addChar_sum]
    rfl
  have hw : weilIndex f = weilIndex fV ^ Fintype.card ν := by
    rw [hfT, weilIndex_comp_addEquiv (IsCharacterOfSecondDegree.pi fun _ => hfV) T,
      weilIndex_pi fun _ => hfV, Finset.prod_const, Finset.card_univ]
  -- conclusion
  rw [← hw]
  have hsq : (Real.sqrt C : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hC).ne'
  have hCC : (C : ℂ) = (Real.sqrt C : ℂ) * (Real.sqrt C : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hC.le]
  rw [hγw, hCC] at hκC
  push_cast
  rw [eq_inv_mul_iff_mul_eq₀ hsq]
  exact mul_left_cancel₀ hsq (by linear_combination hκC)

/-- **The scalar at the Weyl element for the self-dual measure** (GKT Proposition 12.29, Case `3₊`,
with the measure `d𝐱` of Proposition 12.27 (1) the self-dual one):
`lerayScalar c ψ χ Q μ_sd = γ(ψ_{1/2} ∘ Res_{E/F} V)^{|ν|}`, the book's `β(w)`, a Weil index. -/
theorem lerayScalar_selfDualMeasure (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    (ψ : UnitaryAdditiveCharacter F) [MeasurableSpace (Matrix α ν E)]
    [BorelSpace (Matrix α ν E)] :
    lerayScalar c ψ χ Q
        (selfDualMeasure fun x y : Matrix α ν E => ψ.complex (hermitianTracePairing c Q x y)) =
      weilIndex (fun v : α → E => (ψ.scale (twoUnit F)⁻¹).complex (hermitianTraceForm c Q v v)) ^
        Fintype.card ν := by
  have : FiniteDimensional F E := hE.finite
  have : IsModuleTopology F (Matrix α ν E) := isModuleTopology_matrix F (E := E) α ν
  have := IsModuleTopology.isTopologicalAddGroup F (Matrix α ν E)
  have := locallyCompactSpace_of_finiteDimensional F (Matrix α ν E)
  have := secondCountableTopology_of_finiteDimensional F (Matrix α ν E)
  have := compactOpenExhaustion_of_finiteDimensional F (Matrix α ν E)
  have he := isSelfDualBicharacter_hermitianTracePairing (ν := ν) hE hQ hQu ψ.continuous_complex
    ψ.norm_complex ψ.complex_ne_one
  have := isAddHaarMeasure_selfDualMeasure he
  rw [lerayScalar_eq (ν := ν) hE hQ hQu hχ hres ψ, bicharacterFourierConstant_selfDualMeasure he,
    Real.sqrt_one, inv_one, Complex.ofReal_one, one_mul]

/-- **The Weyl element acts by the Weil index times the self-dual Fourier transform** (GKT
Proposition 12.27 (1), third formula, with Proposition 12.29):
`ω(w) φ(x) = γ(ψ_{1/2} ∘ Res_{E/F} V)^{|ν|} ∫ ψ(⟪x, y⟫) φ(y) d𝐱(y)`, `d𝐱` the self-dual measure of
`ψ ∘ ⟪,⟫`. -/
theorem lerayWeil_weylElement_apply_selfDualMeasure (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    (ψ : UnitaryAdditiveCharacter F) [MeasurableSpace (Matrix α ν E)]
    [BorelSpace (Matrix α ν E)] (φ : SchwartzBruhat (Matrix α ν E)) (x : Matrix α ν E) :
    (lerayWeil c ν ψ χ Q (weylElement c ν) φ : Matrix α ν E → ℂ) x =
      weilIndex (fun v : α → E => (ψ.scale (twoUnit F)⁻¹).complex (hermitianTraceForm c Q v v)) ^
          Fintype.card ν *
        ∫ y, (ψ (hermitianTracePairing c Q x y) : ℂ) * (φ : Matrix α ν E → ℂ) y
          ∂(selfDualMeasure fun x y : Matrix α ν E =>
            ψ.complex (hermitianTracePairing c Q x y)) := by
  have : FiniteDimensional F E := hE.finite
  have : IsModuleTopology F (Matrix α ν E) := isModuleTopology_matrix F (E := E) α ν
  have := IsModuleTopology.isTopologicalAddGroup F (Matrix α ν E)
  have := locallyCompactSpace_of_finiteDimensional F (Matrix α ν E)
  have := secondCountableTopology_of_finiteDimensional F (Matrix α ν E)
  have := compactOpenExhaustion_of_finiteDimensional F (Matrix α ν E)
  have he := isSelfDualBicharacter_hermitianTracePairing (ν := ν) hE hQ hQu ψ.continuous_complex
    ψ.norm_complex ψ.complex_ne_one
  have := isAddHaarMeasure_selfDualMeasure he
  rw [lerayWeil_weylElement_apply hE hQ hQu hχ hres
      (selfDualMeasure fun x y : Matrix α ν E => ψ.complex (hermitianTracePairing c Q x y)) φ x,
    lerayScalar_selfDualMeasure (ν := ν) hE hQ hQu hχ hres ψ]

/-- **The definite form of the Leray splitting's formulas** (the scalar of `exists_isLerayWeil` is
a value, not an existential): for every Haar measure `μ`, `lerayWeil` is `IsLerayWeil` for the
Library's character `ψ(2 ·)` with the scalar `C(μ)^{-1/2} γ(ψ_{1/2} ∘ Res_{E/F} V)^{|ν|}`. -/
theorem isLerayWeil_weilIndex (hE : IsQuadraticInvolution c δ) (hQ : Matrix.IsHermitianFor c Q)
    (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    (ψ : UnitaryAdditiveCharacter F) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)]
    (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] :
    IsLerayWeil c (ψ.scale (twoUnit F)).complex χ Q μ
      ((((Real.sqrt (bicharacterFourierConstant μ
        fun x y => ψ.complex (hermitianTracePairing c Q x y)))⁻¹ : ℝ) : ℂ) *
        weilIndex (fun v : α → E => (ψ.scale (twoUnit F)⁻¹).complex (hermitianTraceForm c Q v v)) ^
          Fintype.card ν)
      (lerayWeil c ν ψ χ Q) := by
  rw [← lerayScalar_eq (ν := ν) hE hQ hQu hχ hres ψ μ]
  exact isLerayWeil_lerayWeil hE hQ hQu hχ hres μ

end Scalar

end Langlands.Theta
