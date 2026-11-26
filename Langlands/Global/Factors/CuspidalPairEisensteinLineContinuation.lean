import Langlands.Global.Factors.CuspidalPairEisensteinConvergence
import Langlands.Global.AdelicEisensteinLineContinuation

/-! # The cuspidal-pair Eisenstein series along Shahidi's line, from the general continuation

The meromorphic continuation of Eisenstein series (`EisensteinMeromorphicContinuationStatement`)
and its joint root-hyperplane form (`EisensteinJointRootHyperplaneStatement`), in the universe of
the number field, give the first two clauses of `CuspidalPairEisensteinJointContinuationStatement`
for every section of a cuspidal pair, and its third clause whenever the group-scheme Eisenstein
series of the transported section has `EisensteinLine.HasImaginaryAxisHolomorphy`. See the paired
Markdown. -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry NumberField TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairEisenstein

open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
open AdelicBlockEisensteinGeometry AdelicGroupPoints GeneralLinearGroupPoints
open Langlands.Automorphic.GroupSchemeFunctions PrimitiveAdelicHeight

section Line

variable (F : Type u) [Field F] [NumberField F] (r t : ℕ)

local notation "D" => blockRootData F (blockShape r t)

local instance lineContTorusMono : Mono (D).root.data.i.hom.hom.left := (D).torus_mono

local instance lineContFactorMono :
    Mono (CommGroupScheme.groupHom (D).root.data.f).hom.hom.left := (D).factor_mono

local instance lineContWeylFinite : Fintype (relativeWeylGroup (D).root.data.i) :=
  @Fintype.ofFinite _ (D).finite_weylGroup

omit [NumberField F] in
/-- The complex root form of a root `β` at `λ₁` is the real root form at the real part of `λ₁`:
`λ₁` has real coefficients. -/
theorem rootFunctional_lineParameter (β : characterLattice (D).A) :
    (D).root.rootFunctional (D).splitComponent (D).splitTorus β (lineParameter F r t) =
      ((D).root.realRootFunctional (D).splitComponent (D).splitTorus β
        (parameterRealPart F _ (lineParameter F r t)) : ℂ) := by
  have key : ∀ (c : ℝ) (χ : GroupScheme.rationalCharacters
      (blockParabolicScheme (Fin (r + t + 2)) (CommRingCat.of F)
        (blockShapeWeight (blockShape r t)))),
      (D).root.rootFunctional (D).splitComponent (D).splitTorus β ((c : ℂ) ⊗ₜ[ℤ] χ) =
        ((D).root.realRootFunctional (D).splitComponent (D).splitTorus β
          (parameterRealPart F _ ((c : ℂ) ⊗ₜ[ℤ] χ)) : ℂ) := by
    intro c χ
    rw [ParabolicRootPresentation.rootFunctional_tmul, parameterRealPart_tmul, Complex.ofReal_re]
    have : (c ⊗ₜ[ℤ] χ : RealCharacterParameter F _) = c • ((1 : ℝ) ⊗ₜ[ℤ] χ) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul, Complex.ofReal_mul]
  have h0 : (((t + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ)) =
      (((t + 1 : ℕ) / (r + t + 2 : ℕ) : ℝ) : ℂ) := by push_cast; ring
  have h1 : (-(((r + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ))) =
      ((-((r + 1 : ℕ) / (r + t + 2 : ℕ)) : ℝ) : ℂ) := by push_cast; ring
  rw [lineParameter, h0, h1, map_add, key, key, map_add, map_add, Complex.ofReal_add]

omit [NumberField F] in
/-- Every root form of a root of the split component in the unipotent radical is nonzero at
`λ₁`. -/
theorem rootFunctional_lineParameter_ne_zero {β : characterLattice (D).A}
    (hβ : β ∈ (D).root.unipotentRoots) :
    (D).root.rootFunctional (D).splitComponent (D).splitTorus β (lineParameter F r t) ≠ 0 := by
  rw [rootFunctional_lineParameter, Complex.ofReal_ne_zero]
  exact (weylInducedCharacterForm_lineRestriction_pos F r t hβ).ne'

omit [NumberField F] in
/-- For `Re s = 0` the parameter `s λ₁` is imaginary. -/
theorem smul_lineParameter_mem_range_imaginaryParameter {s : ℂ} (hs : s.re = 0) :
    s • lineParameter F r t ∈ Set.range (imaginaryParameter F
      (blockParabolicScheme (Fin (r + t + 2)) (CommRingCat.of F)
        (blockShapeWeight (blockShape r t)))) := by
  have hsI : s = (s.im : ℂ) * Complex.I := Complex.ext (by simp [hs]) (by simp)
  refine ⟨(s.im * ((t + 1 : ℕ) / (r + t + 2 : ℕ) : ℝ)) ⊗ₜ[ℤ]
      parabolicBlockCharacter (blockShape r t) (CommRingCat.of F) (firstBlock r t) +
    (s.im * (-((r + 1 : ℕ) / (r + t + 2 : ℕ)) : ℝ)) ⊗ₜ[ℤ]
      parabolicBlockCharacter (blockShape r t) (CommRingCat.of F) (secondBlock r t), ?_⟩
  rw [map_add, imaginaryParameter, AlgebraTensorModule.map_tmul, AlgebraTensorModule.map_tmul,
    lineParameter, smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  simp only [LinearMap.toSpanSingleton_apply, LinearMap.id_coe, id_eq, smul_eq_mul]
  congr 2
  · rw [Complex.real_smul]; conv_rhs => rw [hsI]
    push_cast; ring
  · rw [Complex.real_smul]; conv_rhs => rw [hsI]
    push_cast; ring

end Line

section Reduction

local instance lineRedGLAffine {F : Type u} [Field F] (n : ℕ) :
    IsAffine (groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance lineRedGLAffineHom {F : Type u} [Field F] (n : ℕ) :
    IsAffineHom (groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  isAffineHom_groupScheme (n := Fin n) (R := CommRingCat.of F)

local instance lineRedParabolicAffine {F : Type u} [Field F] {r t : ℕ} :
    IsAffine (blockParabolicScheme (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t))).X.left :=
  blockParabolic_isAffine F (blockShape r t)

local instance lineRedParabolicClosed {F : Type u} [Field F] {r t : ℕ} :
    IsClosedImmersion (blockParabolicHom (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t))).hom.hom.left :=
  isClosedSubgroup_blockParabolicHom (Fin (r + t + 2)) (CommRingCat.of F)
    (blockShapeWeight (blockShape r t))

local instance lineRedTorusMono {F : Type u} [Field F] [NumberField F] {r t : ℕ} :
    Mono (blockRootData F (blockShape r t)).root.data.i.hom.hom.left :=
  (blockRootData F (blockShape r t)).torus_mono

local instance lineRedFactorMono {F : Type u} [Field F] [NumberField F] {r t : ℕ} :
    Mono (CommGroupScheme.groupHom (blockRootData F (blockShape r t)).root.data.f).hom.hom.left :=
  (blockRootData F (blockShape r t)).factor_mono

local instance lineRedWeylFinite {F : Type u} [Field F] [NumberField F] {r t : ℕ} :
    Fintype (relativeWeylGroup (blockRootData F (blockShape r t)).root.data.i) :=
  @Fintype.ofFinite _ (blockRootData F (blockShape r t)).finite_weylGroup

/-- **Shahidi's line from the general continuation.** Assume the meromorphic continuation of
Eisenstein series (`EisensteinMeromorphicContinuationStatement`) and its joint root-hyperplane
form (`EisensteinJointRootHyperplaneStatement`) for number fields in the universe `u`. Let
`F : Type u` be a number field with compact adele quotient, `T`, `T'` actual cuspidal
realizations and `φ` a section of the cuspidal pair (`IsSection T T' φ`). Then there are
`E : ℂ → GL_N(𝔸) → ℂ` and `σ` such that

* `E s` is the actual Eisenstein sum `eisensteinSeries F φ s` for `σ < Re s`;
* near every `s₀` there are an exponent `m`, an open `W ∋ s₀` and a function `h` of `(s, g)`,
  continuous on `W × GL_N(𝔸)`, holomorphic in `s ∈ W`, left `GL_N(F)`-invariant in `g`, with
  `h s g = (s - s₀)^m E s g` for `s ∈ W`, `s ≠ s₀`;
* if moreover the group-scheme Eisenstein series of the transported section `φ ∘ adelicHomeomorph`
  for the block parabolic has `EisensteinLine.HasImaginaryAxisHolomorphy`, then for `Re s₀ = 0`
  one can take `m = 0`, and then also `h s₀ = E s₀`. -/
def CuspidalPairEisensteinLineReductionStatement : Prop :=
  EisensteinMeromorphicContinuationStatement.{u} → EisensteinJointRootHyperplaneStatement.{u} →
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r t : ℕ)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t) (φ : AdelicGL F (r + t + 2) → ℂ),
    IsSection T T' φ →
    ∃ (E : ℂ → AdelicGL F (r + t + 2) → ℂ) (σ : ℝ),
      (∀ s : ℂ, σ < s.re → E s = eisensteinSeries F (r := r) (t := t) φ s) ∧
      ∀ s₀ : ℂ, ∃ (m : ℕ) (W : Set ℂ) (h : ℂ → AdelicGL F (r + t + 2) → ℂ),
        IsOpen W ∧ s₀ ∈ W ∧
        ContinuousOn (fun q : ℂ × AdelicGL F (r + t + 2) => h q.1 q.2) (W ×ˢ Set.univ) ∧
        (∀ g, DifferentiableOn ℂ (fun s => h s g) W) ∧
        (∀ s ∈ W, ∀ (x : RationalGL F (r + t + 2)) (g : AdelicGL F (r + t + 2)),
          h s (AdelicGL.rational F (r + t + 2) x * g) = h s g) ∧
        (∀ s ∈ W, s ≠ s₀ → ∀ g, h s g = (s - s₀) ^ m * E s g) ∧
        (EisensteinLine.HasImaginaryAxisHolomorphy (blockRootData F (blockShape r t)).root
            (blockRootData F (blockShape r t)).splitComponent
            (blockRootData F (blockShape r t)).splitTorus
            (isIwasawaCompact_blockParabolic F (blockShape r t))
            (φ ∘ adelicHomeomorph F (r + t + 2)) →
          s₀.re = 0 → m = 0 ∧ ∀ g, h s₀ g = E s₀ g)

theorem cuspidalPairEisensteinLineReduction : CuspidalPairEisensteinLineReductionStatement.{u} := by
  intro hMero hJoint F _ _ _ r t T T' φ hφ
  have hG := isConnectedReductive_generalLinear F (Fin (r + t + 2))
  have hs := hG.smoothDimension_spec
  have hc := adelicDifferentialCommutator_of_smooth F
    (groupScheme (Fin (r + t + 2)) (CommRingCat.of F)) hs
  have hrho : IsClosedSubgroup (MatrixRepresentation.standard (Fin (r + t + 2))
      (CommRingCat.of F)) := by
    change IsClosedImmersion (𝟙 (groupScheme (Fin (r + t + 2)) (CommRingCat.of F)).X.left)
    infer_instance
  let eG := adelicHomeomorph F (r + t + 2)
  obtain ⟨E, σ, h1, h2⟩ := EisensteinLine.exists_lineContinuation_imaginary
    (blockRootData F (blockShape r t)).root (blockRootData F (blockShape r t)).splitComponent
    (blockRootData F (blockShape r t)).splitTorus
    (isIwasawaCompact_blockParabolic F (blockShape r t)) hMero hJoint hG
    (blockUnipotentInclusion_isLeviGeometricUnipotentRadical F (blockShape r t))
    (MatrixRepresentation.standard (Fin (r + t + 2)) (CommRingCat.of F)) (by omega) hrho hs hc
    (standardCompactPoints_isMaximalCompact F (r + t + 2)) (φ ∘ eG)
    (isAutomorphicFunctionOn_of_isSection hφ hs hc) (lineParameter F r t)
    (fun β hβ => rootFunctional_lineParameter_ne_zero F r t hβ)
    (fun R => exists_isRegularParameter_lineParameter F r t R)
  refine ⟨fun s g => E s (eG.symm g), σ, fun s hs => funext fun g => ?_, fun s₀ => ?_⟩
  · simp only [h1 s hs]
    rw [← eisensteinSeries_eq_schemeEisensteinSeries hφ s (eG.symm g)]
    simp only [eG, ContinuousMulEquiv.apply_symm_apply]
  obtain ⟨m, W, h, hW, hs₀, hcont, hd, hinv, heq, him⟩ := h2 s₀
  refine ⟨m, W, fun s g => h s (eG.symm g), hW, hs₀, ?_, fun g => hd (eG.symm g), ?_,
    fun s hs hne g => heq s hs hne (eG.symm g), fun hIm hre => ?_⟩
  · exact hcont.comp (continuous_fst.prodMk (eG.symm.continuous.comp continuous_snd)).continuousOn
      fun q hq => ⟨hq.1, Set.mem_univ _⟩
  · intro s hs x g
    let c0 := (rationalPointsEquiv F r t).symm x
    have hx : AdelicGL.rational F (r + t + 2) x = eG c0.val := by
      rw [← rational_rationalPointsEquiv, MulEquiv.apply_symm_apply]
    change h s (eG.symm (AdelicGL.rational F (r + t + 2) x * g)) = h s (eG.symm g)
    rw [hx, map_mul, ContinuousMulEquiv.symm_apply_apply]
    exact hinv s hs c0.val c0.property (eG.symm g)
  · obtain ⟨hm, hh⟩ := him hIm (smul_lineParameter_mem_range_imaginaryParameter F r t hre)
    exact ⟨hm, fun g => hh (eG.symm g)⟩

end Reduction

end Langlands.Global.CuspidalPairEisenstein
