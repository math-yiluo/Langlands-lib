import Langlands.Global.AdelicBlockCompactTensorFiniteAction
import Langlands.Global.AdelicBlockCompactTensorSmooth
import Langlands.Global.AdelicBlockInfiniteMultiplicity
import Langlands.Representation.Archimedean.CompactPolynomialOrbit
import Langlands.Representation.TensorProduct.MultiplicityCancellation

/-! # Realized scalar sections from a compact polynomial seed -/

noncomputable section

open scoped Classical ContDiff Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 950000
set_option maxRecDepth 4000

universe u

namespace Langlands.Global.AdelicBlockScalarSections

open Automorphic GeneralLinear AdelicBlockParabolic AdelicBlockDeterminantCharacter
open PrimitiveAdelicHeight ArchimedeanGL Langlands.Archimedean

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
variable (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))
variable {A V U : Type u}
variable [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
variable (ρ : Representation ℂ (FiniteAdelicGL F n) A)
variable (ef : FiniteAdelicGL F n → A →ₗ[ℂ] V)
variable (e : V ⊗[ℂ] U →ₗ[ℂ] coefficientValues F B S)
variable (τ : Representation ℂ (infiniteCompactIntersection F B) U)
variable (seed : MultiplicityCompactPolynomial (V := U) (infiniteCompactMatrixInclusion F B) τ)

local notation "G" => FiniteAdelicGL F n
local notation "K" => standardCompact F n
local notation "KI" => standardInfiniteCompact F n
local notation "KF" => FiniteAdelicGL.standardIntegral F n
local notation "W" => smoothCompactFiniteSections F B S
local notation "C" => coefficientValues F B S
local notation "L" => FullLevi F B
local notation "R" => ArchimedeanMatrix F n
local notation "H" => infiniteCompactIntersection F B

local instance seedCompactFiniteGroup : AddCommGroup (FiniteSmoothRealizedSections F B S) :=
  Submodule.addCommGroup _
local instance seedCompactSmoothGroup : AddCommGroup W := Submodule.addCommGroup _

variable (hr : ∀ (d g : FiniteAdelicGL F n) (a : A), ef g (ρ d a) = ef (g * d) a)
variable (hl : ∀ (p : AdelicBlockParabolic.Finite F B) (g : FiniteAdelicGL F n)
    (a : A) (w : U) (m : FullLevi F B),
  (e (ef (p.val * g) a ⊗ₜ[ℂ] w)).val m = (parabolicHalfCharacter F B (ofFinite F B p) : ℂ) *
    (e (ef g a ⊗ₜ[ℂ] w)).val (m * leviPair F B 1 (B.leviProjection (FiniteAdeles F) p)))
variable (hi : ∀ (p : infiniteCompactIntersection F B) (v : V) (w : U) (m : FullLevi F B),
    (e (v ⊗ₜ[ℂ] τ p w)).val m =
      (e (v ⊗ₜ[ℂ] w)).val (m * leviPair F B (B.leviProjection (InfiniteAdeles F) p.val) 1))

private abbrev compactUnits (n : ℕ) : standardInfiniteCompact F n →* (ArchimedeanMatrix F n)ˣ :=
  (archimedeanGLCoordinates F n).toMonoidHom.comp (standardInfiniteCompact F n).subtype

/-- The subrepresentation spanned by the right translates of the infinite seed
polynomial under the standard infinite compact group, acting through its
archimedean matrix coordinates. -/
abbrev polynomialOrbit :
    Subrepresentation (matrixRightTranslation (V := Fin seed.dimension → ℂ) (compactUnits F n)) :=
  FiniteVectors.orbitSubrepresentation
    (matrixRightTranslation (compactUnits F n)) seed.polynomial

set_option quotPrecheck false in
local notation "O" => (polynomialOrbit F B τ seed).toSubmodule
local instance polynomialOrbitGroup : AddCommGroup O := Submodule.addCommGroup _

private def polynomialEvaluate (a : KI) : O →ₗ[ℂ] U :=
  seed.inclusion.comp ((LinearMap.proj (compactMatrix F a)).comp (O).subtype)

private theorem polynomialEvaluate_compact (p : H) (k : KI) (b : O) :
    polynomialEvaluate F B τ seed (⟨p.val.val, p.property⟩ * k) b =
      τ p (polynomialEvaluate F B τ seed k b) := by
  have he : compactMatrix F (⟨p.val.val, p.property⟩ * k) =
      (infiniteCompactMatrixInclusion F B p).val * compactMatrix F k := by
    change (archimedeanGLCoordinates F n (p.val.val * k.val)).val = _
    rw [map_mul, Units.val_mul]
    rfl
  change seed.inclusion (b.val (compactMatrix F (⟨p.val.val, p.property⟩ * k))) = _
  rw [he]
  exact matrixRightTranslation_orbitSpan_covariant (compactUnits F n) seed.polynomial
    seed.inclusion (infiniteCompactMatrixInclusion F B p).val (τ p) (seed.covariance p)
    b.property (compactMatrix F k)

private theorem polynomialEvaluate_right (k l : KI) (b : O) :
    polynomialEvaluate F B τ seed k ((polynomialOrbit F B τ seed).toRepresentation l b) =
      polynomialEvaluate F B τ seed (k * l) b := by
  change seed.inclusion (b.val (compactMatrix F k * compactMatrix F l)) =
    seed.inclusion (b.val (compactMatrix F (k * l)))
  have h : compactMatrix F (k * l) = compactMatrix F k * compactMatrix F l := by
    simp only [compactMatrix, Subgroup.coe_mul, map_mul, Units.val_mul]
  rw [h]

local notation "efK" => fun l : KF => ef (Subtype.val l)
local notation "ei" => polynomialEvaluate F B τ seed

include hl hi in
private theorem compactTensorValue_polynomial_covariance
    (p : compactIntersection B F) (k : K) (m : L) (a : A) (b : O) :
    (compactTensorValue F B C efK ei e (⟨p.val.val, p.property⟩ * k) (a ⊗ₜ[ℂ] b)).val m =
      (compactTensorValue F B C efK ei e k (a ⊗ₜ[ℂ] b)).val (m * B.leviProjection (Adeles F) p.val) := by
  let x := compactIntersectionProductEquiv F B p
  let pI : KI := ⟨x.1.val.val, x.1.property⟩
  let pF : KF := ⟨x.2.val.val, x.2.property⟩
  let z := standardCompactProductEquiv F n k
  let mI := leviPair F B (B.leviProjection (InfiniteAdeles F) x.1.val) 1
  let mF := leviPair F B 1 (B.leviProjection (FiniteAdeles F) x.2.val)
  have hpair : standardCompactProductEquiv F n (⟨p.val.val, p.property⟩ * k) = (pI * z.1, pF * z.2) := by
    rw [map_mul, standardCompactProductEquiv_compactIntersection]
    rfl
  have hδ : (parabolicHalfCharacter F B (ofFinite F B x.2.val) : ℂ) = 1 := by
    have hm : (ofFinite F B x.2.val).val ∈ standardCompact F n := (compactPair F 1 pF).property
    rw [parabolicHalfCharacter_eq_one_of_mem_standardCompact B F _ hm, Units.val_one]
  have hp : pair F B x.1.val x.2.val = p.val := by
    exact congrArg Subtype.val ((compactIntersectionProductEquiv F B).symm_apply_apply p)
  have hproj : mI * mF = B.leviProjection (Adeles F) p.val := by
    rw [← hp, leviProjection_pair]
    funext i
    change AdelicGL.pair F (B.size i) (B.leviProjection (InfiniteAdeles F) x.1.val i) 1 *
      AdelicGL.pair F (B.size i) 1 (B.leviProjection (FiniteAdeles F) x.2.val i) = _
    rw [AdelicGL.pair_mul, mul_one, one_mul]
    rfl
  rw [compactTensorValue_tmul, compactTensorValue_tmul, hpair]
  change (e (ef (pF.val * z.2.val) a ⊗ₜ[ℂ] ei (pI * z.1) b)).val m = _
  rw [polynomialEvaluate_compact F B τ seed x.1 z.1 b, hi, hl x.2.val, hδ, one_mul]
  change (e (ef z.2.val a ⊗ₜ[ℂ] ei z.1 b)).val ((m * mI) * mF) = _
  rw [mul_assoc, hproj]

private theorem compactPolynomial_smooth (a : A) (b : O) (k : KI) (l : KF) (m : L) :
    ∃ φ : R → ℂ, ContDiffAt ℝ ∞ φ (compactMatrix F k) ∧
      ∀ᶠ x in nhds (compactMatrix F k), ∀ h : KI, compactMatrix F h = x →
        φ x = (e (ef l.val a ⊗ₜ[ℂ] ei h b)).val m := by
  let Q : (Fin seed.dimension → ℂ) →ₗ[ℂ] ℂ := (LinearMap.proj m).comp ((C).subtype.comp
    (e.comp (((TensorProduct.mk ℂ V U) (ef l.val a)).comp seed.inclusion)))
  let Q' := (Q.toContinuousLinearMap).restrictScalars ℝ
  have hb : ContDiff ℝ ∞ b.val := contDiff_of_mem_matrixRightTranslation_orbitSpan
    (compactUnits F n) seed.polynomial (contDiff_of_mem_vectorCoordinatePolynomials seed.polynomial_mem)
      b.property
  refine ⟨fun x => Q' (b.val x), (Q'.contDiff.comp hb).contDiffAt, Filter.Eventually.of_forall ?_⟩
  intro x h hx
  change Q' (b.val x) = Q' (b.val (compactMatrix F h))
  rw [hx]

include hr hl hi in
/-- A covariant compact polynomial seed and faithful finite evaluations give
nonzero actual smooth scalar sections with the prescribed compact slices. -/
theorem exists_smoothSectionFamily_of_compactPolynomial
    (hρ : IsSmooth ρ) (he : Function.Injective e) (hn : ∃ (a : A) (l : KF), ef l.val a ≠ 0) :
    ∃ f : A → W,
      (∀ (a : A) (k : KI) (l : KF) (m : L),
        normalizedSlice F B (f a).val.val.val (compactPair F k l) m =
          (e (ef l.val a ⊗ₜ[ℂ] seed.inclusion (seed.polynomial (compactMatrix F k)))).val m) ∧
      ∃ a, f a ≠ 0 := by
  let cov := compactTensorValue_polynomial_covariance F B S ef e τ seed hl hi
  let j := compactTensorSectionMap F B C efK ei e cov
  let b : O := ⟨seed.polynomial, FiniteVectors.self_mem_orbitSpan _ _⟩
  let κ := (polynomialOrbit F B τ seed).toRepresentation
  let : FiniteDimensional ℂ O := matrixRightTranslation_isFiniteVector (compactUnits F n)
    seed.polynomial seed.polynomial_mem
  have hκ (x : O) : FiniteVectors.IsFiniteVector κ x :=
    FiniteVectors.isFiniteVector_of_mem κ ⊤ (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ O))
  have hs (t : A ⊗[ℂ] O) : IsSmoothVector (RealizedSections.finiteAction F B S) (j t) :=
    (finiteSmoothTensorSectionIntertwiner F B S ef ei e cov ρ hr hl hρ t).property
  let J := smoothCompactTensorSectionIntertwiner F B S efK ei e cov
    (compactPolynomial_smooth F B S ef e τ seed) κ (fun l k x => polynomialEvaluate_right F B τ seed k l x)
    hs hκ
  let f (a : A) : W := J (a ⊗ₜ[ℂ] b)
  have hf (a : A) (k : KI) (l : KF) (m : L) :
      normalizedSlice F B (f a).val.val.val (compactPair F k l) m =
        (e (ef l.val a ⊗ₜ[ℂ] seed.inclusion (seed.polynomial (compactMatrix F k)))).val m := by
    change normalizedSlice F B (j (a ⊗ₜ[ℂ] b)).val (compactPair F k l) m = _
    rw [normalizedSlice_compactTensorSectionMap, compactTensorValue_tmul]
    have h : standardCompactProductEquiv F n (compactPair F k l) = (k, l) :=
      (standardCompactProductEquiv F n).apply_symm_apply (k, l)
    rw [h]
    rfl
  refine ⟨f, hf, ?_⟩
  obtain ⟨a, l, hal⟩ := hn
  refine ⟨a, fun h => ?_⟩
  have hk : compactMatrix F (1 : KI) = 1 := by
    simp only [compactMatrix, Subgroup.coe_one, map_one, Units.val_one]
  have hz : e (ef l.val a ⊗ₜ[ℂ] seed.inclusion (seed.polynomial 1)) = 0 := by
    apply Subtype.ext
    funext m
    have hval := hf a 1 l m
    rw [h, hk] at hval
    exact hval.symm.trans (by simp [normalizedSlice])
  exact TensorMultiplicity.tmul_ne_zero hal seed.value_one_ne_zero
    (he (hz.trans (map_zero e).symm))

end Langlands.Global.AdelicBlockScalarSections
