import Langlands.Automorphic.CuspidalFiniteInfiniteDecomposition
import Langlands.Global.AdelicBlockCoefficientTensor
import Langlands.Global.AdelicBlockInfiniteCompactSections
import Langlands.Global.EisensteinEvaluationMatrix
import Langlands.Representation.Tensor.ExternalSubquotient

/-! # Compact polynomial seeds in the actual inducing multiplicities -/

noncomputable section

open NumberField
open scoped Classical BigOperators TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 100000

universe u

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic
open Langlands.GeneralLinear (BlockShape)
open AdelicBlockParabolic PrimitiveAdelicHeight ArchimedeanGL EisensteinJet

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

local instance infiniteMultiplicityRationalGroup (t : ℕ) :
    AddCommGroup (RationalInvariantFunctions F t) := Submodule.addCommGroup _
local instance infiniteMultiplicityContinuousGroup (t : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F t) := Submodule.addCommGroup _
local instance infiniteMultiplicitySmoothGroup (t : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F t) := Submodule.addCommGroup _
local instance infiniteMultiplicityFormsGroup (t : ℕ) :
    AddCommGroup (AutomorphicForms F t) := Submodule.addCommGroup _
local instance infiniteMultiplicityStableGroup (t : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F t) := Submodule.addCommGroup _
local instance infiniteMultiplicityOperatorGroup {t : ℕ} (P : OperatorRealization F t) :
    AddCommGroup P.Space := Submodule.addCommGroup _

variable (M : ∀ i, Subrepresentation (S i).finiteRepresentation)

local instance infiniteMultiplicityFiniteGroup (i : Fin B.length) :
    AddCommGroup (M i).toSubmodule := Submodule.addCommGroup _

local notation "H" => infiniteCompactIntersection F B
local notation "J" => fun i : Fin B.length => OperatorRealization.FiniteMultiplicity (S i) (M i)
local notation "C" => (⨂[ℂ] i, J i)
local notation "κ" => fun i : Fin B.length => OperatorRealization.finiteMultiplicityCompact (S i) (M i)
local notation "A" => ArchimedeanMatrix F n
local notation "projection" => infiniteCompactLeviProjection F B

/-- The actual infinite compact parabolic acts on the tensor of the infinite
multiplicities through its Levi projection. -/
def infiniteMultiplicityCompactAction : Representation ℂ H C :=
  (FiniteTensor.external κ).comp (projection).toMonoidHom

private theorem continuous_coefficientEvaluation (t : ⨂[ℂ] i, (S i).Space) :
    Continuous (coefficientEvaluation F B S t) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c t =>
    rw [map_smul, coefficientEvaluation_tprod]
    exact continuous_const.mul (continuous_finsetProd _ fun i _ =>
      (ContinuousRationalFunctions.continuous_evaluate F (B.size i) ((S i).toContinuous (t i))).comp
        (continuous_apply i))
  | add t s ht hs =>
    rw [map_add]
    exact ht.add hs

private theorem piTensor_map_injective {ι : Type*} {U V : ι → Type*}
    [∀ i, AddCommGroup (U i)] [∀ i, Module ℂ (U i)]
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (f : ∀ i, U i →ₗ[ℂ] V i) (hf : ∀ i, Function.Injective (f i)) :
    Function.Injective (PiTensorProduct.map f) := by
  choose g hg using fun i => (f i).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (hf i))
  apply Function.LeftInverse.injective (g := PiTensorProduct.map g)
  intro t
  have he : (fun i => (g i).comp (f i)) = fun i => LinearMap.id := funext hg
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp, he, PiTensorProduct.map_id, LinearMap.id_apply]

private theorem weakContinuity_of_injectiveEvaluation {G V X : Type*} [Group G] [TopologicalSpace G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (j : V →ₗ[ℂ] (X → ℂ)) (hj : Function.Injective j)
    (hc : ∀ v x, Continuous fun g => j (ρ g v) x) :
    ∀ (v : V) (l : V →ₗ[ℂ] ℂ), Continuous fun g => l (ρ g v) := by
  obtain ⟨x, e, he⟩ := exists_evaluationEquiv j hj
  intro v l
  have hco : Continuous fun g => e (ρ g v) := continuous_pi fun i => by
    simp only [he]
    exact hc v (x i)
  have heq : (fun g => l (ρ g v)) = (l.comp e.symm.toLinearMap) ∘ fun g => e (ρ g v) := by
    funext g
    change l (ρ g v) = l (e.symm (e (ρ g v)))
    rw [e.symm_apply_apply]
  exact heq ▸ ((l.comp e.symm.toLinearMap).continuous_of_finiteDimensional.comp hco)

private theorem exists_finiteOrbitTensor {ι : Type} [Finite ι] {G : ι → Type*} [∀ i, Group (G i)]
    {V : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (G i) (V i)) (v : ∀ i, V i)
    (hf : ∀ i, FiniteVectors.IsFiniteVector (ρ i) (v i)) (hn : ∀ i, v i ≠ 0) :
    ∃ (T : Type u) (_ : AddCommGroup T) (_ : Module ℂ T) (_ : FiniteDimensional ℂ T)
      (_ : Nontrivial T) (σ : Representation ℂ (∀ i, G i) T)
      (j : σ.IntertwiningMap (FiniteTensor.external ρ)), Function.Injective j := by
  let O (i : ι) := FiniteVectors.orbitSubrepresentation (ρ i) (v i)
  let T := (⨂[ℂ] i, (O i).toSubmodule)
  let i (b : ι) : (O b).toRepresentation.IntertwiningMap (ρ b) :=
    ⟨(O b).toSubmodule.subtype, fun _ => rfl⟩
  let : ∀ b, FiniteDimensional ℂ (O b).toSubmodule := hf
  let : FiniteDimensional ℂ T := inferInstance
  let : ∀ b, Nontrivial (O b).toSubmodule := fun b =>
    ⟨⟨⟨v b, FiniteVectors.self_mem_orbitSpan (ρ b) (v b)⟩, 0,
      fun h => hn b (congrArg Subtype.val h)⟩⟩
  let : Nontrivial T := FiniteTensor.nontrivial_piTensorProduct fun _ => inferInstance
  exact ⟨T, inferInstance, inferInstance, inferInstance, inferInstance, _, FiniteTensor.externalMap i,
    piTensor_map_injective _ fun b => (O b).toSubmodule.subtype_injective⟩

private def infiniteCoefficientEvaluation
    (v : ∀ i, (M i).toSubmodule) : C →ₗ[ℂ] (FullLevi F B → ℂ) :=
  (coefficientEvaluation F B S).comp
    (FiniteTensor.externalMap (fun i => (S i).finiteMultiplicityEvalAt (M i) (v i))).toLinearMap

private theorem infiniteCoefficientEvaluation_injective
    (hi : ∀ i, (M i).toRepresentation.IsIrreducible)
    (v : ∀ i, (M i).toSubmodule) (hv : ∀ i, v i ≠ 0) :
    Function.Injective (infiniteCoefficientEvaluation F B S M v) :=
  (coefficientEvaluation_injective F B S).comp
    (piTensor_map_injective _ fun i => (S i).finiteMultiplicityEvalAt_injective (M i) (hi i) (hv i))

private theorem continuous_infiniteCoefficientEvaluation
    (v : ∀ i, (M i).toSubmodule) (t : C) :
    Continuous (infiniteCoefficientEvaluation F B S M v t) :=
  continuous_coefficientEvaluation F B S _

private theorem infiniteCoefficientEvaluation_compact
    (v : ∀ i, (M i).toSubmodule) (t : C) (h : H) (m : FullLevi F B) :
    infiniteCoefficientEvaluation F B S M v (infiniteMultiplicityCompactAction F B S M h t) m =
      infiniteCoefficientEvaluation F B S M v t
        (m * leviPair F B (fun b => (projection h b).val) 1) := by
  let φ := FiniteTensor.externalMap (fun i => (S i).finiteMultiplicityEvalAt (M i) (v i))
  have he : φ (infiniteMultiplicityCompactAction F B S M h t) =
      PiTensorProduct.map (fun b => (S b).compactRepresentation (projection h b)) (φ t) :=
    φ.isIntertwining _ _ (projection h) t
  exact (congrArg (fun s => coefficientEvaluation F B S s m) he).trans
    (coefficientEvaluation_compact F B S (projection h) (φ t) m)

/-- A nonzero covariant polynomial with values in a compact coefficient representation. -/
structure MultiplicityCompactPolynomial {D G V : Type*} [NormedRing D] [NormedAlgebra ℝ D]
    [Monoid G] [AddCommMonoid V] [Module ℂ V] (ι : G →* Dˣ) (τ : Representation ℂ G V) where
  dimension : ℕ
  inclusion : (Fin dimension → ℂ) →ₗ[ℂ] V
  polynomial : D → (Fin dimension → ℂ)
  inclusion_injective : Function.Injective inclusion
  polynomial_mem : polynomial ∈ Langlands.Archimedean.vectorCoordinatePolynomials D (Fin dimension → ℂ)
  value_one_ne_zero : inclusion (polynomial 1) ≠ 0
  covariance : ∀ h a, inclusion (polynomial ((ι h).val * a)) = τ h (inclusion (polynomial a))

abbrev InfiniteMultiplicityCompactSeed :=
  MultiplicityCompactPolynomial (V := C) (infiniteCompactMatrixInclusion F B)
    (infiniteMultiplicityCompactAction F B S M)

private theorem continuous_compact_orbit_evaluation
    (v : ∀ i, (M i).toSubmodule) (t : C) (m : FullLevi F B) :
    Continuous fun h : H =>
      infiniteCoefficientEvaluation F B S M v (infiniteMultiplicityCompactAction F B S M h t) m := by
  have hproj : Continuous fun h : H => fun b => (projection h b).val :=
    continuous_pi fun b => continuous_subtype_val.comp ((continuous_apply b).comp (projection).continuous)
  have hc : Continuous fun h : H => infiniteCoefficientEvaluation F B S M v t
      (m * leviPair F B (fun b => (projection h b).val) 1) :=
    (continuous_infiniteCoefficientEvaluation F B S M v t).comp
      (continuous_const.mul ((continuous_leviPair F B).comp (hproj.prodMk continuous_const)))
  exact (funext (fun h => infiniteCoefficientEvaluation_compact F B S M v t h m)).symm ▸ hc

private theorem exists_seed_of_finiteMultiplicityEmbedding
    {T : Type u} [AddCommGroup T] [Module ℂ T] [FiniteDimensional ℂ T] [Nontrivial T]
    (σ₀ : Representation ℂ (∀ i : Fin B.length, standardInfiniteCompact F (B.size i)) T)
    (incl : σ₀.IntertwiningMap (FiniteTensor.external κ)) (hincl : Function.Injective incl)
    (hi : ∀ i, (M i).toRepresentation.IsIrreducible)
    (v : ∀ i, (M i).toSubmodule) (hv : ∀ i, v i ≠ 0) :
    Nonempty (InfiniteMultiplicityCompactSeed F B S M) := by
  let σ : Representation ℂ H T := σ₀.comp (projection).toMonoidHom
  let j₀ : T →ₗ[ℂ] C := incl.toLinearMap
  have hj₀ : Function.Injective j₀ := hincl
  have hJ (h : H) (t : T) : j₀ (σ h t) = infiniteMultiplicityCompactAction F B S M h (j₀ t) :=
    incl.isIntertwining _ _ (projection h) t
  let e := infiniteCoefficientEvaluation F B S M v
  let j := e.comp j₀
  have hj : Function.Injective j := (infiniteCoefficientEvaluation_injective F B S M hi v hv).comp hj₀
  have hcont (t : T) (m : FullLevi F B) : Continuous fun h : H => j (σ h t) m := by
    have heval : (fun h : H => j (σ h t) m) =
        (fun h : H => e (infiniteMultiplicityCompactAction F B S M h (j₀ t)) m) :=
      funext fun h => congrArg (fun s => e s m) (hJ h t)
    rw [heval]
    exact continuous_compact_orbit_evaluation F B S M v (j₀ t) m
  have hfinite (t : T) : FiniteVectors.IsFiniteVector σ t :=
    Module.Finite.of_injective (FiniteVectors.orbitSpan σ t).subtype Subtype.val_injective
  obtain ⟨d, j', f, hj', hf, hne, hcov⟩ := exists_polynomialSection_infiniteCompactIntersection F B σ
    hfinite (weakContinuity_of_injectiveEvaluation σ j hj hcont)
  exact ⟨⟨d, j₀.comp j', f, hj₀.comp hj', hf,
    fun h => hne (hj₀ (h.trans (map_zero j₀).symm)), fun h a =>
      (congrArg j₀ (hcov h a)).trans (hJ h (j' (f a)))⟩⟩

/-- A nonzero polynomial compact seed exists in the original inducing
multiplicity spaces, for any nonzero irreducible finite factors. -/
theorem exists_infiniteMultiplicityCompactSeed
    (hm : ∀ i, M i ≠ ⊥) (hi : ∀ i, (M i).toRepresentation.IsIrreducible) :
    Nonempty (InfiniteMultiplicityCompactSeed F B S M) := by
  choose a ha ha0 using fun i => TwoFactorExistence.exists_ne_zero_of_ne_bot (hm i)
  let v (i : Fin B.length) : (M i).toSubmodule := ⟨a i, ha i⟩
  have hv (i : Fin B.length) : v i ≠ 0 := fun h => ha0 i (congrArg Subtype.val h)
  let u (i : Fin B.length) : J i := ⟨(M i).toSubmodule.subtype, fun _ => rfl⟩
  have hu (i : Fin B.length) : u i ≠ 0 := by
    intro h
    have e := congrArg (fun f : J i => f (v i)) h
    exact ha0 i e
  have hfinite (b : Fin B.length) : FiniteVectors.IsFiniteVector (κ b) (u b) :=
    (S b).finiteMultiplicityCompact_isFiniteVector (M b) (hm b) (hi b) (u b)
  obtain ⟨T, _, _, _, _, σ₀, incl, hincl⟩ := exists_finiteOrbitTensor κ u hfinite hu
  exact exists_seed_of_finiteMultiplicityEmbedding F B S M σ₀ incl hincl hi v hv

end Langlands.Global.AdelicBlockScalarSections
