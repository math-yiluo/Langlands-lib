import Langlands.Global.AdelicGLIwasawa
import Langlands.Global.FiniteAdelicGL.PadicComparison
import Langlands.Representation.Unramified.SphericalProductVector

/-!
# Compact evaluations for normalized local block induction

At a finite place, the actual local integral group distinguishes sections of
the canonical normalized block induction. Each tensor of integral-fixed block
vectors extends to a section with that constant value on the integral group.
-/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uV

namespace Langlands.Global.FiniteAdelicGL

open Langlands.GeneralLinear Langlands.Unramified
open CompletionPadic PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (v : FinitePlace F)

local notation "Fv" => (padicField v)
local notation "T" => (PadicField.canonicalTopologicalData (padicField v))
local notation "G" => (FiniteLocalGL F n v)
local notation "P" => (B.parabolic (FiniteCompletion F v))
local notation "μ" => (B.leviProjection (FiniteCompletion F v))

/-- The actual local integral subgroup, without a choice of matrix topology
in its type. -/
abbrev localIntegralSubgroup (s : ℕ) : Subgroup (FiniteLocalGL F s v) :=
  (localIntegral F s v).toSubgroup

private def canonicalIntegral : @OpenSubgroup G _ ((Fv).canonicalGeneralLinearTopology n) := by
  refine @OpenSubgroup.mk G _ ((Fv).canonicalGeneralLinearTopology n)
    (localIntegralSubgroup F v n) ?_
  change @IsOpen (FiniteLocalGL F n v) ((Fv).canonicalGeneralLinearTopology n)
    (localIntegral F n v : Set (FiniteLocalGL F n v))
  rw [← localGL_topology_eq F v n]
  exact (localIntegral F n v).isOpen

local instance localBlockTopology (s : ℕ) :
    TopologicalSpace (GeneralLinear s (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology s

local instance localBlockTopologicalGroup (s : ℕ) :
    IsTopologicalGroup (GeneralLinear s (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopologicalGroup s

theorem exists_local_parabolic_mul_integral (g : FiniteLocalGL F n v) :
    ∃ (p : P) (k : localIntegral F n v), g = p.val * k.val := by
  obtain ⟨p, k, h, hp, hk⟩ := exists_local_iwasawa F n v g
  exact ⟨⟨p, B.mem_parabolic_of_isUpperTriangular p hp⟩, ⟨k, hk⟩, h⟩

theorem localLeviProjection_mem_integral (p : P) (hp : p.val ∈ localIntegral F n v)
    (i : Fin B.length) : μ p i ∈ localIntegral F (B.size i) v := by
  have h := (mem_localIntegral F n v p.val).mp hp
  apply (mem_localIntegral F (B.size i) v (μ p i)).mpr
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · rw [B.leviProjection_apply]
    exact h.1 _ _
  · rw [← Pi.inv_apply, ← map_inv, B.leviProjection_apply]
    exact h.2 _ _

theorem localLeviEmbedding_mem_integral (m : B.Levi (FiniteCompletion F v))
    (hm : ∀ i, m i ∈ localIntegral F (B.size i) v) :
    B.leviEmbedding (FiniteCompletion F v) m ∈ localIntegral F n v := by
  have h (x : B.Levi (FiniteCompletion F v))
      (hx : ∀ i, ∀ a b, x i a b ∈ v.adicCompletionIntegers F) :
      ∀ a b, B.leviEmbedding (FiniteCompletion F v) x a b ∈ v.adicCompletionIntegers F := by
    intro a b
    obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective a
    obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective b
    change B.leviEmbedding (FiniteCompletion F v) x (B.index i a) (B.index j b) ∈
      v.adicCompletionIntegers F
    by_cases hij : i = j
    · subst j
      rw [B.leviEmbedding_apply_same]
      exact hx i a b
    · rw [B.leviEmbedding_apply_ne _ _ a b hij]
      exact zero_mem _
  apply (mem_localIntegral F n v _).mpr
  refine ⟨h m (fun i => ((mem_localIntegral F (B.size i) v _).mp (hm i)).1), ?_⟩
  rw [← map_inv]
  exact h m⁻¹ (fun i => ((mem_localIntegral F (B.size i) v _).mp (hm i)).2)

theorem localParabolicHalfModulus_eq_one_of_integral (p : P)
    (hp : p.val ∈ localIntegral F n v) : (T).parabolicHalfModulus B p = 1 := by
  have h := (mem_localIntegral F n v p.val).mp hp
  have hp' : p.val ∈ GeneralLinearGroup.integralSubgroup (Fin n) (T).Integers := by
    apply (GeneralLinearGroup.mem_integralSubgroup (Fin n) (T).Integers p.val).mpr
    exact ⟨fun a b => (mem_localIntegers_iff_canonical F v _).mp (h.1 a b),
      fun a b => (mem_localIntegers_iff_canonical F v _).mp (h.2 a b)⟩
  rw [(T).parabolicHalfModulus_apply]
  exact ((T).leviHalfModulus_eq_one B _).mpr
    ((T).normOneLevi_le_ker_leviModulus B
      ((T).blockLeviProjection_mem_normOneLevi_of_integral B p hp'))

variable {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  (σ : ∀ i, Representation ℂ (FiniteLocalGL F (B.size i) v) (V i))

local notation "W" => (⨂[ℂ] i, V i)

/-- The exact parabolic action of the canonical normalized product induction. -/
abbrev localBlockInducing : Representation ℂ P W :=
  twist ((T).parabolicHalfModulus B) ((B.blockTensor σ).comp μ)

/-- The canonical normalized block induction carrier at an actual finite place. -/
abbrev LocalBlockInduced :=
  Induction.SmoothFunctions P (localBlockInducing F B v σ)

/-- Evaluate the canonical normalized induction on a local integral matrix. -/
def localBlockCompactEvaluation (k : localIntegral F n v) : LocalBlockInduced F B v σ →ₗ[ℂ] W where
  toFun f := Induction.eval _ _ f k.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem localBlockCompactEvaluation_apply (k : localIntegral F n v) (f : LocalBlockInduced F B v σ) :
    localBlockCompactEvaluation F B v σ k f = Induction.eval _ _ f k.val := rfl

theorem eq_zero_of_localBlockCompactEvaluation_zero (f : LocalBlockInduced F B v σ)
    (hf : ∀ k, localBlockCompactEvaluation F B v σ k f = 0) : f = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  obtain ⟨p, k, h⟩ := exists_local_parabolic_mul_integral F B v g
  change Induction.eval _ _ f g = (0 : W)
  rw [h, show Induction.eval _ _ f (p.val * k.val) =
    localBlockInducing F B v σ p (localBlockCompactEvaluation F B v σ k f)
      from f.val.property p k.val,
    hf, map_zero]

theorem localBlockInducing_apply_of_integral (p : P)
    (hp : p.val ∈ localIntegral F n v) (w : W) :
    localBlockInducing F B v σ p w = B.blockTensor σ (μ p) w := by
  change ((T).parabolicHalfModulus B p : ℂ) • B.blockTensor σ (μ p) w = _
  rw [localParabolicHalfModulus_eq_one_of_integral F B v p hp, Units.val_one, one_smul]

/-- Evaluate a finite right translate by factoring the translated compact
argument with its actual parabolic half modulus. -/
theorem localBlockCompactEvaluation_rightTranslate (f : LocalBlockInduced F B v σ)
    (g : G) (k l : localIntegral F n v) (p : P) (h : k.val * g = p.val * l.val) :
    localBlockCompactEvaluation F B v σ k ((Fv).canonicalNormalizedProductInduced B σ g f) =
      ((T).parabolicHalfModulus B p : ℂ) •
        B.blockTensor σ (μ p) (localBlockCompactEvaluation F B v σ l f) := by
  change Induction.eval P (localBlockInducing F B v σ) f (k.val * g) = _
  rw [h]
  exact f.val.property p l.val

/-- A pure tensor of local integral-fixed coefficients extends to a reference
section with constant compact evaluation and genuine integral right invariance. -/
theorem exists_localBlockReference (e : ∀ i, V i)
    (he : ∀ i (g : localIntegral F (B.size i) v), σ i g.val (e i) = e i) :
    ∃ f : LocalBlockInduced F B v σ,
      (∀ k, localBlockCompactEvaluation F B v σ k f = PiTensorProduct.tprod ℂ e) ∧
      ∀ k : localIntegral F n v, (Fv).canonicalNormalizedProductInduced B σ k.val f = f := by
  obtain ⟨f, h1, hf⟩ := SphericalExistence.exists_fixed_smoothFunction P (localBlockInducing F B v σ)
    (canonicalIntegral F (n := n) v)
    (fun g => by
      obtain ⟨p, k, h⟩ := exists_local_parabolic_mul_integral F B v g
      exact ⟨p, k.val, k.property, h⟩) (PiTensorProduct.tprod ℂ e) (by
        intro p hp
        change p.val ∈ localIntegral F n v at hp
        rw [localBlockInducing_apply_of_integral F B v σ p hp, B.blockTensor_tprod]
        exact congrArg (PiTensorProduct.tprod ℂ) (funext fun i =>
          he i ⟨μ p i, localLeviProjection_mem_integral F B v p hp i⟩))
  refine ⟨f, fun k => ?_, fun k => hf ⟨k.val, k.property⟩⟩
  have hk := Induction.eval_mul_of_mem_fixedVectors P (localBlockInducing F B v σ)
    (canonicalIntegral F (n := n) v).toSubgroup hf ⟨k.val, k.property⟩ 1
  change Induction.eval P (localBlockInducing F B v σ) f (1 * k.val) =
    Induction.eval P (localBlockInducing F B v σ) f 1 at hk
  rw [one_mul, h1] at hk
  exact hk

theorem localBlockCompactEvaluation_eq_one_of_fixed (f : LocalBlockInduced F B v σ)
    (hf : ∀ k : localIntegral F n v, (Fv).canonicalNormalizedProductInduced B σ k.val f = f)
    (k : localIntegral F n v) :
    localBlockCompactEvaluation F B v σ k f = localBlockCompactEvaluation F B v σ 1 f := by
  have h := congrArg (localBlockCompactEvaluation F B v σ 1) (hf k)
  change Induction.eval P (localBlockInducing F B v σ) f (1 * k.val) = _ at h
  rw [one_mul] at h
  exact h

local notation "J" => (fun i => localIntegralSubgroup F v (B.size i))
local notation "U" => (fun i => fixedVectors (σ i) (J i))

theorem localBlockCompactEvaluation_mem_fixedCoefficients (f : LocalBlockInduced F B v σ)
    (hf : ∀ k : localIntegral F n v, (Fv).canonicalNormalizedProductInduced B σ k.val f = f) :
    localBlockCompactEvaluation F B v σ 1 f ∈
      fixedVectors (B.blockTensor σ) (Subgroup.pi Set.univ J) := by
  intro m
  let p := B.leviInParabolic (FiniteCompletion F v) m.val
  have hp : p.val ∈ localIntegral F n v :=
    localLeviEmbedding_mem_integral F B v m.val (fun i => m.property i (Set.mem_univ i))
  let k : localIntegral F n v := ⟨p.val, hp⟩
  calc
    B.blockTensor σ m.val (localBlockCompactEvaluation F B v σ 1 f) =
        localBlockInducing F B v σ p (localBlockCompactEvaluation F B v σ 1 f) := by
      rw [localBlockInducing_apply_of_integral F B v σ p hp, B.leviProjection_section]
    _ = localBlockCompactEvaluation F B v σ k f := by
      have h : Induction.eval P (localBlockInducing F B v σ) f (p.val * 1) =
          localBlockInducing F B v σ p (localBlockCompactEvaluation F B v σ 1 f) :=
        f.val.property p 1
      rw [mul_one] at h
      exact h.symm
    _ = localBlockCompactEvaluation F B v σ 1 f :=
      localBlockCompactEvaluation_eq_one_of_fixed F B v σ f hf k

/-- When the coefficient fixed spaces are lines, every integral-fixed induced
section is a multiple of the section with the prescribed pure reference value. -/
theorem exists_smul_localBlockReference_eq
    (e : ∀ i, U i) (he : ∀ i, e i ≠ 0) (hU : ∀ i, Module.finrank ℂ (U i) = 1)
    (f₀ f : LocalBlockInduced F B v σ)
    (hf₀ : ∀ k, localBlockCompactEvaluation F B v σ k f₀ =
      PiTensorProduct.tprod ℂ (fun i => (e i).val))
    (hf : ∀ k : localIntegral F n v, (Fv).canonicalNormalizedProductInduced B σ k.val f = f) :
    ∃ c : ℂ, c • f₀ = f := by
  let w := PiTensorProduct.tprod ℂ (fun i => (e i).val)
  have hline : (PiTensorProduct.map (fun i => (U i).subtype)).range ≤
      Submodule.span ℂ {w} := by
    rw [PiTensorProduct.map_range_eq_span_tprod]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    choose c hc using fun i => (finrank_eq_one_iff_of_nonzero' (e i) (he i)).mp (hU i) (x i)
    apply Submodule.mem_span_singleton.mpr
    refine ⟨∏ i, c i, ?_⟩
    rw [← (PiTensorProduct.tprod ℂ).map_smul_univ]
    exact congrArg (PiTensorProduct.tprod ℂ) (funext fun i => congrArg Subtype.val (hc i))
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (hline (FiniteTensor.fixedVectors_external_le σ J
      (localBlockCompactEvaluation_mem_fixedCoefficients F B v σ f hf)))
  refine ⟨c, sub_eq_zero.mp (eq_zero_of_localBlockCompactEvaluation_zero F B v σ _ ?_)⟩
  intro k
  rw [map_sub, map_smul, hf₀, localBlockCompactEvaluation_eq_one_of_fixed F B v σ f hf k]
  exact sub_eq_zero.mpr hc

end Langlands.Global.FiniteAdelicGL
