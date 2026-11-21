import Langlands.Automorphic.CuspidalLeviCoefficientSlices
import Langlands.Automorphic.TranslatedBlockLeviUniformBounds
import Langlands.Automorphic.CuspidalAdmissible.CompactOrbitCasimirUniform
import Langlands.Automorphic.CuspidalOperatorSemisimplicity
import Langlands.Representation.Twist.Definitions

/-! # Finite-dimensional windows for the actual twisted cuspidal slices -/

noncomputable section
universe u
open NumberField Polynomial
open scoped Classical
set_option autoImplicit false
set_option quotPrecheck false

namespace Langlands.Automorphic

open Langlands.Global ArchimedeanGL Langlands.GeneralLinear CuspidalAdmissible FiniteVectors

variable (F : Type u) [Field F] [NumberField F] {n : ℕ}

local instance cuspSliceFiniteRationalGroup (d : ℕ) : AddCommGroup (RationalInvariantFunctions F d) :=
  Submodule.addCommGroup _
local instance cuspSliceFiniteContinuousGroup (d : ℕ) : AddCommGroup (ContinuousRationalFunctions F d) :=
  Submodule.addCommGroup _
local instance cuspSliceFiniteSmoothGroup (d : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F d) :=
  Submodule.addCommGroup _
local instance cuspSliceFiniteStableGroup (d : ℕ) : AddCommGroup (StableAutomorphicFunctions F d) :=
  Submodule.addCommGroup _
local instance cuspSliceFiniteFormGroup (d : ℕ) : AddCommGroup (AutomorphicForms F d) := Submodule.addCommGroup _
local instance cuspSliceFiniteRealizationGroup {d : ℕ} (W : OperatorRealization F d) : AddCommGroup W.Space :=
  Submodule.addCommGroup _
local instance cuspSliceFiniteOperatorRing (d : ℕ) : Ring (automorphicOperatorAlgebra F d) :=
  Subalgebra.toRing _

variable (B : BlockShape n) (S : OperatorRealization F n)
  {C : Type*} [AddCommGroup C] [Module ℂ C]
  (j : C →ₗ[ℂ] TranslatedBlockConstantTerms F B S) (i : Fin B.length)
  {W : OperatorRealization F (B.size i)}
  (D : RealizedBlockLeviSlices F B S j i W) (μ : HeckeCharacter F)

local notation "M" => AdelicBlockParabolic.FullLevi F B
local notation "d" => B.size i
local notation "W₁" => W.heckeDeterminantTwist μ
local notation "V" => FiniteSmoothRationalFunctions F d
local notation "s" => D.twistedSlice μ
local notation "raw" => translatedBlockLeviSlice F B S i

set_option maxHeartbeats 550000 in
/-- A determinant twist keeps a single common finite level for all slices of a fixed vector. -/
theorem exists_twistedSlice_commonLevel (w : C) :
    ∃ K : OpenSubgroup (FiniteAdelicGL F d), ∀ (m : M) (a : K),
      (W₁).finiteRepresentation a.val (s m w) = s m w := by
  obtain ⟨L, hL⟩ := exists_translatedBlockLeviSlice_commonLevel F B S i (j w)
  let K := L ⊓ μ.heckeFiniteDeterminantKernel d
  refine ⟨K, fun m a => ?_⟩
  let e := W.heckeDeterminantTwistEquiv μ
  let b := a.val
  have h₁ : W.finiteRepresentation b (D.slice m w) = D.slice m w := by
    apply W.finiteSmoothAmbient_injective F
    calc
      _ = finiteSmoothFiniteRightAction F d b (raw m (j w)) :=
        congrArg (finiteSmoothFiniteRightAction F d b) (D.ambient_slice m w)
      _ = raw m (j w) := hL m ⟨b, a.property.1⟩
      _ = _ := (D.ambient_slice m w).symm
  have h₂ : (μ.adelicDeterminant d (AdelicGL.ofFinite F d b) : ℂ) = 1 :=
    congrArg Units.val ((μ.mem_heckeFiniteDeterminantKernel d b).mp a.property.2)
  calc
    _ = (μ.adelicDeterminant d (AdelicGL.ofFinite F d b) : ℂ) •
        e (W.finiteRepresentation b (D.slice m w)) :=
      W.heckeDeterminantTwistEquiv_finite μ b (D.slice m w)
    _ = (1 : ℂ) • e (D.slice m w) :=
      congrArg₂ (fun (c : ℂ) (f : W.Space) => c • e f) h₂ h₁
    _ = _ := one_smul ℂ _

set_option maxHeartbeats 550000 in
/-- The common shifted-Casimir bound holds in the twisted realization itself. -/
theorem exists_twistedSlice_commonMatrixCasimir (w : C) :
    ∃ q : ℂ[X], q ≠ 0 ∧ ∀ m : M, aeval (casimirOperator W₁) q (s m w) = 0 := by
  obtain ⟨q, hq, h⟩ := exists_translatedBlockLeviSlice_twistedCasimirPolynomial F B S i (j w) μ
  refine ⟨q, hq, fun m => ?_⟩
  let e : (W₁).Space →ₗ[ℂ] V := (W₁).finiteSmoothAmbient F
  let A := finiteSmoothEnvelopingAction F d (matrixCasimir F d)
  apply (W₁).finiteSmoothAmbient_injective F
  calc
    _ = aeval A q (e (s m w)) := aeval_intertwine e (fun _ => rfl) q (s m w)
    _ = aeval A q (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier d μ (raw m (j w))) :=
      congrArg (aeval A q) (D.ambient_twistedSlice μ m w)
    _ = 0 := h m
    _ = _ := e.map_zero.symm

variable (A : automorphicOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ C)

local notation "ρc" => (AlgHom.toMonoidHom' A).comp (compactOperator F n)

/-- The restricted compact action with the same determinant twist as the slice. -/
def twistedBlockCompactAction : Representation ℂ (standardInfiniteCompact F d) C :=
  Langlands.twist ((μ.infiniteDeterminantCharacter d).comp (standardInfiniteCompact F d).subtype)
    ((ρc).comp (blockShapeInfiniteCompactEmbedding B F i))

set_option maxHeartbeats 700000 in
/-- The compact Casimir admits one polynomial for all twisted slices of a fixed vector. -/
theorem exists_twistedSlice_commonCompactCasimir
    (hj : ∀ (a : automorphicOperatorAlgebra F n) (w : C),
      j (A a w) = translatedBlockTermOperatorAction F B S a (j w))
    (w : C) (hw : IsFiniteVector ρc w) :
    ∃ p : ℂ[X], p ≠ 0 ∧ ∀ m : M, aeval (compactCasimirOperator W₁) p (s m w) = 0 := by
  let K := standardInfiniteCompact F d
  let κ := twistedBlockCompactAction F B i μ A
  let b := blockShapeInfiniteCompactEmbedding B F i
  let c (k : K) : ℂ := (μ.infiniteDeterminantCharacter d k.val : ℂ)
  have hκ : orbitSpan κ w ≤ orbitSpan ρc w := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    change c k • ρc (b k) w ∈ orbitSpan ρc w
    exact (orbitSpan ρc w).smul_mem (c k) (action_mem_orbitSpan ρc (b k) w)
  let : Module.Finite ℂ (orbitSpan ρc w) := hw
  have hwκ : IsFiniteVector κ w := Submodule.finiteDimensional_of_le hκ
  obtain ⟨p, hp, h⟩ := exists_compactCasimir_annihilator_of_finiteVector W₁ κ w hwκ
  refine ⟨p, hp, fun m => h (s m) (fun k x => ?_)⟩
  let e := W.heckeDeterminantTwistEquiv μ
  calc
    _ = c k • s m (ρc (b k) x) := (s m).map_smul _ _
    _ = c k • e (W.compactRepresentation k (D.slice m x)) :=
      congrArg (fun y : W.Space => c k • e y) (D.compact hj m k x)
    _ = _ := (W.heckeDeterminantTwistEquiv_compact μ k (D.slice m x)).symm

variable [CompactSpace (AdeleQuotient F)]

set_option maxHeartbeats 850000 in
/-- All twisted slices of one vector in a block lie in one finite-dimensional subspace. -/
theorem exists_finiteDimensional_twistedSliceSpace
    (hj : ∀ (a : automorphicOperatorAlgebra F n) (w : C),
      j (A a w) = translatedBlockTermOperatorAction F B S a (j w))
    (hW : (W₁).IsCuspidal) (χ : HeckeCharacter F) (hχ : χ.IsUnitary) (hχW : (W₁).HasCentralCharacter χ)
    (w : C) (hw : IsFiniteVector ρc w) :
    ∃ P : Submodule ℂ (W₁).Space, FiniteDimensional ℂ P ∧ ∀ m : M, s m w ∈ P := by
  obtain ⟨L, hL⟩ := exists_twistedSlice_commonLevel F B S j i D μ w
  obtain ⟨q, hq, hqkill⟩ := exists_twistedSlice_commonMatrixCasimir F B S j i D μ w
  obtain ⟨p, hp, hpkill⟩ := exists_twistedSlice_commonCompactCasimir F B S j i D μ A hj w hw
  refine ⟨fixedPolynomialKernels (W₁).finiteRepresentation (casimirOperator W₁)
      (compactCasimirOperator W₁) L q p, ?_, fun m => ⟨⟨hL m, hqkill m⟩, hpkill m⟩⟩
  exact finiteDimensional_fixedCasimirKernels W₁ (Nat.ne_of_gt (B.positive i)) hW χ hχ hχW L q p hq hp

end Langlands.Automorphic
