import Langlands.Automorphic.CuspidalFiniteInfiniteDecomposition
import Langlands.Representation.Archimedean.GKModule

/-! # Irreducibility of the archimedean multiplicity space -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace Langlands.Automorphic

open Langlands.Global
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem enveloping_stable
    {L V : Type*} [LieRing L] [LieAlgebra ℂ L] [AddCommGroup V] [Module ℂ V]
    (E : UniversalEnvelopingAlgebra ℂ L →ₐ[ℂ] Module.End ℂ V)
    (N : Submodule ℂ V)
    (hN : ∀ (X : L) (v : V), v ∈ N → E (UniversalEnvelopingAlgebra.ι ℂ X) v ∈ N)
    (a : UniversalEnvelopingAlgebra ℂ L) (v : V) (hv : v ∈ N) : E a v ∈ N := by
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ L) a
  induction t using TensorAlgebra.induction generalizing v with
  | algebraMap c =>
    simpa only [Algebra.algebraMap_eq_smul_one, map_smul, map_one, LinearMap.smul_apply,
      Module.End.one_apply] using N.smul_mem c hv
  | «ι» X => exact hN X v hv
  | mul a b ha hb =>
    simpa only [map_mul, Module.End.mul_apply] using ha _ (hb v hv)
  | add a b ha hb =>
    simpa only [map_add, LinearMap.add_apply] using N.add_mem (ha v hv) (hb v hv)

private theorem multiplicity_dual_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] {a : V} (ha : a ≠ 0) :
    ∃ φ : V →ₗ[ℂ] ℂ, φ a = 1 :=
  Module.Projective.exists_dual_eq_one ℂ ha

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance multIrreducibleRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance multIrreducibleContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance multIrreducibleSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance multIrreducibleFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance multIrreducibleStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance multIrreducibleSpaceGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization

variable (S : OperatorRealization F n) (A : Subrepresentation S.finiteRepresentation)

local instance multIrreducibleSliceGroup : AddCommGroup A.toSubmodule :=
  Submodule.addCommGroup _

/-- The genuine complexified Lie action on the finite-factor multiplicity space. -/
def finiteMultiplicityLie :
    ArchimedeanGL.ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ (S.FiniteMultiplicity A) :=
  (S.finiteMultiplicityEnveloping A).toLieHom.comp (ArchimedeanGL.envelopingGenerator F n)

@[simp]
theorem finiteMultiplicityLie_apply (X : ArchimedeanGL.ComplexLieAlgebra F n)
    (f : S.FiniteMultiplicity A) (a : A.toSubmodule) :
    S.finiteMultiplicityLie A X f a = S.complexLieAction X (f a) := rfl

set_option maxHeartbeats 5000000 in
/-- Full-operator irreducibility descends to the combined archimedean multiplicity action. -/
theorem finiteMultiplicity_isIrreducibleGKModule
    (hS : S.IsIrreducible) (hne : A ≠ ⊥)
    (hA : A.toRepresentation.IsIrreducible) (ha : IsAdmissible A.toRepresentation) :
    Archimedean.IsIrreducibleGKModule (S.finiteMultiplicityCompact A)
      (S.finiteMultiplicityLie A) := by
  classical
  obtain ⟨a, haA, ha0⟩ := TwoFactorExistence.exists_ne_zero_of_ne_bot hne
  let a₀ : A.toSubmodule := ⟨a, haA⟩
  have ha₀ : a₀ ≠ 0 := fun h => ha0 (congrArg Subtype.val h)
  have hinj := S.finiteMultiplicityEvalAt_injective A hA ha₀
  let ι : S.FiniteMultiplicity A := ProductFactorization.subrepresentationInclusion A
  have hι : ι ≠ 0 := by
    intro h
    exact ha0 (congrArg (fun f : S.FiniteMultiplicity A => f a₀) h)
  refine ⟨⟨ι, 0, hι⟩, ?_⟩
  intro N hk hl
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  have he : ∀ b f, f ∈ N → S.finiteMultiplicityEnveloping A b f ∈ N :=
    enveloping_stable (S.finiteMultiplicityEnveloping A) N hl
  obtain ⟨f₀, hf₀N, hf₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  let T : A.toSubmodule ⊗[ℂ] N →ₗ[ℂ] A.toSubmodule ⊗[ℂ] S.FiniteMultiplicity A :=
    TensorProduct.map LinearMap.id N.subtype
  let R : Submodule ℂ S.Space := LinearMap.range (S.finiteMultiplicityEvaluation A ∘ₗ T)
  have hdR : ∀ d t, S.finiteRepresentation d
      (S.finiteMultiplicityEvaluation A (T t)) ∈ R := by
    intro d t
    induction t with
    | tmul b f =>
      refine ⟨A.toRepresentation d b ⊗ₜ[ℂ] f, ?_⟩
      exact Representation.IntertwiningMap.isIntertwining _ _ f.val d b
    | add t t' ht ht' =>
      simpa only [map_add] using R.add_mem ht ht'
  have hkR : ∀ k t, S.compactRepresentation k
      (S.finiteMultiplicityEvaluation A (T t)) ∈ R := by
    intro k t
    induction t with
    | tmul b f =>
      exact ⟨b ⊗ₜ[ℂ] (⟨S.finiteMultiplicityCompact A k f.val, hk k f.val f.property⟩ : N),
        rfl⟩
    | add t t' ht ht' =>
      simpa only [map_add] using R.add_mem ht ht'
  have heR : ∀ b t, S.envelopingAction b
      (S.finiteMultiplicityEvaluation A (T t)) ∈ R := by
    intro b t
    induction t with
    | tmul a f =>
      exact ⟨a ⊗ₜ[ℂ] (⟨S.finiteMultiplicityEnveloping A b f.val, he b f.val f.property⟩ : N),
        rfl⟩
    | add t t' ht ht' =>
      simpa only [map_add] using R.add_mem ht ht'
  have hR : R ≠ ⊥ := by
    intro h
    have hm : f₀ a₀ ∈ R := ⟨a₀ ⊗ₜ[ℂ] (⟨f₀, hf₀N⟩ : N), rfl⟩
    rw [h] at hm
    apply hf₀
    apply hinj
    exact (Submodule.mem_bot ℂ).mp hm
  have hRtop : R = ⊤ := S.eq_top_of_generatorStable hS R
    (by rintro d _ ⟨t, rfl⟩; exact hdR d t)
    (by rintro k _ ⟨t, rfl⟩; exact hkR k t)
    (by rintro b _ ⟨t, rfl⟩; exact heR b t) hR
  obtain ⟨φ, hφ⟩ := multiplicity_dual_eq_one ha₀
  let Φ : A.toSubmodule ⊗[ℂ] S.FiniteMultiplicity A →ₗ[ℂ] S.FiniteMultiplicity A :=
    (TensorProduct.lid ℂ (S.FiniteMultiplicity A)).toLinearMap ∘ₗ
      TensorProduct.map φ LinearMap.id
  have hΦ : ∀ t, Φ (T t) ∈ N := by
    intro t
    induction t with
    | tmul b f =>
      change φ b • f.val ∈ N
      exact N.smul_mem _ f.property
    | add t t' ht ht' =>
      simpa only [map_add] using N.add_mem ht ht'
  apply eq_top_iff.mpr
  intro f _
  have hfR : f a₀ ∈ R := hRtop ▸ Submodule.mem_top
  obtain ⟨t, ht⟩ := hfR
  have ht' : T t = a₀ ⊗ₜ[ℂ] f := by
    apply S.finiteMultiplicityEvaluation_injective A hA ha
    exact ht
  have hmem := hΦ t
  rw [ht'] at hmem
  have hval : Φ (a₀ ⊗ₜ[ℂ] f) = f := by
    change φ a₀ • f = f
    rw [hφ, one_smul]
  exact hval ▸ hmem

end OperatorRealization

end Langlands.Automorphic
