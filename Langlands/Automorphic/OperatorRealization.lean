import Langlands.Automorphic.OperatorCore

/-! # Realized subspaces preserved by the actual automorphic operators -/

noncomputable section
universe u

namespace Langlands.Automorphic

open Langlands.Global NumberField ContinuousRationalFunctions

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

/-- An actual subspace of the constructed stable form space, invariant under
finite translations, standard infinite compact translations and genuine differentials. -/
abbrev OperatorRealization := Subrepresentation (stableAutomorphicAction F n)

namespace OperatorRealization

variable {F n} (S : OperatorRealization F n)

abbrev Space := S.toSubmodule

local instance : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The whole concrete operator algebra acts by restriction. -/
def representation :
    Representation ℂ (automorphicOperatorAlgebra F n) S.Space :=
  S.toRepresentation

def finiteRepresentation : Representation ℂ (FiniteAdelicGL F n) S.Space :=
  S.representation.comp (finiteOperator F n)

def compactRepresentation : Representation ℂ (standardInfiniteCompact F n) S.Space :=
  S.representation.comp (compactOperator F n)

/-- The restricted genuine differential action retains its algebra structure. -/
def envelopingAction :
    ArchimedeanGL.EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ S.Space where
  toFun a := S.representation (differentialOperator F n a)
  map_one' := by simp only [map_one]
  map_mul' a b := by simp only [map_mul]
  map_zero' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change stableAutomorphicEnvelopingAction F n 0 f.val = 0
    simp only [map_zero, LinearMap.zero_apply]
  map_add' a b := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change stableAutomorphicEnvelopingAction F n (a + b) f.val =
      stableAutomorphicEnvelopingAction F n a f.val +
        stableAutomorphicEnvelopingAction F n b f.val
    simp only [map_add, LinearMap.add_apply]
  commutes' c := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change stableAutomorphicEnvelopingAction F n (algebraMap ℂ _ c) f.val = c • f.val
    rw [AlgHom.commutes]
    rfl

/-- Faithful inclusion intertwining the entire concrete operator algebra. -/
def inclusion : S.representation.IntertwiningMap (stableAutomorphicAction F n) where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := by ext; rfl

theorem inclusion_injective : Function.Injective S.inclusion := Subtype.val_injective

@[simp]
theorem inclusion_finiteRepresentation (d : FiniteAdelicGL F n) (f : S.Space) :
    S.inclusion (S.finiteRepresentation d f) =
      stableAutomorphicFiniteAction F n d (S.inclusion f) := rfl

@[simp]
theorem inclusion_compactRepresentation (k : standardInfiniteCompact F n) (f : S.Space) :
    S.inclusion (S.compactRepresentation k f) =
      stableAutomorphicCompactAction F n k (S.inclusion f) := rfl

@[simp]
theorem inclusion_envelopingAction (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : S.Space) :
    S.inclusion (S.envelopingAction a f) =
      stableAutomorphicEnvelopingAction F n a (S.inclusion f) := rfl

theorem finiteRepresentation_envelopingAction (d : FiniteAdelicGL F n)
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : S.Space) :
    S.finiteRepresentation d (S.envelopingAction a f) =
      S.envelopingAction a (S.finiteRepresentation d f) := by
  apply S.inclusion_injective
  exact stableAutomorphicFiniteAction_envelopingAction F n d a f.val

/-- The inclusion in actual forms preserves the finite action. -/
def formInclusion : FiniteRealizationMap F n S.finiteRepresentation where
  toLinearMap := (stableAutomorphicInclusion F n).toLinearMap.comp S.inclusion.toLinearMap
  isIntertwining' _ := by ext; rfl

theorem formInclusion_injective : Function.Injective S.formInclusion :=
  (stableAutomorphicInclusion_injective F n).comp S.inclusion_injective

theorem finiteRepresentation_isSmooth : Langlands.IsSmooth S.finiteRepresentation :=
  Langlands.isSmooth_of_injective S.formInclusion S.formInclusion_injective
    (automorphicFiniteRightAction_isSmooth F n)

/-- Forgetting the extra operators gives the actual image in the existing finite space. -/
def toFiniteRealization : FiniteRealization F n :=
  finiteRealizationImage F n S.formInclusion

/-- The finite action is genuinely equivalent to that on its image in forms. -/
def finiteEquiv :
    S.finiteRepresentation.Equiv S.toFiniteRealization.representation :=
  finiteRealizationImageEquiv F n S.formInclusion S.formInclusion_injective

@[simp]
theorem finiteEquiv_inclusion (f : S.Space) :
    S.toFiniteRealization.inclusion (S.finiteEquiv f) = S.formInclusion f := rfl

/-- The actual continuous adelic function carried by a realized vector. -/
def toContinuous : S.Space →ₗ[ℂ] ContinuousRationalFunctions F n :=
  (automorphicToContinuous F n).comp S.formInclusion.toLinearMap

theorem toContinuous_injective : Function.Injective S.toContinuous :=
  (automorphicToContinuous_injective F n).comp S.formInclusion_injective

@[simp]
theorem evaluate_finiteRepresentation (d : FiniteAdelicGL F n) (f : S.Space)
    (x : AdelicGL F n) :
    evaluate F n (S.toContinuous (S.finiteRepresentation d f)) x =
      evaluate F n (S.toContinuous f) (x * AdelicGL.ofFinite F n d) := rfl

@[simp]
theorem evaluate_compactRepresentation (k : standardInfiniteCompact F n) (f : S.Space)
    (x : AdelicGL F n) :
    evaluate F n (S.toContinuous (S.compactRepresentation k f)) x =
      evaluate F n (S.toContinuous f) (x * AdelicGL.ofInfinite F n k.val) := rfl

/-- Irreducibility refers to all three operator families together. -/
abbrev IsIrreducible : Prop := S.representation.IsIrreducible

/-- The prescribed character is imposed on the actual form image. -/
def HasCentralCharacter (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) : Prop :=
  S.toFiniteRealization.HasCentralCharacter χ

theorem hasCentralCharacter_iff (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) :
    S.HasCentralCharacter χ ↔
      ∀ f : S.Space, S.formInclusion f ∈ centralCharacterAutomorphicSubrepresentation F n χ := by
  constructor
  · intro h f
    exact h ⟨f, rfl⟩
  · intro h f hf
    obtain ⟨v, rfl⟩ := hf
    exact h v

theorem centralCharacter_evaluate (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hS : S.HasCentralCharacter χ) (f : S.Space)
    (z : IdeleGroup (𝓞 F) F) (x : AdelicGL F n) :
    evaluate F n (S.toContinuous f) (AdelicGL.scalar F n z * x) =
      (centralIdeleCharacter F χ z : ℂ) * evaluate F n (S.toContinuous f) x :=
  (S.hasCentralCharacter_iff χ).mp hS f z x

variable [CompactSpace (AdeleQuotient F)]

/-- Cuspidality is the vanishing of actual constant terms on the form image. -/
def IsCuspidal : Prop := S.toFiniteRealization.IsCuspidal

theorem isCuspidal_iff :
    S.IsCuspidal ↔ ∀ f : S.Space, Langlands.Automorphic.IsCuspidal F n (S.toContinuous f) := by
  constructor
  · intro h f
    exact h ⟨f, rfl⟩
  · intro h f hf
    obtain ⟨v, rfl⟩ := hf
    exact h v

theorem constantTerm_eq_zero (hS : S.IsCuspidal)
    {a b : ℕ} (h : a + b = n) (ha : 0 < a) (hb : 0 < b)
    (f : S.Space) (g : AdelicGL F n) :
    constantTerm F n h (S.toContinuous f) g = 0 :=
  S.isCuspidal_iff.mp hS f a b h ha hb g

end OperatorRealization

/-- Generate an actual realization from a vector in the constructed stable space. -/
def generatedOperatorRealization (f : StableAutomorphicFunctions F n) :
    OperatorRealization F n :=
  Langlands.FiniteVectors.orbitSubrepresentation (stableAutomorphicAction F n) f

theorem mem_generatedOperatorRealization (f : StableAutomorphicFunctions F n) :
    f ∈ generatedOperatorRealization F n f :=
  Langlands.FiniteVectors.self_mem_orbitSpan (stableAutomorphicAction F n) f

theorem generatedOperatorRealization_le_iff (f : StableAutomorphicFunctions F n)
    (S : OperatorRealization F n) :
    generatedOperatorRealization F n f ≤ S ↔ f ∈ S :=
  ⟨fun h => h (mem_generatedOperatorRealization F n f),
    fun h => Langlands.FiniteVectors.orbitSpan_le (stableAutomorphicAction F n) f S h⟩

theorem generatedOperatorRealization_ne_bot {f : StableAutomorphicFunctions F n} (hf : f ≠ 0) :
    generatedOperatorRealization F n f ≠ ⊥ := by
  intro h
  have hm := mem_generatedOperatorRealization F n f
  rw [h] at hm
  exact hf hm

end Langlands.Automorphic
