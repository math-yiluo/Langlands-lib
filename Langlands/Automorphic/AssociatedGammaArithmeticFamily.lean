import Langlands.Automorphic.AssociatedGammaArithmeticTwist
import Langlands.Automorphic.AssociatedGammaEulerFamily
import Langlands.Global.Factors.RelativeWeilFunctionalEquationProof

/-!
# The arithmetic Hecke Euler family of a pair of relative Weil representations

For continuous representations `S`, `S'` of `W_{E/F}`, local maps `ι_z`, local-constant
systems and additive components at every finite place, and the archimedean block of the
proved global functional equation `RelativeWeilTwistFunctionalEquationStatement`, the local
factors at a Hecke character `χ` are: the archimedean block, independent of `χ`; and at a
finite place `z` arithmetic local factors of the twisted pair `((χ ∘ τ_F) ⊗ S, S')` along
`ι_z`, chosen so that they depend on `χ` only through `χ_z`.
-/

noncomputable section

set_option autoImplicit false

open scoped Classical

universe u uV uE

namespace Langlands.ClassFieldTheory.Global.RelativeWeilGroup

open Langlands.Global Langlands.Global.CompletionPadic
open Langlands.Global.FunctionalEquationComparison Langlands.Global.AdelicFunctoriality

variable {c : FundamentalClass.ClassFamily.{u}} {F E : Type u} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E] [IsGalois F E]

instance _root_.Langlands.Global.FunctionalEquationComparison.LocalFactors.instNonempty :
    Nonempty LocalFactors :=
  ⟨⟨fun _ => 1, fun _ => 1, fun _ => 1⟩⟩

/-- Local data at every finite place for the arithmetic family of `(S, S')`. -/
structure ArithmeticTwistSetup (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)) where
  hS : S.IsContinuous
  hS' : S'.IsContinuous
  place : ∀ z : FinitePlace F, FinitePlacesAbove E z
  candidate : ∀ z, LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z (place z).1)
  localMap : ∀ z : FinitePlace F, Weil.Local.localWeilGroup (padicField z) →ₜ*
    RelativeWeilGroup c F E
  localMap_spec : ∀ z, IsLocalRelativeWeilMap z (place z).1 (candidate z) (localMap z)
  additive : ∀ z : FinitePlace F, Correspondence.NontrivialAdditiveCharacter (padicField z)
  additive_spec : ∀ z, IsCanonicalFiniteAdditiveComponent ψ z (additive z)
  family : ∀ z : FinitePlace F, LocalFactor.CommonClosure.ReciprocityFamily (padicField z)
  system : ∀ z : FinitePlace F, LocalFactor.NonabelianSystem.Assignment.{u, uE} (padicField z)
  system_spec : ∀ z, LocalFactor.NonabelianSystem.IsSystem (padicField z) (family z) (system z)

namespace ArithmeticTwistSetup

variable {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
  {S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
  (A : ArithmeticTwistSetup.{u, uV, uE} ψ S S')

/-- `f` is a factor triple at `z` of the twist by some global character with local
component `η`. -/
def IsLocalTwistFactors (z : FinitePlace F) (η : (FiniteCompletion F z)ˣ →ₜ* ℂˣ)
    (f : LocalFactors) : Prop :=
  ∃ χ' : HeckeCharacter F, χ'.finiteComponent z = η ∧
    IsArithmeticPairLocalFactors.{u, uV, uE} (padicField z) (A.family z) (A.system z)
      (A.system_spec z) (A.additive z)
      (localPairClass (FiniteRepresentation.twist (reciprocityCharacter c F E χ') S)
        (A.localMap z))
      (localPairClass S' (A.localMap z))
      (localPairClass (FiniteRepresentation.twist (reciprocityCharacter c F E χ') S).dual
        (A.localMap z))
      (localPairClass S'.dual (A.localMap z)) f

/-- The finite factor at `z`, depending on `χ` only through `χ_z`. -/
def finiteFactors (χ : HeckeCharacter F) (z : FinitePlace F) : LocalFactors :=
  Classical.epsilon (A.IsLocalTwistFactors z (χ.finiteComponent z))

/-- The local factors of the arithmetic family, with archimedean block `arch`. -/
def localFactors (arch : NumberField.InfinitePlace F → LocalFactors) (χ : HeckeCharacter F) :
    AllPlaces F → LocalFactors :=
  Sum.elim arch (A.finiteFactors χ)

theorem localFactors_inl (arch : NumberField.InfinitePlace F → LocalFactors)
    (χ : HeckeCharacter F) (w : NumberField.InfinitePlace F) :
    A.localFactors arch χ (.inl w) = A.localFactors arch 1 (.inl w) := rfl

theorem localFactors_inr_of_finiteComponent_eq (arch : NumberField.InfinitePlace F → LocalFactors)
    {χ χ' : HeckeCharacter F} {z : FinitePlace F}
    (h : χ.finiteComponent z = χ'.finiteComponent z) :
    A.localFactors arch χ (.inr z) = A.localFactors arch χ' (.inr z) := by
  simp only [localFactors, Sum.elim_inr, finiteFactors, h]

/-- The chosen finite factors are arithmetic local factors of the twist by `χ` itself. -/
theorem finiteFactors_spec
    (hEps : Correspondence.ArithmeticPairEpsilonExistenceStatement.{u, uV, uE})
    (χ : HeckeCharacter F) (z : FinitePlace F) :
    IsArithmeticPairLocalFactors.{u, uV, uE} (padicField z) (A.family z) (A.system z)
      (A.system_spec z) (A.additive z)
      (localPairClass (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S)
        (A.localMap z))
      (localPairClass S' (A.localMap z))
      (localPairClass (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S).dual
        (A.localMap z))
      (localPairClass S'.dual (A.localMap z)) (A.finiteFactors χ z) := by
  have hex : ∃ f, A.IsLocalTwistFactors z (χ.finiteComponent z) f := by
    obtain ⟨f, hf⟩ := exists_isArithmeticPairLocalFactors hEps A.hS A.hS' (A.localMap_spec z)
      (A.family z) (A.system z) (A.system_spec z) (A.additive z) χ
    exact ⟨f, χ, rfl, hf⟩
  obtain ⟨χ', hχ', hf⟩ := Classical.epsilon_spec hex
  have hg := reciprocityCharacter_comp_eq_of_finiteComponent_eq (A.localMap_spec z)
    (A.family z) (A.system_spec z).1 hχ'
  rw [localPairClass_twist_congr S (A.localMap z) hg,
    localPairClass_twist_dual_congr S (A.localMap z) hg] at hf
  exact hf

/-- The chosen finite factors satisfy the factor hypothesis of the global equation. -/
theorem isTwistedRelativePairFactorsAt
    (hEps : Correspondence.ArithmeticPairEpsilonExistenceStatement.{u, uV, uE})
    (χ : HeckeCharacter F) (z : FinitePlace F) :
    IsTwistedRelativePairFactorsAt.{u, uV, uE} c E ψ S S' χ z (A.finiteFactors χ z) :=
  ⟨A.place z, A.candidate z, A.localMap z, A.localMap_spec z, A.additive z, A.family z,
    A.system z, A.system_spec z, A.additive_spec z, A.finiteFactors_spec hEps χ z⟩

/-- **Engine inputs.** With the archimedean block and finite set of the proved global
functional equation, the family satisfies the engine inputs for every finite-order `χ`
trivial at infinity and every `B ⊇ T₀` outside which `χ` is unramified. -/
theorem exists_engineInputs
    (hEps : Correspondence.ArithmeticPairEpsilonExistenceStatement.{u, uV, uE})
    (hc : IsArithmeticClassFamily c) (hψ : ∃ x : Adeles F, ψ x ≠ 1)
    (hdiag : ∀ x : F, ψ (diagonal F x) = 1) :
    ∃ (T₀ : Finset (FinitePlace F)) (arch : NumberField.InfinitePlace F → LocalFactors),
      ∀ χ : HeckeCharacter F, χ.HasFiniteOrder → χ.HasPrescribedInfinityComponent 1 →
      ∀ B : Finset (FinitePlace F), T₀ ⊆ B → (∀ z ∉ B, χ.IsUnramifiedAt z) →
        HeckeEulerFamily.HasEngineInputs (A.localFactors arch χ) B := by
  obtain ⟨T₀, arch, h⟩ := relativeWeilTwistFunctionalEquation.{u, uV, uE} c hc F E ψ hψ hdiag
    S S' A.hS A.hS'
  refine ⟨T₀, arch, fun χ hχ hχ' B hB hunr => ?_⟩
  obtain ⟨σ, Lp, Lpd, hA, hE, hF⟩ := h χ hχ hχ' B hB hunr (A.finiteFactors χ)
    (A.isTwistedRelativePairFactorsAt hEps χ)
  exact ⟨σ, Lp, Lpd, hA, hE, hF⟩

end ArithmeticTwistSetup

end Langlands.ClassFieldTheory.Global.RelativeWeilGroup
