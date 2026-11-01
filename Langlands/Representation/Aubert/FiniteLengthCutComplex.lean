import Langlands.Representation.Aubert.ActualCutComplex
import Langlands.Representation.Aubert.AlternatingOperator

/-! Finite group-algebra length of the actual cut-complex terms. -/

noncomputable section

namespace Langlands.Aubert

open scoped MonoidAlgebra

namespace FiniteProduct

universe uJ uG uM

variable {J : Type uJ} {G : Type uG} [Group G]
  {M : J → Type uM} [∀ j, AddCommGroup (M j)] [∀ j, Module ℂ (M j)]

/-- Coordinate evaluation on the actual pointwise product representation. -/
def evaluation (ρ : ∀ j, Representation ℂ G (M j)) (j : J) :
    (representation ρ).IntertwiningMap (ρ j) where
  toLinearMap := LinearMap.proj j
  isIntertwining' _ := rfl

/-- Comparison with the pointwise product of the actual group-algebra modules. -/
def groupModuleMap (ρ : ∀ j, Representation ℂ G (M j)) :
    (representation ρ).asModule →ₗ[ℂ[G]] ∀ j, (ρ j).asModule :=
  LinearMap.pi fun j =>
    Representation.IntertwiningMap.equivLinearMapAsModule _ _ (evaluation ρ j)

theorem groupModuleMap_injective (ρ : ∀ j, Representation ℂ G (M j)) :
    Function.Injective (groupModuleMap ρ) := by
  intro x y h
  apply (representation ρ).asModuleEquiv.injective
  funext j
  exact congrFun h j

variable [Finite J]

/-- A finite product of finite-length representations has finite group-algebra length. -/
theorem finiteLength (ρ : ∀ j, Representation ℂ G (M j))
    (hρ : ∀ j, IsFiniteLength ℂ[G] (ρ j).asModule) :
    IsFiniteLength ℂ[G] (representation ρ).asModule := by
  have : ∀ j, IsNoetherian ℂ[G] (ρ j).asModule :=
    fun j => (isFiniteLength_iff_isNoetherian_isArtinian.mp (hρ j)).1
  have : ∀ j, IsArtinian ℂ[G] (ρ j).asModule :=
    fun j => (isFiniteLength_iff_isNoetherian_isArtinian.mp (hρ j)).2
  have hprod : IsFiniteLength ℂ[G] (∀ j, (ρ j).asModule) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  exact hprod.of_injective (f := groupModuleMap ρ) (groupModuleMap_injective ρ)

end FiniteProduct

namespace ActualCutComplex

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {n : ℕ}

/-- Finite length on one actual normalized induction--Jacquet carrier. -/
theorem term_hasFiniteLength (B : BlockShape n) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)),
      A.HasFiniteLength → IsFiniteLength ℂ[GeneralLinear n F.Carrier]
        (Transition.term T B A.representation).asModule := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro A hA
  exact normalizedInductionJacquet_hasFiniteLength.{uF,uV} F T A hA B

/-- Each degree of the actual cut complex has finite length on finite-length input. -/
theorem degree_hasFiniteLength :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)),
      A.HasFiniteLength → ∀ k, (degreeObject T A.representation k).HasFiniteLength := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro A hA k
  let I := {s : Finset (Fin (n - 1)) // s.card = k}
  let τ := degreeRepresentation T A.representation k
  let ρ : ∀ s : I, Representation ℂ (GeneralLinear n F.Carrier) (Term T A.representation s.1) :=
    fun s => Transition.term T (shape s.1) A.representation
  let f : ∀ s : I, τ.IntertwiningMap (ρ s) := fun s =>
    { toLinearMap := LinearMap.proj s
      isIntertwining' _ := rfl }
  let L : τ.asModule →ₗ[ℂ[GeneralLinear n F.Carrier]] ∀ s : I, (ρ s).asModule :=
    LinearMap.pi fun s => Representation.IntertwiningMap.equivLinearMapAsModule _ _ (f s)
  have hL : Function.Injective L := by
    intro x y h
    apply τ.asModuleEquiv.injective
    funext s
    exact congrFun h s
  have hρ : ∀ s : I, IsFiniteLength ℂ[GeneralLinear n F.Carrier] (ρ s).asModule :=
    fun s => term_hasFiniteLength.{uF,uV} (n := n) F T (shape (n := n) s.1) A hA
  have : ∀ s : I, IsNoetherian ℂ[GeneralLinear n F.Carrier] (ρ s).asModule :=
    fun s => (isFiniteLength_iff_isNoetherian_isArtinian.mp (hρ s)).1
  have : ∀ s : I, IsArtinian ℂ[GeneralLinear n F.Carrier] (ρ s).asModule :=
    fun s => (isFiniteLength_iff_isNoetherian_isArtinian.mp (hρ s)).2
  have hprod : IsFiniteLength ℂ[GeneralLinear n F.Carrier] (∀ s : I, (ρ s).asModule) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  exact hprod.of_injective (f := L) hL

/-- The actual degree as an object of finite group-algebra length. -/
def finiteDegree :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)),
      A.HasFiniteLength → ℕ →
        SmoothRep.FiniteLengthObject.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  fun A hA k => ⟨degreeObject T A.representation k, degree_hasFiniteLength.{uF,uV} F T A hA k⟩

end ActualCutComplex
end Langlands.Aubert
