import Langlands.Representation.Tensor.ExternalFiltration
import Langlands.Representation.Parabolic.InductionFiltration
import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Induction.Equivalences

/-! Actual slot filtrations in normalized induction of block factors. -/

noncomputable section

namespace Langlands.Parabolic

open GeneralLinear

universe uF uV uW uX

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)
  {V : Fin B.length → Type uV}
  [∀ h, AddCommGroup (V h)] [∀ h, Module ℂ (V h)]
  (ρ : ∀ h, Representation ℂ (GeneralLinear (B.size h) F.Carrier) (V h))
  (j : Fin B.length) {m : ℕ} (s : ObjectRepFiltration (Rep.of (ρ j)) m)

/-- Lift the actual slot filtration, then use value subspaces to filter the
actual normalized block-product induction. -/
def normalizedProductSlotFiltration :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ObjectRepFiltration (Rep.of (T.normalizedProductInduced B ρ)) m :=
  normalizedInductionFiltration T B (B.blockTensor ρ)
    (FiniteTensor.externalSlotFiltration ρ j s)

variable {W : Fin B.length → Type uW}
  [∀ h, AddCommGroup (W h)] [∀ h, Module ℂ (W h)]
  (σ : ∀ h, Representation ℂ (GeneralLinear (B.size h) F.Carrier) (W h))

/-- Identify an actual full-product quotient with the actual normalized product
of a supplied equivalent replacement family. -/
def normalizedProductSlotFiltrationGradedEquivOfFamily (i : Fin m)
    (e : ∀ h : ({j}ᶜ : Set (Fin B.length)), (ρ h).Equiv (σ h))
    (f : (s.gradedRepresentation i).ρ.Equiv (σ j)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (∀ h, IsSmooth (ρ h)) →
      ((normalizedProductSlotFiltration T B ρ j s).gradedRepresentation i).ρ.Equiv
        (T.normalizedProductInduced B σ) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  intro hρ
  exact (normalizedInductionFiltrationGradedEquiv T B (B.blockTensor ρ)
    (FiniteTensor.externalSlotFiltration ρ j s) i
    (FiniteTensor.isSmooth_external ρ hρ)).trans
      (T.normalizedParabolicInducedEquiv B
        (FiniteTensor.externalSlotFiltrationGradedEquivOfFamily ρ j s σ i e f))

/-- Induce the external quotient map after identifying the actual quotient of
the induced filtration. -/
def normalizedProductSlotFiltrationGradedMap (i : Fin m)
    (e : ∀ h : ({j}ᶜ : Set (Fin B.length)), (ρ h).Equiv (σ h))
    (f : (s.gradedRepresentation i).ρ.IntertwiningMap (σ j)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (∀ h, IsSmooth (ρ h)) →
      ((normalizedProductSlotFiltration T B ρ j s).gradedRepresentation i).ρ.IntertwiningMap
        (T.normalizedProductInduced B σ) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  intro hρ
  exact (T.normalizedParabolicInducedMap B
    (FiniteTensor.externalSlotFiltrationGradedMap ρ j s σ i e f)).comp
      (normalizedInductionFiltrationGradedEquiv T B (B.blockTensor ρ)
        (FiniteTensor.externalSlotFiltration ρ j s) i
        (FiniteTensor.isSmooth_external ρ hρ)).toIntertwiningMap

/-- Injectivity of the original slot-quotient map survives tensoring and actual
normalized parabolic induction. -/
theorem normalizedProductSlotFiltrationGradedMap_injective (i : Fin m)
    (e : ∀ h : ({j}ᶜ : Set (Fin B.length)), (ρ h).Equiv (σ h))
    (f : (s.gradedRepresentation i).ρ.IntertwiningMap (σ j))
    (hf : Function.Injective f) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ hρ : ∀ h, IsSmooth (ρ h),
      Function.Injective
        (normalizedProductSlotFiltrationGradedMap T B ρ j s σ i e f hρ) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro hρ
  exact (T.normalizedParabolicInducedMap_injective B
    (FiniteTensor.externalSlotFiltrationGradedMap ρ j s σ i e f)
    (FiniteTensor.externalSlotFiltrationGradedMap_injective ρ j s σ i e f hf)).comp
      (normalizedInductionFiltrationGradedEquiv T B (B.blockTensor ρ)
        (FiniteTensor.externalSlotFiltration ρ j s) i
        (FiniteTensor.isSmooth_external ρ hρ)).injective

variable {X : Type uX} [AddCommGroup X] [Module ℂ X]

/-- Choose an actual replacement product admitting the original irreducible
representation, from quotient embeddings supplied at each grade. Replacement
carriers may depend on the grade as well as the block. -/
theorem exists_injective_normalizedProduct_replacement
    {U : Fin m → Fin B.length → Type uW}
    [∀ i h, AddCommGroup (U i h)] [∀ i h, Module ℂ (U i h)]
    (τ : ∀ i h, Representation ℂ (GeneralLinear (B.size h) F.Carrier) (U i h))
    (e : ∀ i, ∀ h : ({j}ᶜ : Set (Fin B.length)), (ρ h).Equiv (τ i h))
    (f : ∀ i, (s.gradedRepresentation i).ρ.IntertwiningMap (τ i j))
    (hf : ∀ i, Function.Injective (f i))
    (π : Representation ℂ (GeneralLinear n F.Carrier) X) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (∀ h, IsSmooth (ρ h)) → π.IsIrreducible →
      ∀ a : π.IntertwiningMap (T.normalizedProductInduced B ρ),
        Function.Injective a →
          ∃ i : Fin m, ∃ b : π.IntertwiningMap (T.normalizedProductInduced B (τ i)),
            Function.Injective b := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro hρ hπ a ha
  obtain ⟨i, b, hb⟩ :=
    (normalizedProductSlotFiltration T B ρ j s).exists_injective_graded a hπ ha
  let c := normalizedProductSlotFiltrationGradedMap T B ρ j s (τ i) i (e i) (f i) hρ
  exact ⟨i, c.comp b,
    (normalizedProductSlotFiltrationGradedMap_injective T B ρ j s
      (τ i) i (e i) (f i) (hf i) hρ).comp hb⟩

end Langlands.Parabolic
