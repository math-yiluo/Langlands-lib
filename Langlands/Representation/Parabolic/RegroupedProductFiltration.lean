import Langlands.Representation.Parabolic.OrderedProductRegroupingProof
import Langlands.Representation.Parabolic.OrderedProductRegroupingEquivalence
import Langlands.Representation.Parabolic.ProductInductionFiltration
import Langlands.Representation.Filtration.ObjectTransport

/-! Actual filtrations of the original product through ordered regrouping. -/

noncomputable section

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV uW uX uY uZ

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  (B D : BlockShape n) (S : BlockRefinement D)
  (e : ((k : Fin D.length) × Fin (S k).length) ≃ Fin B.length)
  (h : ∀ a, (S a.1).size a.2 = B.size (e a))
  (hc : ∀ k l (x : Fin ((S k).size l)),
    D.index k ((S k).index l x) = B.index (e ⟨k,l⟩) (Fin.cast (h ⟨k,l⟩) x))
  (σ : letI := T.topology
    ∀ k, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size k) F.Carrier))
  {W : Fin D.length → Type uW}
  [∀ k, AddCommGroup (W k)] [∀ k, Module ℂ (W k)]
  (τ : ∀ k, Representation ℂ (GeneralLinear (D.size k) F.Carrier) (W k))
  (δ : letI := T.topology
    ∀ k, Representation.Equiv
      (((T.normalizedProductInductionFunctor.{uF,uV} (S k)).obj
        (fun l => (h ⟨k,l⟩).symm ▸ σ (e ⟨k,l⟩))).representation) (τ k))
  (j : Fin D.length) {m : ℕ} (s : ObjectRepFiltration (Rep.of (τ j)) m)

/-- Pull the outer slot filtration back to the original flat normalized product
using the independently proved ordered regrouping equivalence. -/
def regroupedProductSlotFiltration :
    letI := T.topology
    ObjectRepFiltration
      (Rep.of (((T.normalizedProductInductionFunctor B).obj σ).representation)) m := by
  letI := T.topology
  exact LengthTwo.transport
    (T.normalizedProductRegroupingToEquiv (orderedProductRegrouping F T)
      B D S e h hc σ τ δ).symm
    (normalizedProductSlotFiltration T D τ j s)

/-- The original product is filtered by the preimages of the actual outer
product subspaces under the actual regrouping map. -/
@[simp]
theorem mem_regroupedProductSlotFiltration
    (i : Fin (m + 1)) :
    letI := T.topology
    ∀ v,
      v ∈ (regroupedProductSlotFiltration T B D S e h hc σ τ δ j s).subrepresentation i ↔
        T.normalizedProductRegroupingToEquiv (orderedProductRegrouping F T)
          B D S e h hc σ τ δ v ∈
            (normalizedProductSlotFiltration T D τ j s).subrepresentation i := by
  let := T.topology
  intro v
  rfl

variable {X : Fin D.length → Type uX}
  [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
  (υ : ∀ k, Representation ℂ (GeneralLinear (D.size k) F.Carrier) (X k))

/-- Identify an actual quotient of the original flat product with a replacement
outer product when the slot quotient and the other factors are equivalent. -/
def regroupedProductSlotFiltrationGradedEquiv (i : Fin m)
    (a : ∀ k : ({j}ᶜ : Set (Fin D.length)), (τ k).Equiv (υ k))
    (b : (s.gradedRepresentation i).ρ.Equiv (υ j)) :
    letI := T.topology
    (∀ k, IsSmooth (τ k)) →
      ((regroupedProductSlotFiltration T B D S e h hc σ τ δ j s).gradedRepresentation i).ρ.Equiv
        (T.normalizedProductInduced D υ) := by
  letI := T.topology
  intro hτ
  exact (ObjectRepFiltration.equivTransportGradedEquiv
    (normalizedProductSlotFiltration T D τ j s)
    (T.normalizedProductRegroupingToEquiv (orderedProductRegrouping F T)
      B D S e h hc σ τ δ).symm i).symm.trans
    (normalizedProductSlotFiltrationGradedEquivOfFamily T D τ j s υ i a b hτ)

/-- Map an actual quotient of the original flat product into the full outer
replacement product through the transported quotient equivalence. -/
def regroupedProductSlotFiltrationGradedMap (i : Fin m)
    (a : ∀ k : ({j}ᶜ : Set (Fin D.length)), (τ k).Equiv (υ k))
    (b : (s.gradedRepresentation i).ρ.IntertwiningMap (υ j)) :
    letI := T.topology
    (∀ k, IsSmooth (τ k)) →
      ((regroupedProductSlotFiltration T B D S e h hc σ τ δ j s).gradedRepresentation i).ρ.IntertwiningMap
        (T.normalizedProductInduced D υ) := by
  letI := T.topology
  intro hτ
  exact (normalizedProductSlotFiltrationGradedMap T D τ j s υ i a b hτ).comp
    (ObjectRepFiltration.equivTransportGradedEquiv
      (normalizedProductSlotFiltration T D τ j s)
      (T.normalizedProductRegroupingToEquiv (orderedProductRegrouping F T)
        B D S e h hc σ τ δ).symm i).symm.toIntertwiningMap

/-- Injectivity of the slot quotient map survives regrouping, tensoring with all
outside factors and actual normalized induction. -/
theorem regroupedProductSlotFiltrationGradedMap_injective (i : Fin m)
    (a : ∀ k : ({j}ᶜ : Set (Fin D.length)), (τ k).Equiv (υ k))
    (b : (s.gradedRepresentation i).ρ.IntertwiningMap (υ j))
    (hb : Function.Injective b) :
    letI := T.topology
    ∀ hτ : ∀ k, IsSmooth (τ k),
      Function.Injective
        (regroupedProductSlotFiltrationGradedMap T B D S e h hc σ τ δ j s υ i a b hτ) := by
  let := T.topology
  intro hτ
  exact (normalizedProductSlotFiltrationGradedMap_injective
    T D τ j s υ i a b hb hτ).comp
    (ObjectRepFiltration.equivTransportGradedEquiv
      (normalizedProductSlotFiltration T D τ j s)
      (T.normalizedProductRegroupingToEquiv (orderedProductRegrouping F T)
        B D S e h hc σ τ δ).symm i).symm.injective

variable {Y : Type uY} [AddCommGroup Y] [Module ℂ Y]

include S e h hc δ in
/-- An irreducible representation embedded in the original flat product embeds
into one of the actual replacement outer products. The replacement carriers
and maps may depend on the filtration grade. -/
theorem exists_injective_regroupedProduct_replacement
    {U : Fin m → Fin D.length → Type uX}
    [∀ i k, AddCommGroup (U i k)] [∀ i k, Module ℂ (U i k)]
    (ν : ∀ i k, Representation ℂ (GeneralLinear (D.size k) F.Carrier) (U i k))
    (a : ∀ i, ∀ k : ({j}ᶜ : Set (Fin D.length)), (τ k).Equiv (ν i k))
    (b : ∀ i, (s.gradedRepresentation i).ρ.IntertwiningMap (ν i j))
    (hb : ∀ i, Function.Injective (b i))
    (π : Representation ℂ (GeneralLinear n F.Carrier) Y) :
    letI := T.topology
    (∀ k, IsSmooth (τ k)) → π.IsIrreducible →
      ∀ f : π.IntertwiningMap
        (((T.normalizedProductInductionFunctor B).obj σ).representation),
        Function.Injective f →
          ∃ i : Fin m, ∃ g : π.IntertwiningMap (T.normalizedProductInduced D (ν i)),
            Function.Injective g := by
  let := T.topology
  intro hτ hπ f hf
  obtain ⟨i, g, hg⟩ :=
    (regroupedProductSlotFiltration T B D S e h hc σ τ δ j s).exists_injective_graded f hπ hf
  exact ⟨i,
    (regroupedProductSlotFiltrationGradedMap T B D S e h hc σ τ δ j s
      (ν i) i (a i) (b i) hτ).comp g,
    (regroupedProductSlotFiltrationGradedMap_injective T B D S e h hc σ τ δ j s
      (ν i) i (a i) (b i) (hb i) hτ).comp hg⟩

include S e h hc δ in
/-- The selected outer replacement embedding transports to any supplied actual
full replacement representation equivalent to that outer product. -/
theorem exists_injective_regroupedProduct_target
    {U : Fin m → Fin D.length → Type uX}
    [∀ i k, AddCommGroup (U i k)] [∀ i k, Module ℂ (U i k)]
    (ν : ∀ i k, Representation ℂ (GeneralLinear (D.size k) F.Carrier) (U i k))
    (a : ∀ i, ∀ k : ({j}ᶜ : Set (Fin D.length)), (τ k).Equiv (ν i k))
    (b : ∀ i, (s.gradedRepresentation i).ρ.IntertwiningMap (ν i j))
    (hb : ∀ i, Function.Injective (b i))
    {Z : Fin m → Type uZ} [∀ i, AddCommGroup (Z i)] [∀ i, Module ℂ (Z i)]
    (ζ : ∀ i, Representation ℂ (GeneralLinear n F.Carrier) (Z i))
    (q : letI := T.topology
      ∀ i, (T.normalizedProductInduced D (ν i)).Equiv (ζ i))
    (π : Representation ℂ (GeneralLinear n F.Carrier) Y) :
    letI := T.topology
    (∀ k, IsSmooth (τ k)) → π.IsIrreducible →
      ∀ f : π.IntertwiningMap
        (((T.normalizedProductInductionFunctor B).obj σ).representation),
        Function.Injective f →
          ∃ i : Fin m, ∃ g : π.IntertwiningMap (ζ i), Function.Injective g := by
  let := T.topology
  intro hτ hπ f hf
  obtain ⟨i, g, hg⟩ := exists_injective_regroupedProduct_replacement
    T B D S e h hc σ τ δ j s ν a b hb π hτ hπ f hf
  exact ⟨i, (q i).toIntertwiningMap.comp g, (q i).injective.comp hg⟩

end Langlands.Parabolic
