import Langlands.BushnellKutzko.AdjointCriticalExponent
import Langlands.BushnellKutzko.TameCorestriction

/-! # Adjoint lattice exactness (Bushnell–Kutzko 1993, §1.4; T2) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV uE uA

/-- Elementwise full content of `0 → X/D → P/R → Q/T → 0` with the maps induced
by the additive maps `f,g`. The conditions include well-definedness of both quotient maps,
injectivity of the first, surjectivity of the second, and middle exactness.
This is internal notation for the quotient-lattice sequences of BK93 §1.4. -/
def QuotientLatticeExact {A : Type uA} [AddCommGroup A] (f g : A → A)
    (X D P R Q T : AddSubgroup A) : Prop :=
  D ≤ X ∧ R ≤ P ∧ T ≤ Q ∧
  (∀ x ∈ X, f x ∈ P) ∧ (∀ x ∈ D, f x ∈ R) ∧
  (∀ y ∈ P, g y ∈ Q) ∧ (∀ y ∈ R, g y ∈ T) ∧
  (∀ x ∈ X, f x ∈ R ↔ x ∈ D) ∧
  (∀ z ∈ Q, ∃ y ∈ P, g y - z ∈ T) ∧
  (∀ y ∈ P, g y ∈ T ↔ ∃ x ∈ X, y - f x ∈ R)

/-- **BK93 (1.4.4), (1.4.7), (1.4.10), pp. 36–38 (T2).**
Intersection, existence of the critical maximum, and all four exact sequences. -/
def AdjointExactnessStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (E : Type uE) [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
    (𝓛 : LatticeChain 𝒪[F] F V) (β : E),
    Algebra.adjoin F ({β} : Set E) = ⊤ →
    (¬ ∃ a : F, algebraMap F E a = β) →
    (∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer) →
    let b := subfieldEmbedding F E V β
    let N := adjointLattice 𝓛 b
    let P := 𝓛.endFiltration
    let Q := centralizerLattice 𝓛 b
    let C := criticalIndexSet 𝓛 b
    (⨅ k : ℤ, N k) = Q 0 ∧
    C.Nonempty ∧ BddAbove C ∧
    (∃ k₀ : ℤ, IsGreatest C k₀ ∧ criticalExponent 𝓛 b = (k₀ : WithBot ℤ)) ∧
    ∀ (s : TameCorestriction 𝒪[F] F E V) (m k r : ℤ),
      criticalExponent 𝓛 b ≤ (k : WithBot ℤ) → 1 ≤ r →
      let a := adjointMap 𝒪[F] b
      let t := fun x => (s x).restrictScalars F
      QuotientLatticeExact a t
        (N k).toAddSubgroup (N (k + r)).toAddSubgroup
        (P k).toAddSubgroup (P (k + r)).toAddSubgroup
        (Q k).toAddSubgroup (Q (k + r)).toAddSubgroup ∧
      QuotientLatticeExact a t
        (N k).toAddSubgroup (Q 0).toAddSubgroup
        (P k).toAddSubgroup ⊥ (Q k).toAddSubgroup ⊥ ∧
      QuotientLatticeExact a t
        (Q m * N k).toAddSubgroup (Q m).toAddSubgroup
        (P (m + k)).toAddSubgroup ⊥ (Q (m + k)).toAddSubgroup ⊥ ∧
      QuotientLatticeExact a t
        (Q m * N k).toAddSubgroup (Q m * N (k + 1)).toAddSubgroup
        (P (m + k)).toAddSubgroup (P (m + k + 1)).toAddSubgroup
        (Q (m + k)).toAddSubgroup (Q (m + k + 1)).toAddSubgroup

end Langlands.BushnellKutzko
