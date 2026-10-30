import Langlands.CategoryTheory.Renard.SimpleSupportSum
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Renard A.IX: canonical splitting by simple support

Definitions for the boxed definition on printed268/PDF274 of the French
edition dated 9 July 2026. The actual canonical maps use the public sums
`simpleSupportSum`, with their actual inclusions. The predicates assert
existence of exactly the coproducts they use, together with invertibility
of those maps. They do not assert any splitting theorem.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The complement of `S` inside the actual simple-object classes. -/
def simpleSupportComplement (S : Set (ObjectClass C)) : Set (ObjectClass C) :=
  simpleClasses C \ S

@[simp]
theorem mem_simpleSupportComplement (S : Set (ObjectClass C)) (q : ObjectClass C) :
    q ∈ simpleSupportComplement S ↔ q ∈ simpleClasses C ∧ q ∉ S :=
  Iff.rfl

theorem disjoint_simpleSupportComplement (S : Set (ObjectClass C)) :
    Disjoint S (simpleSupportComplement S) := by
  exact Set.disjoint_left.mpr fun _ hS hc => hc.2 hS

section Subset

variable (S : Set (ObjectClass C)) (X : C)
  [HasCoproduct fun P : simpleSupportSubobjects S X => ((P : Subobject X) : C)]
  [HasCoproduct fun P : simpleSupportSubobjects (simpleSupportComplement S) X =>
    ((P : Subobject X) : C)]

/-- The canonical map `E_S ⊕ E_(Irr \ S) ⟶ E`, determined by the actual
inclusions of the two supported sums. -/
def simpleSupportSubsetDesc :
    (simpleSupportSum S X : C) ⊞
      (simpleSupportSum (simpleSupportComplement S) X : C) ⟶ X :=
  biprod.desc (simpleSupportSum S X).arrow
    (simpleSupportSum (simpleSupportComplement S) X).arrow

@[reassoc (attr := simp)]
theorem inl_simpleSupportSubsetDesc :
    biprod.inl ≫ simpleSupportSubsetDesc S X = (simpleSupportSum S X).arrow := by
  simp [simpleSupportSubsetDesc]

@[reassoc (attr := simp)]
theorem inr_simpleSupportSubsetDesc :
    biprod.inr ≫ simpleSupportSubsetDesc S X =
      (simpleSupportSum (simpleSupportComplement S) X).arrow := by
  simp [simpleSupportSubsetDesc]

end Subset

/-- `S` splits `X`: `S` is a subset of `Irr(C)`, the two full supported
families have coproducts, and their actual canonical binary map is invertible.
Existence of these coproducts is asserted, never a vacuous antecedent. -/
@[pp_with_univ]
def SimpleSupportSubsetSplits (S : Set (ObjectClass C)) (X : C) : Prop :=
  S ⊆ simpleClasses C ∧
    ∃ (hS : HasCoproduct fun P : simpleSupportSubobjects S X =>
        ((P : Subobject X) : C))
      (hSc : HasCoproduct fun P :
          simpleSupportSubobjects (simpleSupportComplement S) X =>
        ((P : Subobject X) : C)),
      letI := hS
      letI := hSc
      IsIso (simpleSupportSubsetDesc S X)

/-- `S` splits the category when it splits every actual object. -/
@[pp_with_univ]
def SimpleSupportSubsetSplitsCategory (S : Set (ObjectClass C)) : Prop :=
  ∀ X : C, SimpleSupportSubsetSplits S X

/-- With the required actual coproducts available, subset splitting is
exactly the subset condition and invertibility of the canonical map. -/
theorem simpleSupportSubsetSplits_iff (S : Set (ObjectClass C)) (X : C)
    [HasCoproduct fun P : simpleSupportSubobjects S X => ((P : Subobject X) : C)]
    [HasCoproduct fun P : simpleSupportSubobjects (simpleSupportComplement S) X =>
      ((P : Subobject X) : C)] :
    SimpleSupportSubsetSplits S X ↔
      S ⊆ simpleClasses C ∧ IsIso (simpleSupportSubsetDesc S X) := by
  constructor
  · rintro ⟨hS, _, _, hIso⟩
    exact ⟨hS, hIso⟩
  · rintro ⟨hS, hIso⟩
    exact ⟨hS, inferInstance, inferInstance, hIso⟩

section Partition

variable {I : Type w}

/-- An actual partition of all simple-object classes into pairwise disjoint
sets. Empty indices and empty blocks are allowed. -/
@[pp_with_univ]
def IsSimpleSupportPartition (S : I → Set (ObjectClass C)) : Prop :=
  Pairwise (fun i j => Disjoint (S i) (S j)) ∧
    (⋃ i, S i) = simpleClasses C

/-- Each block of a support partition lies in `Irr(C)`. -/
theorem IsSimpleSupportPartition.subset {S : I → Set (ObjectClass C)}
    (h : IsSimpleSupportPartition S) (i : I) : S i ⊆ simpleClasses C := by
  intro q hq
  rw [← h.2]
  exact Set.mem_iUnion.mpr ⟨i, hq⟩

variable (S : I → Set (ObjectClass C)) (X : C)
  [∀ i : I, HasCoproduct fun P : simpleSupportSubobjects (S i) X =>
    ((P : Subobject X) : C)]
  [HasCoproduct fun i : I => (simpleSupportSum (S i) X : C)]

/-- The canonical map `∐ i, E_(S i) ⟶ E`, whose legs are the actual inclusions
of the supported sums. Its outer index universe is independent of `u,v`. -/
def simpleSupportPartitionDesc :
    (∐ fun i : I => (simpleSupportSum (S i) X : C)) ⟶ X :=
  Sigma.desc fun i => (simpleSupportSum (S i) X).arrow

@[reassoc (attr := simp)]
theorem ι_simpleSupportPartitionDesc (i : I) :
    Sigma.ι (fun j : I => (simpleSupportSum (S j) X : C)) i ≫
        simpleSupportPartitionDesc S X =
      (simpleSupportSum (S i) X).arrow := by
  simp [simpleSupportPartitionDesc]

end Partition

/-- A partition splits `X` when every supported sum exists, their outer
coproduct exists, and the actual canonical map from it to `X` is invertible.
All the required existence conditions are part of the proposition. -/
@[pp_with_univ]
def SimpleSupportPartitionSplits {I : Type w}
    (S : I → Set (ObjectClass C)) (X : C) : Prop :=
  IsSimpleSupportPartition S ∧
    ∃ hS : ∀ i : I, HasCoproduct fun P : simpleSupportSubobjects (S i) X =>
        ((P : Subobject X) : C),
      letI := hS
      ∃ hSum : HasCoproduct fun i : I => (simpleSupportSum (S i) X : C),
        letI := hSum
        IsIso (simpleSupportPartitionDesc S X)

/-- A support partition splits the category when it splits every actual object. -/
@[pp_with_univ]
def SimpleSupportPartitionSplitsCategory {I : Type w}
    (S : I → Set (ObjectClass C)) : Prop :=
  ∀ X : C, SimpleSupportPartitionSplits S X

/-- With the exact inner and outer coproducts available, partition splitting
is precisely the partition condition and invertibility of its canonical map. -/
theorem simpleSupportPartitionSplits_iff {I : Type w}
    (S : I → Set (ObjectClass C)) (X : C)
    [∀ i : I, HasCoproduct fun P : simpleSupportSubobjects (S i) X =>
      ((P : Subobject X) : C)]
    [HasCoproduct fun i : I => (simpleSupportSum (S i) X : C)] :
    SimpleSupportPartitionSplits S X ↔
      IsSimpleSupportPartition S ∧ IsIso (simpleSupportPartitionDesc S X) := by
  constructor
  · rintro ⟨hS, _, _, hIso⟩
    exact ⟨hS, hIso⟩
  · rintro ⟨hS, hIso⟩
    exact ⟨hS, inferInstance, inferInstance, hIso⟩

end

end Langlands.Renard
