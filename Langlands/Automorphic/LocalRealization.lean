import Langlands.Automorphic.TensorRealization

/-! # Actual local subspaces and tensor-slice realizations in automorphic forms -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL
open ContinuousRationalFunctions

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

local instance localRealizationRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance localRealizationContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance localRealizationSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance localRealizationFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

/-- A subspace of actual forms stable under the specified completed-local group. -/
abbrev LocalRealization (v : FinitePlace F) :=
  Subrepresentation (automorphicLocalRightAction F n v)

namespace LocalRealization

variable {F n} {v : FinitePlace F} (S : LocalRealization F n v)

abbrev Space := S.toSubmodule

local instance localRealizationSpaceAddCommGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _

abbrev Action := Representation ℂ (FiniteLocalGL F n v) S.Space

/-- The local action is inherited from actual positive right translation. -/
def representation : S.Action := S.toRepresentation

/-- The actual embedding into automorphic forms. -/
def inclusion : S.representation.IntertwiningMap (automorphicLocalRightAction F n v) where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := by ext; rfl

theorem inclusion_injective : Function.Injective S.inclusion := Subtype.val_injective

/-- Smoothness follows from the embedding, with no additional hypothesis. -/
theorem isSmooth : Langlands.IsSmooth S.representation :=
  Langlands.isSmooth_of_injective S.inclusion S.inclusion_injective
    (automorphicLocalRightAction_isSmooth F n v)

def smoothRepresentation : Langlands.SmoothRep ℂ (FiniteLocalGL F n v) :=
  Langlands.SmoothRep.of S.representation S.isSmooth

/-- Forget the embedded form subspace and retain its local smooth class. -/
def isoClass : Langlands.SmoothRep.IsoClass.{0, uF, uF} ℂ (FiniteLocalGL F n v) :=
  Langlands.SmoothRep.isoClass S.smoothRepresentation

theorem isoClass_eq_iff (T : LocalRealization F n v) :
    S.isoClass = T.isoClass ↔ Nonempty (S.representation.Equiv T.representation) := by
  rw [isoClass, isoClass, Langlands.SmoothRep.isoClass_eq_iff]
  exact ⟨fun ⟨e⟩ => ⟨Langlands.SmoothRep.equivOfIso e⟩,
    fun ⟨e⟩ => ⟨Langlands.SmoothRep.mkIso e⟩⟩

/-- The faithful continuous-function realization of the local subspace. -/
def toContinuous : S.Space →ₗ[ℂ] ContinuousRationalFunctions F n :=
  (automorphicToContinuous F n).comp S.inclusion.toLinearMap

theorem toContinuous_injective : Function.Injective S.toContinuous :=
  (automorphicToContinuous_injective F n).comp S.inclusion_injective

@[simp]
theorem evaluate_representation (g : FiniteLocalGL F n v) (f : S.Space)
    (a : AdelicGL F n) :
    evaluate F n (S.toContinuous (S.representation g f)) a =
      evaluate F n (S.toContinuous f)
        (a * AdelicGL.ofFinite F n (localInclusion F n v g)) := rfl

end LocalRealization

/-- Restrict the action of a finite adelic realization, retaining its whole carrier. -/
def FiniteRealization.toLocal (S : FiniteRealization F n) (v : FinitePlace F) :
    LocalRealization F n v where
  toSubmodule := S.toSubmodule
  apply_mem_toSubmodule g _ hf := S.apply_mem_toSubmodule (localInclusion F n v g) hf

@[simp]
theorem FiniteRealization.mem_toLocal (S : FiniteRealization F n) (v : FinitePlace F)
    (f : AutomorphicForms F n) : f ∈ S.toLocal F n v ↔ f ∈ S := Iff.rfl

@[simp]
theorem FiniteRealization.toLocal_representation (S : FiniteRealization F n)
    (v : FinitePlace F) :
    (S.toLocal F n v).representation = S.localRepresentation v := rfl

namespace LocalRealization

variable {F n} {v : FinitePlace F} (S : LocalRealization F n v)

/-- Central character remains a condition on the embedded forms. -/
def HasCentralCharacter (χ : NumberField.IdeleClassGroup (NumberField.RingOfIntegers F) F →ₜ* ℂˣ) :
    Prop :=
  S ≤ FiniteRealization.toLocal F n (centralCharacterAutomorphicSubrepresentation F n χ) v

theorem centralCharacter_evaluate
    (χ : NumberField.IdeleClassGroup (NumberField.RingOfIntegers F) F →ₜ* ℂˣ)
    (hS : S.HasCentralCharacter χ) (f : S.Space)
    (z : NumberField.IdeleGroup (NumberField.RingOfIntegers F) F) (a : AdelicGL F n) :
    evaluate F n (S.toContinuous f) (AdelicGL.scalar F n z * a) =
      (centralIdeleCharacter F χ z : ℂ) * evaluate F n (S.toContinuous f) a :=
  hS f.property z a

variable [CompactSpace (AdeleQuotient F)]

/-- Cuspidality likewise refers to the actual normalized constant terms. -/
def IsCuspidal : Prop :=
  S ≤ FiniteRealization.toLocal F n (cuspidalAutomorphicSubrepresentation F n) v

theorem constantTerm_eq_zero (hS : S.IsCuspidal)
    {a b : ℕ} (h : a + b = n) (ha : 0 < a) (hb : 0 < b)
    (f : S.Space) (g : AdelicGL F n) :
    constantTerm F n h (S.toContinuous f) g = 0 :=
  hS f.property a b h ha hb g

end LocalRealization

section Image

variable {v : FinitePlace F} {V : Type uV} [AddCommGroup V] [Module ℂ V]

abbrev LocalRealizationMap (ρ : Representation ℂ (FiniteLocalGL F n v) V) :=
  ρ.IntertwiningMap (automorphicLocalRightAction F n v)

abbrev LocalRealizationMap.IsInjective {ρ : Representation ℂ (FiniteLocalGL F n v) V}
    (T : LocalRealizationMap F n ρ) : Prop := Function.Injective T

abbrev LocalRealization.Equivalence (S : LocalRealization F n v)
    (ρ : Representation ℂ (FiniteLocalGL F n v) V) := ρ.Equiv S.representation

/-- The actual local invariant range of a form-valued intertwiner. -/
def localRealizationImage {ρ : Representation ℂ (FiniteLocalGL F n v) V}
    (T : LocalRealizationMap F n ρ) : LocalRealization F n v := T.range

/-- A faithful local model is genuinely equivalent to its image. -/
def localRealizationImageEquiv {ρ : Representation ℂ (FiniteLocalGL F n v) V}
    (T : LocalRealizationMap F n ρ) (hT : LocalRealizationMap.IsInjective F n T) :
    (localRealizationImage F n T).Equivalence F n ρ :=
  Representation.Equiv.mk (LinearEquiv.ofInjective T.toLinearMap hT) (by
    intro g
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _ T g x)

@[simp]
theorem inclusion_localRealizationImageEquiv
    {ρ : Representation ℂ (FiniteLocalGL F n v) V}
    (T : LocalRealizationMap F n ρ) (hT : LocalRealizationMap.IsInjective F n T) (x : V) :
    (localRealizationImage F n T).inclusion (localRealizationImageEquiv F n T hT x) =
      T x := rfl

end Image

namespace FiniteTensorRealization

open Langlands.RestrictedTensor

variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable (ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v))
variable (E : Finset (FinitePlace F)) (e : ∀ v, V v)
variable (he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v)
variable (hne : ∀ v ∉ E, e v ≠ 0)

/-- Ordinary nonzeroness of a complementary vector, hiding its large zero instance. -/
abbrev TailNonzero (v : FinitePlace F) (y : LocalTensorTail (K := ℂ) F E v e) :
    Prop := y ≠ 0

/-- The local slice as an embedded subspace of actual forms. -/
def sliceRealization (T : Map F n ρ E e he) (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) : LocalRealization F n v :=
  localRealizationImage F n (localSlice F n ρ E e he hne T v y)

/-- Every slice lies in the full finite adelic image, after local restriction. -/
theorem sliceRealization_le (T : Map F n ρ E e he) (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    sliceRealization F n ρ E e he hne T v y ≤
      (finiteRealizationImage F n T).toLocal F n v := by
  rintro f ⟨x, rfl⟩
  exact (mem_image_iff F n ρ E e he hne T v _).mpr ⟨x ⊗ₜ[ℂ] y, rfl⟩

theorem sliceRealization_hasCentralCharacter
    (T : Map F n ρ E e he) (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (χ : NumberField.IdeleClassGroup (NumberField.RingOfIntegers F) F →ₜ* ℂˣ)
    (hχ : (finiteRealizationImage F n T).HasCentralCharacter χ) :
    (sliceRealization F n ρ E e he hne T v y).HasCentralCharacter χ :=
  fun _ hf => hχ (sliceRealization_le F n ρ E e he hne T v y hf)

theorem sliceRealization_isCuspidal [CompactSpace (AdeleQuotient F)]
    (T : Map F n ρ E e he) (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hC : (finiteRealizationImage F n T).IsCuspidal) :
    (sliceRealization F n ρ E e he hne T v y).IsCuspidal :=
  fun _ hf => hC (sliceRealization_le F n ρ E e he hne T v y hf)

/-- A nonzero complementary vector gives an actual copy of the local factor. -/
def sliceEquiv (T : Map F n ρ E e he) (hT : IsInjective F n ρ E e he T)
    (v : FinitePlace F) (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : TailNonzero F E e v y) :
    (sliceRealization F n ρ E e he hne T v y).Equivalence F n (ρ v) :=
  localRealizationImageEquiv F n (localSlice F n ρ E e he hne T v y)
    (localSlice_injective F n ρ E e he hne T hT v y hy)

@[simp]
theorem inclusion_sliceEquiv (T : Map F n ρ E e he) (hT : IsInjective F n ρ E e he T)
    (v : FinitePlace F) (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : TailNonzero F E e v y) (x : V v) :
    (sliceRealization F n ρ E e he hne T v y).inclusion
        (sliceEquiv F n ρ E e he hne T hT v y hy x) =
      localSlice F n ρ E e he hne T v y x := rfl

/-- The comparison concerns the two actual slice images. -/
abbrev SliceChangeEquivalence
    (T T' : Map F n ρ E e he) (v : FinitePlace F)
    (y y' : LocalTensorTail (K := ℂ) F E v e) :=
  (sliceRealization F n ρ E e he hne T v y).representation.Equiv
    (sliceRealization F n ρ E e he hne T' v y').representation

/-- Two faithful embeddings and two nonzero tails give equivalent local copies
of the same specified factor; their embedded form subspaces need not be equal. -/
def sliceChangeEquiv
    (T T' : Map F n ρ E e he)
    (hT : IsInjective F n ρ E e he T) (hT' : IsInjective F n ρ E e he T')
    (v : FinitePlace F) (y y' : LocalTensorTail (K := ℂ) F E v e)
    (hy : TailNonzero F E e v y) (hy' : TailNonzero F E e v y') :
    SliceChangeEquivalence F n ρ E e he hne T T' v y y' :=
  (sliceEquiv F n ρ E e he hne T hT v y hy).symm.trans
    (sliceEquiv F n ρ E e he hne T' hT' v y' hy')

@[simp]
theorem sliceChangeEquiv_apply
    (T T' : Map F n ρ E e he)
    (hT : IsInjective F n ρ E e he T) (hT' : IsInjective F n ρ E e he T')
    (v : FinitePlace F) (y y' : LocalTensorTail (K := ℂ) F E v e)
    (hy : TailNonzero F E e v y) (hy' : TailNonzero F E e v y') (x : V v) :
    sliceChangeEquiv F n ρ E e he hne T T' hT hT' v y y' hy hy'
        (sliceEquiv F n ρ E e he hne T hT v y hy x) =
      sliceEquiv F n ρ E e he hne T' hT' v y' hy' x := by
  change (sliceEquiv F n ρ E e he hne T' hT' v y' hy')
    ((sliceEquiv F n ρ E e he hne T hT v y hy).symm
      (sliceEquiv F n ρ E e he hne T hT v y hy x)) = _
  rw [Representation.Equiv.symm_apply_apply]

theorem slice_isoClass_eq
    (T T' : Map F n ρ E e he)
    (hT : IsInjective F n ρ E e he T) (hT' : IsInjective F n ρ E e he T')
    (v : FinitePlace F) (y y' : LocalTensorTail (K := ℂ) F E v e)
    (hy : TailNonzero F E e v y) (hy' : TailNonzero F E e v y') :
    (sliceRealization F n ρ E e he hne T v y).isoClass =
      (sliceRealization F n ρ E e he hne T' v y').isoClass :=
  (LocalRealization.isoClass_eq_iff _ _).mpr
    ⟨sliceChangeEquiv F n ρ E e he hne T T' hT hT' v y y' hy hy'⟩

/-- Away from the exceptional set, each faithful nonzero slice has a nonzero
vector fixed by the actual integral local subgroup. -/
theorem slice_exists_integral_fixed
    (T : Map F n ρ E e he) (hT : IsInjective F n ρ E e he T)
    (v : FinitePlace F) (hv : v ∉ E)
    (y : LocalTensorTail (K := ℂ) F E v e) (hy : TailNonzero F E e v y) :
    ∃ f : (sliceRealization F n ρ E e he hne T v y).Space,
      f ≠ 0 ∧ ∀ g ∈ localIntegral F n v,
        (sliceRealization F n ρ E e he hne T v y).representation g f = f := by
  let q := sliceEquiv F n ρ E e he hne T hT v y hy
  refine ⟨q (e v), ?_, ?_⟩
  · intro h
    exact hne v hv (q.injective (h.trans q.toLinearEquiv.map_zero.symm))
  · intro g hg
    have h := LinearMap.congr_fun (q.isIntertwining' g) (e v)
    change q (ρ v g (e v)) = _ at h
    rw [he v hv g hg] at h
    exact h.symm

end FiniteTensorRealization
end Langlands.Automorphic
