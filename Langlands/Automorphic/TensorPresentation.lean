import Langlands.Automorphic.LocalRealization

/-! # Tensor presentations of specified finite automorphic realizations -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorPresentationRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance tensorPresentationContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorPresentationSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorPresentationFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

variable (ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v))
variable (E : Finset (FinitePlace F)) (e : ∀ v, V v)
variable (he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v)

/-- Presentation data includes an actual equivalence onto the specified form space.
Its existence is a separate mathematical obligation. -/
structure FiniteTensorPresentation (S : FiniteRealization F n) where
  reference_nonzero : ∀ v ∉ E, e v ≠ 0
  equiv : S.Equivalence F n (tensorRepresentation F n ρ E e he)

/-- A compact type for whole-carrier local comparison, retaining the tail. -/
abbrev FiniteTensorPresentation.LocalEquivalence
    (S : FiniteRealization F n) (v : FinitePlace F) :=
  (separatedLocalRepresentation F n ρ E v e).Equiv (S.localRepresentation v)

namespace FiniteTensorPresentation

variable {F n ρ E e he} {S : FiniteRealization F n}
variable (P : FiniteTensorPresentation F n ρ E e he S)

/-- Compose the given global equivalence with the actual inclusion into forms. -/
def toMap : FiniteTensorRealization.Map F n ρ E e he :=
  S.inclusion.comp P.equiv.toIntertwiningMap

theorem toMap_injective : FiniteTensorRealization.IsInjective F n ρ E e he P.toMap :=
  S.inclusion_injective.comp P.equiv.injective

@[simp]
theorem toMap_apply (x : Space ℂ V E e) :
    P.toMap x = S.inclusion (P.equiv x) := rfl

/-- A presentation covers the prescribed embedded subspace exactly. -/
theorem image_toMap : finiteRealizationImage F n P.toMap = S := by
  apply SetLike.ext
  intro f
  constructor
  · rintro ⟨x, rfl⟩
    exact (P.equiv x).property
  · intro hf
    obtain ⟨x, hx⟩ := P.equiv.surjective (⟨f, hf⟩ : S.Space)
    exact ⟨x, congrArg S.inclusion hx⟩

/-- A faithful form-valued tensor map with precisely the specified image
constructs presentation data; no occurrence is postulated. -/
def ofMap (hne : ∀ v ∉ E, e v ≠ 0)
    (T : FiniteTensorRealization.Map F n ρ E e he)
    (hT : FiniteTensorRealization.IsInjective F n ρ E e he T)
    (hS : finiteRealizationImage F n T = S) :
    FiniteTensorPresentation F n ρ E e he S :=
  hS ▸ (⟨hne, finiteRealizationImageEquiv F n T hT⟩ :
    FiniteTensorPresentation F n ρ E e he (finiteRealizationImage F n T))

/-- Restrict the supplied global equivalence along the actual local insertion. -/
def restrictedEquiv (v : FinitePlace F) :
    (tensorLocalRepresentation F n ρ E e he v).Equiv (S.localRepresentation v) :=
  Representation.Equiv.mk P.equiv.toLinearEquiv
    (fun g => P.equiv.isIntertwining' (localInclusion F n v g))

/-- The whole local restriction retains the entire complementary tensor space. -/
def localEquiv (v : FinitePlace F) :
    LocalEquivalence F n ρ E e S v :=
  (localTensorSeparation F n ρ E e he P.reference_nonzero v).symm.trans
    (P.restrictedEquiv v)

@[simp]
theorem inclusion_localEquiv (v : FinitePlace F)
    (z : V v ⊗[ℂ] LocalTensorTail (K := ℂ) F E v e) :
    S.inclusion (P.localEquiv v z) =
      FiniteTensorRealization.localMap F n ρ E e he P.reference_nonzero P.toMap v z := rfl

/-- The actual local form subspace obtained by fixing a complementary vector. -/
def slice (v : FinitePlace F) (y : LocalTensorTail (K := ℂ) F E v e) :
    LocalRealization F n v :=
  FiniteTensorRealization.sliceRealization F n ρ E e he P.reference_nonzero P.toMap v y

theorem slice_le (v : FinitePlace F) (y : LocalTensorTail (K := ℂ) F E v e) :
    P.slice v y ≤ S.toLocal F n v := by
  have h := FiniteTensorRealization.sliceRealization_le
    F n ρ E e he P.reference_nonzero P.toMap v y
  rwa [P.image_toMap] at h

/-- With a nonzero tail this actual slice is equivalent to the specified factor. -/
def sliceEquiv (v : FinitePlace F) (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) :
    (P.slice v y).Equivalence F n (ρ v) :=
  FiniteTensorRealization.sliceEquiv F n ρ E e he P.reference_nonzero
    P.toMap P.toMap_injective v y hy

/-- All slices together generate the whole locally restricted realization,
expressed by its universal containment property. -/
theorem toLocal_le_iff_slices_le (v : FinitePlace F) (L : LocalRealization F n v) :
    S.toLocal F n v ≤ L ↔ ∀ y, P.slice v y ≤ L := by
  constructor
  · intro h y
    exact (P.slice_le v y).trans h
  · intro h f hf
    obtain ⟨z, hz⟩ := (P.localEquiv v).surjective (⟨f, hf⟩ : S.Space)
    have hm : S.inclusion (P.localEquiv v z) ∈ L := by
      clear hz
      induction z using TensorProduct.inductionOn with
      | tmul x y =>
          apply h y
          exact ⟨x, rfl⟩
      | add x y hx hy =>
          change S.inclusion (P.localEquiv v (x + y)) ∈ L.toSubmodule
          simpa only [map_add] using L.toSubmodule.add_mem hx hy
    have hz' : S.inclusion (P.localEquiv v z) = f := congrArg S.inclusion hz
    rwa [hz'] at hm

/-- Slices from any two presentations using this same tensor model have the
same local class when their complementary vectors are nonzero. -/
theorem slice_isoClass_eq {S' : FiniteRealization F n}
    (Q : FiniteTensorPresentation F n ρ E e he S') (v : FinitePlace F)
    (y y' : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hy' : FiniteTensorRealization.TailNonzero F E e v y') :
    (P.slice v y).isoClass = (Q.slice v y').isoClass :=
  (LocalRealization.isoClass_eq_iff _ _).mpr
    ⟨(P.sliceEquiv v y hy).symm.trans (Q.sliceEquiv v y' hy')⟩

end FiniteTensorPresentation

/-- Existence of presentation data for these specified tensor inputs.
This predicate does not assert factorization for arbitrary automorphic spaces. -/
def HasFiniteTensorPresentation (S : FiniteRealization F n) : Prop :=
  Nonempty (FiniteTensorPresentation F n ρ E e he S)

/-- A presentation is equivalent to a faithful tensor map with exactly this image,
together with nonzero reference vectors outside the exceptional set. -/
theorem hasFiniteTensorPresentation_iff (S : FiniteRealization F n) :
    HasFiniteTensorPresentation F n ρ E e he S ↔
      (∀ v ∉ E, e v ≠ 0) ∧
        ∃ T : FiniteTensorRealization.Map F n ρ E e he,
          FiniteTensorRealization.IsInjective F n ρ E e he T ∧
            finiteRealizationImage F n T = S := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.reference_nonzero, P.toMap, P.toMap_injective, P.image_toMap⟩
  · rintro ⟨hne, T, hT, hS⟩
    exact ⟨FiniteTensorPresentation.ofMap hne T hT hS⟩

end Langlands.Automorphic
