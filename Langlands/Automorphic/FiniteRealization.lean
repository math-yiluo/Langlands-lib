import Langlands.Automorphic.LocalAction
import Langlands.Representation.Category.Basic
import Langlands.Representation.Smooth.Transfer.SubquotientProof

/-! # Finite adelic realizations inside actual automorphic forms -/

noncomputable section
universe uF uV

namespace Langlands.Automorphic

open Langlands.Global NumberField ContinuousRationalFunctions

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

local instance finiteRealizationRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance finiteRealizationContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance finiteRealizationSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance finiteRealizationFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

/-- An actual finite adelic invariant subspace of automorphic forms.
This records its position in the form space, before passage to isomorphism classes. -/
abbrev FiniteRealization := Subrepresentation (automorphicFiniteRightAction F n)

namespace FiniteRealization

variable {F n} (S : FiniteRealization F n)

/-- The actual vectors of the realized subspace. -/
abbrev Space := S.toSubmodule

local instance finiteRealizationSpaceAddCommGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _

/-- A compact type for the finite adelic action on the realized space. -/
abbrev Action := Representation ℂ (FiniteAdelicGL F n) S.Space

/-- Restriction of actual positive right translation to the invariant subspace. -/
def representation : S.Action := S.toRepresentation

/-- The faithful intertwining inclusion of the realized space into automorphic forms. -/
def inclusion : S.representation.IntertwiningMap (automorphicFiniteRightAction F n) where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := by ext; rfl

theorem inclusion_injective : Function.Injective S.inclusion := Subtype.val_injective

/-- Smoothness is inherited from the actual form action, rather than supplied as data. -/
theorem isSmooth : Langlands.IsSmooth S.representation :=
  Langlands.isSmooth_of_injective S.inclusion S.inclusion_injective
    (automorphicFiniteRightAction_isSmooth F n)

/-- The realized vectors retain their faithful continuous adelic function map. -/
def toContinuous : S.Space →ₗ[ℂ] ContinuousRationalFunctions F n :=
  (automorphicToContinuous F n).comp S.inclusion.toLinearMap

theorem toContinuous_injective : Function.Injective S.toContinuous :=
  (automorphicToContinuous_injective F n).comp S.inclusion_injective

@[simp]
theorem evaluate_representation (d : FiniteAdelicGL F n) (f : S.Space)
    (x : AdelicGL F n) :
    evaluate F n (S.toContinuous (S.representation d f)) x =
      evaluate F n (S.toContinuous f) (x * AdelicGL.ofFinite F n d) := rfl

/-- The local restriction keeps the entire realized carrier. -/
def localRepresentation (v : Langlands.Global.FinitePlace F) :
    Representation ℂ (FiniteLocalGL F n v) S.Space :=
  S.representation.comp (FiniteAdelicGL.localInclusion F n v).toMonoidHom

theorem localRepresentation_isSmooth (v : Langlands.Global.FinitePlace F) :
    Langlands.IsSmooth (S.localRepresentation v) :=
  Langlands.isSmooth_comp (FiniteAdelicGL.localInclusion F n v).toMonoidHom
    (FiniteAdelicGL.localInclusion F n v).continuous S.isSmooth

@[simp]
theorem evaluate_localRepresentation (v : Langlands.Global.FinitePlace F)
    (g : FiniteLocalGL F n v) (f : S.Space) (x : AdelicGL F n) :
    evaluate F n (S.toContinuous (S.localRepresentation v g f)) x =
      evaluate F n (S.toContinuous f)
        (x * AdelicGL.ofFinite F n (FiniteAdelicGL.localInclusion F n v g)) := rfl

/-- The realized space as an object of the existing smooth representation category. -/
def smoothRepresentation : Langlands.SmoothRep ℂ (FiniteAdelicGL F n) :=
  Langlands.SmoothRep.of S.representation S.isSmooth

/-- Forget the embedding into forms and retain only its smooth representation class. -/
def isoClass : Langlands.SmoothRep.IsoClass.{0, uF, uF} ℂ (FiniteAdelicGL F n) :=
  Langlands.SmoothRep.isoClass S.smoothRepresentation

/-- Class equality means equivariant linear equivalence, not equality of form subspaces. -/
theorem isoClass_eq_iff (T : FiniteRealization F n) :
    S.isoClass = T.isoClass ↔ Nonempty (S.representation.Equiv T.representation) := by
  rw [isoClass, isoClass, Langlands.SmoothRep.isoClass_eq_iff]
  exact ⟨fun ⟨e⟩ => ⟨Langlands.SmoothRep.equivOfIso e⟩,
    fun ⟨e⟩ => ⟨Langlands.SmoothRep.mkIso e⟩⟩

/-- Irreducibility is a separate property of the realized finite action. -/
abbrev IsIrreducible : Prop := S.representation.IsIrreducible

/-- Prescribed central character is imposed on the actual embedded forms. -/
def HasCentralCharacter (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) : Prop :=
  S ≤ centralCharacterAutomorphicSubrepresentation F n χ

theorem centralCharacter_evaluate (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hS : S.HasCentralCharacter χ) (f : S.Space)
    (z : IdeleGroup (𝓞 F) F) (x : AdelicGL F n) :
    evaluate F n (S.toContinuous f) (AdelicGL.scalar F n z * x) =
      (centralIdeleCharacter F χ z : ℂ) * evaluate F n (S.toContinuous f) x :=
  hS f.property z x

variable [CompactSpace (AdeleQuotient F)]

/-- Cuspidality is imposed through the actual normalized constant terms. -/
def IsCuspidal : Prop := S ≤ cuspidalAutomorphicSubrepresentation F n

theorem constantTerm_eq_zero (hS : S.IsCuspidal)
    {a b : ℕ} (h : a + b = n) (ha : 0 < a) (hb : 0 < b)
    (f : S.Space) (g : AdelicGL F n) :
    constantTerm F n h (S.toContinuous f) g = 0 :=
  hS f.property a b h ha hb g

end FiniteRealization

/-- Construct a finite realization by taking the span of the actual finite orbit. -/
def generatedFiniteRealization (f : AutomorphicForms F n) : FiniteRealization F n :=
  Langlands.FiniteVectors.orbitSubrepresentation (automorphicFiniteRightAction F n) f

theorem mem_generatedFiniteRealization (f : AutomorphicForms F n) :
    f ∈ generatedFiniteRealization F n f :=
  Langlands.FiniteVectors.self_mem_orbitSpan (automorphicFiniteRightAction F n) f

/-- This is the smallest finite invariant form space containing the given form. -/
theorem generatedFiniteRealization_le_iff (f : AutomorphicForms F n)
    (S : FiniteRealization F n) :
    generatedFiniteRealization F n f ≤ S ↔ f ∈ S :=
  ⟨fun h => h (mem_generatedFiniteRealization F n f),
    fun h => Langlands.FiniteVectors.orbitSpan_le (automorphicFiniteRightAction F n) f S h⟩

theorem generatedFiniteRealization_ne_bot {f : AutomorphicForms F n} (hf : f ≠ 0) :
    generatedFiniteRealization F n f ≠ ⊥ := by
  intro h
  have hm := mem_generatedFiniteRealization F n f
  rw [h] at hm
  exact hf hm

theorem generatedFiniteRealization_hasCentralCharacter_iff
    (f : AutomorphicForms F n) (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) :
    (generatedFiniteRealization F n f).HasCentralCharacter χ ↔
      f ∈ centralCharacterAutomorphicSubrepresentation F n χ :=
  generatedFiniteRealization_le_iff F n f _

theorem generatedFiniteRealization_isCuspidal_iff [CompactSpace (AdeleQuotient F)]
    (f : AutomorphicForms F n) :
    (generatedFiniteRealization F n f).IsCuspidal ↔
      Langlands.Automorphic.IsCuspidal F n (automorphicToContinuous F n f) :=
  generatedFiniteRealization_le_iff F n f _

section Image

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {ρ : Representation ℂ (FiniteAdelicGL F n) V}

/-- The type of equivariant maps from a representation into actual automorphic forms. -/
abbrev FiniteRealizationMap (ρ : Representation ℂ (FiniteAdelicGL F n) V) :=
  ρ.IntertwiningMap (automorphicFiniteRightAction F n)

/-- Faithfulness of the form-valued map, with its large ambient instances hidden. -/
abbrev FiniteRealizationMap.IsInjective (T : FiniteRealizationMap F n ρ) : Prop :=
  Function.Injective T

/-- Equivalence of a model representation with the actual realized action. -/
abbrev FiniteRealization.Equivalence (S : FiniteRealization F n)
    (ρ : Representation ℂ (FiniteAdelicGL F n) V) :=
  ρ.Equiv S.representation

/-- Construct the actual invariant image of an equivariant form-valued map. -/
def finiteRealizationImage (T : FiniteRealizationMap F n ρ) :
    FiniteRealization F n := T.range

/-- An injective intertwiner is genuinely equivalent to its realized image. -/
def finiteRealizationImageEquiv
    (T : FiniteRealizationMap F n ρ)
    (hT : FiniteRealizationMap.IsInjective F n T) :
    (finiteRealizationImage F n T).Equivalence F n ρ :=
  Representation.Equiv.mk (LinearEquiv.ofInjective T.toLinearMap hT) (by
    intro g
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _ T g v)

@[simp]
theorem inclusion_finiteRealizationImageEquiv
    (T : FiniteRealizationMap F n ρ)
    (hT : FiniteRealizationMap.IsInjective F n T) (v : V) :
    (finiteRealizationImage F n T).inclusion (finiteRealizationImageEquiv F n T hT v) =
      T v := rfl

/-- Existence of a faithful finite adelic realization in the actual form space.
This predicate is not an existence theorem or a tensor-factorization assumption. -/
def HasFiniteRealization (ρ : Representation ℂ (FiniteAdelicGL F n) V) : Prop :=
  ∃ T : FiniteRealizationMap F n ρ, FiniteRealizationMap.IsInjective F n T

/-- A faithful form-valued map and equivalence to an actual invariant form space
are two equivalent descriptions of finite realization. -/
theorem hasFiniteRealization_iff (ρ : Representation ℂ (FiniteAdelicGL F n) V) :
    HasFiniteRealization F n ρ ↔
      ∃ S : FiniteRealization F n, Nonempty (S.Equivalence F n ρ) := by
  constructor
  · rintro ⟨T, hT⟩
    exact ⟨finiteRealizationImage F n T, ⟨finiteRealizationImageEquiv F n T hT⟩⟩
  · rintro ⟨S, ⟨e⟩⟩
    exact ⟨S.inclusion.comp e.toIntertwiningMap, S.inclusion_injective.comp e.injective⟩

end Image
end Langlands.Automorphic
