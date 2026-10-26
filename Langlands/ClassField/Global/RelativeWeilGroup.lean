import Langlands.ClassField.Global.ClassExtensionRestriction
import Langlands.ClassField.Global.LocalClassExtension

/-! # Relative global Weil groups at a supplied class family -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField Topology
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local

universe u

/-- The class-indexed extension at `c F E`; its Weil-group interpretation requires
that this class be the arithmetic fundamental class. No family is selected here. -/
abbrev RelativeWeilGroup (c : FundamentalClass.ClassFamily.{u}) (F E : Type u)
    [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] :
    Type u :=
  ClassExtension (K := F) (c F E)

namespace RelativeWeilGroup

variable (c : FundamentalClass.ClassFamily.{u}) (F E : Type u)
  [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]

attribute [local instance] relativeIdeleClassAction relativeGaloisTopology
  completionGaloisTopology

/-- The existing idele-class inclusion. -/
abbrev inclusion : IdeleClassGroup (𝓞 E) E →* RelativeWeilGroup c F E :=
  ClassExtension.inclusion (c F E)

/-- The existing projection to the arithmetic automorphism group. -/
abbrev projection : RelativeWeilGroup c F E →* (E ≃ₐ[F] E) :=
  ClassExtension.projection (c F E)

/-- The existing inclusion, with its proved continuity. -/
abbrev continuousInclusion : IdeleClassGroup (𝓞 E) E →ₜ* RelativeWeilGroup c F E :=
  ClassExtension.continuousInclusion (c F E)

/-- The existing projection, with its proved continuity and discrete target. -/
abbrev continuousProjection : RelativeWeilGroup c F E →ₜ* (E ≃ₐ[F] E) :=
  ClassExtension.continuousProjection (c F E)

theorem inclusion_injective : Function.Injective (inclusion c F E) :=
  ClassExtension.inclusion_injective (c F E)

theorem projection_surjective : Function.Surjective (projection c F E) :=
  ClassExtension.projection_surjective (c F E)

theorem exact : (inclusion c F E).range = (projection c F E).ker :=
  ClassExtension.exact (c F E)

theorem isOpenEmbedding_inclusion : IsOpenEmbedding (inclusion c F E) :=
  ClassExtension.isOpenEmbedding_inclusion (c F E)

theorem isOpenQuotientMap_projection : IsOpenQuotientMap (projection c F E) :=
  ClassExtension.isOpenQuotientMap_projection (c F E)

theorem conjugation (t : RelativeWeilGroup c F E) (a : IdeleClassGroup (𝓞 E) E) :
    t * inclusion c F E a * t⁻¹ =
      inclusion c F E (ideleClassEquiv (projection c F E t).toRingEquiv a) :=
  ClassExtension.conjugation (c F E) t a

theorem index_range_inclusion : (inclusion c F E).range.index = Module.finrank F E :=
  ClassExtension.index_range_inclusion (c F E)

section Restriction

variable (F' : Type u) [Field F'] [NumberField F']
  [Algebra F F'] [Algebra F' E] [IsScalarTower F F' E]
  (h : FundamentalClass.Restriction c)

include h in
/-- The supplied restriction predicate identifies the two actual cohomology classes. -/
theorem restrictedClass_eq :
    haveI : IsGalois F' E := IsGalois.tower_top_of_isGalois F F' E
    ClassExtension.restrictedClass F' (c F E) = c F' E :=
  (FundamentalClass.restriction_iff_classes c).mp h F F' E

/-- Compare the family's extension with the extension of the restricted class
using representative independence, over both end groups. -/
def restrictionEquiv :
    haveI : IsGalois F' E := IsGalois.tower_top_of_isGalois F F' E
    RelativeWeilGroup c F' E ≃ₜ*
      ClassExtension (ClassExtension.restrictedClass F' (c F E)) := by
  haveI : IsGalois F' E := IsGalois.tower_top_of_isGalois F F' E
  exact ClassExtension.equivOfRepresentative (ClassExtension.representative (c F' E))
    ((ClassExtension.cohomologyClass_representative (c F' E)).trans
      (restrictedClass_eq c F E F' h).symm)

@[simp]
theorem restrictionEquiv_inclusion (a : IdeleClassGroup (𝓞 E) E) :
    haveI : IsGalois F' E := IsGalois.tower_top_of_isGalois F F' E
    restrictionEquiv c F E F' h (inclusion c F' E a) =
      ClassExtension.inclusion (ClassExtension.restrictedClass F' (c F E)) a := by
  have : IsGalois F' E := IsGalois.tower_top_of_isGalois F F' E
  exact ClassExtension.equivOfRepresentative_inclusion
    (ClassExtension.representative (c F' E))
    ((ClassExtension.cohomologyClass_representative (c F' E)).trans
      (restrictedClass_eq c F E F' h).symm) a

@[simp]
theorem projection_restrictionEquiv :
    haveI : IsGalois F' E := IsGalois.tower_top_of_isGalois F F' E
    ∀ t : RelativeWeilGroup c F' E,
      ClassExtension.projection (ClassExtension.restrictedClass F' (c F E))
          (restrictionEquiv c F E F' h t) =
        projection c F' E t := by
  have : IsGalois F' E := IsGalois.tower_top_of_isGalois F F' E
  intro t
  exact ClassExtension.projection_equivOfRepresentative
    (ClassExtension.representative (c F' E))
    ((ClassExtension.cohomologyClass_representative (c F' E)).trans
      (restrictedClass_eq c F E F' h).symm) t

/-- The intermediate-field inclusion, composed from the two published constructions. -/
def restrictionInclusion :
    haveI : IsGalois F' E := IsGalois.tower_top_of_isGalois F F' E
    RelativeWeilGroup c F' E →ₜ* RelativeWeilGroup c F E := by
  haveI : IsGalois F' E := IsGalois.tower_top_of_isGalois F F' E
  exact {
    toMonoidHom := (ClassExtension.restrictionInclusion F' (c F E)).toMonoidHom.comp
      (restrictionEquiv c F E F' h).toMulEquiv.toMonoidHom
    continuous_toFun := (ClassExtension.restrictionInclusion F' (c F E)).continuous.comp
      (restrictionEquiv c F E F' h).continuous }

@[simp]
theorem restrictionInclusion_inclusion (a : IdeleClassGroup (𝓞 E) E) :
    haveI : IsGalois F' E := IsGalois.tower_top_of_isGalois F F' E
    restrictionInclusion c F E F' h (inclusion c F' E a) = inclusion c F E a := by
  have : IsGalois F' E := IsGalois.tower_top_of_isGalois F F' E
  change ClassExtension.restrictionInclusion F' (c F E)
    (restrictionEquiv c F E F' h (inclusion c F' E a)) = _
  rw [restrictionEquiv_inclusion, ClassExtension.restrictionInclusion_inclusion]

@[simp]
theorem projection_restrictionInclusion :
    haveI : IsGalois F' E := IsGalois.tower_top_of_isGalois F F' E
    ∀ t : RelativeWeilGroup c F' E,
      projection c F E (restrictionInclusion c F E F' h t) =
        (projection c F' E t).restrictScalars F := by
  have : IsGalois F' E := IsGalois.tower_top_of_isGalois F F' E
  intro t
  change ClassExtension.projection (c F E)
    (ClassExtension.restrictionInclusion F' (c F E) (restrictionEquiv c F E F' h t)) = _
  rw [ClassExtension.projection_restrictionInclusion, projection_restrictionEquiv]

theorem restrictionInclusion_injective :
    Function.Injective (restrictionInclusion c F E F' h) :=
  (ClassExtension.restrictionInclusion_injective F' (c F E)).comp
    (restrictionEquiv c F E F' h).injective

theorem isOpenEmbedding_restrictionInclusion :
    IsOpenEmbedding (restrictionInclusion c F E F' h) :=
  (ClassExtension.isOpenEmbedding_restrictionInclusion F' (c F E)).comp
    (restrictionEquiv c F E F' h).toHomeomorph.isOpenEmbedding

/-- The intermediate-field image is exactly the inverse image of its automorphism subgroup. -/
theorem range_restrictionInclusion :
    (restrictionInclusion c F E F' h).toMonoidHom.range =
      ((AlgEquiv.restrictScalarsHom F : (E ≃ₐ[F'] E) →* (E ≃ₐ[F] E)).range).comap
        (projection c F E) := by
  rw [show (restrictionInclusion c F E F' h).toMonoidHom.range =
      (ClassExtension.restrictionInclusion F' (c F E)).toMonoidHom.range from ?_]
  · exact ClassExtension.range_restrictionInclusion F' (c F E)
  · ext t
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨restrictionEquiv c F E F' h s, rfl⟩
    · rintro ⟨s, rfl⟩
      refine ⟨(restrictionEquiv c F E F' h).symm s, ?_⟩
      change ClassExtension.restrictionInclusion F' (c F E)
        (restrictionEquiv c F E F' h ((restrictionEquiv c F E F' h).symm s)) = _
      rw [(restrictionEquiv c F E F' h).apply_symm_apply]
      rfl

end Restriction

section FinitePlace

variable {F E} (v : Langlands.Global.FinitePlace F) (w : Langlands.Global.FinitePlace E)
  [w.asIdeal.LiesOver v.asIdeal]
  [IsGalois (padicField v).Carrier (w.adicCompletion E)]

local instance globalNormal : Normal F E := IsGalois.to_normal

-- `FinitePlace` is the height-one spectrum and the `padicField` carrier is the
-- actual adic completion, so this is the published completed-field finiteness.
local instance completionFiniteDimensional :
    FiniteDimensional (padicField v).Carrier (w.adicCompletion E) :=
  FiniteExtension.local_finite
    (show IsDedekindDomain.HeightOneSpectrum (𝓞 F) from v)
    (show IsDedekindDomain.HeightOneSpectrum (𝓞 E) from w)

variable (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
  (h : FundamentalClass.LocalCompatibility I c)
  (a : CompletionH2 v w)
  (ha : IsFundamentalClass (padicField v).Carrier (w.adicCompletion E)
    ((I (residuePrime v)).relative (padicField v) (w.adicCompletion E)) a)

include h ha in
/-- The local fundamental class and the family's local compatibility supply exactly
the class equality required by the published local-to-global construction. -/
theorem localGlobalCompatible :
    CompletionClassExtension.GlobalCompatible v w a (c F E) := by
  -- This also makes explicit the definitional identification of the two local bases.
  have : IsGalois (v.adicCompletion F) (w.adicCompletion E) :=
    (inferInstance : IsGalois (padicField v).Carrier (w.adicCompletion E))
  change localIdeleClassMap v w 2 a = decompositionRestriction v w 2 (c F E)
  exact (FundamentalClass.localCompatibility_iff_classes I c).mp h F E
    (show IsDedekindDomain.HeightOneSpectrum (𝓞 F) from v)
    (show IsDedekindDomain.HeightOneSpectrum (𝓞 E) from w) a ha

/-- The existing continuous homomorphism, using the derived class compatibility.
Its source is a completed-local class extension; no actual local Weil-group
identification is asserted here. -/
def localToRelative : CompletionClassExtension v w a →ₜ* RelativeWeilGroup c F E :=
  CompletionClassExtension.toGlobal v w a (c F E) (localGlobalCompatible c v w I h a ha)

theorem localToRelative_left (t : CompletionClassExtension v w a) :
    (localToRelative c v w I h a ha t).left =
      IdeleClassGroup.ofAdicCompletion (𝓞 E) E w t.left *
        CompletionClassExtension.globalCochain v w a (c F E)
          (localGlobalCompatible c v w I h a ha) t.right :=
  CompletionClassExtension.toGlobal_left v w a (c F E) _ t

theorem localToRelative_right (t : CompletionClassExtension v w a) :
    (localToRelative c v w I h a ha t).right = FundamentalClass.decompositionHom v w t.right :=
  CompletionClassExtension.toGlobal_right v w a (c F E) _ t

theorem localToRelative_inclusion (x : (w.adicCompletion E)ˣ) :
    localToRelative c v w I h a ha (CompletionClassExtension.inclusion v w a x) =
      inclusion c F E (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w x) :=
  CompletionClassExtension.toGlobal_inclusion v w a (c F E) _ x

theorem projection_localToRelative (t : CompletionClassExtension v w a) :
    projection c F E (localToRelative c v w I h a ha t) =
      FundamentalClass.decompositionHom v w (CompletionClassExtension.projection v w a t) :=
  CompletionClassExtension.projection_toGlobal v w a (c F E) _ t

end FinitePlace

end RelativeWeilGroup
end Langlands.ClassField.Global
