import Langlands.ClassField.Global.Cohomology
import Langlands.GroupTheory.CocycleClassEquiv

/-! # Relative idele-class extensions indexed by actual second cohomology classes -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField Topology
open scoped NumberField
open Langlands.Global.AdelicFunctoriality

universe u v

variable {K : Type u} {E : Type v} [Field K] [Field E] [NumberField E] [Algebra K E]

attribute [local instance] relativeIdeleClassAction relativeGaloisTopology

namespace RelativeIdeleCocycle

/-- Converse of `cohomologyClass_eq_of_cochain`: equal classes give a relating cochain. -/
theorem exists_cochain_of_cohomologyClass_eq {c d : RelativeIdeleCocycle K E}
    (hcd : c.cohomologyClass = d.cohomologyClass) :
    ∃ b : (E ≃ₐ[K] E) → IdeleClassGroup (𝓞 E) E, ∀ σ τ,
      c (σ, τ) * b (σ * τ) = b σ * (σ • b τ) * d (σ, τ) :=
  NormalizedTwoCocycle.exists_cochain_of_cohomologyClass_eq hcd

theorem cohomologyClass_eq_iff_exists_cochain (c d : RelativeIdeleCocycle K E) :
    c.cohomologyClass = d.cohomologyClass ↔
      ∃ b : (E ≃ₐ[K] E) → IdeleClassGroup (𝓞 E) E, ∀ σ τ,
        c (σ, τ) * b (σ * τ) = b σ * (σ • b τ) * d (σ, τ) :=
  NormalizedTwoCocycle.cohomologyClass_eq_iff_exists_cochain c d

variable {c d : RelativeIdeleCocycle K E} (hcd : c.cohomologyClass = d.cohomologyClass)

/-- The relating idele-class cochain chosen from equality of classes; it is not unique. -/
abbrev classCochain : (E ≃ₐ[K] E) → IdeleClassGroup (𝓞 E) E :=
  NormalizedTwoCocycle.classCochain hcd

theorem classCochain_spec (σ τ : E ≃ₐ[K] E) :
    c (σ, τ) * classCochain hcd (σ * τ) =
      classCochain hcd σ * (σ • classCochain hcd τ) * d (σ, τ) :=
  NormalizedTwoCocycle.classCochain_spec hcd σ τ

/-- The continuous equivalence `(a,σ) ↦ (a b(σ), σ)` for the chosen cochain `b`. -/
abbrev extensionEquiv : Extension c ≃ₜ* Extension d :=
  NormalizedTwoCocycle.continuousEquivOfCohomologyClassEq hcd

theorem extensionEquiv_left (t : Extension c) :
    (extensionEquiv hcd t).left = t.left * classCochain hcd t.right := rfl

theorem extensionEquiv_right (t : Extension c) :
    (extensionEquiv hcd t).right = t.right := rfl

theorem extensionEquiv_symm_apply (t : Extension d) :
    (extensionEquiv hcd).symm t = ⟨t.left / classCochain hcd t.right, t.right⟩ := rfl

/-- The equivalence fixes the idele-class subgroup. -/
theorem extensionEquiv_inclusion (a : IdeleClassGroup (𝓞 E) E) :
    extensionEquiv hcd (inclusion c a) = inclusion d a :=
  NormalizedTwoCocycle.continuousEquivOfCohomologyClassEq_inl hcd a

/-- The equivalence commutes with the projections to `E ≃ₐ[K] E`. -/
theorem projection_extensionEquiv (t : Extension c) :
    projection d (extensionEquiv hcd t) = projection c t := rfl

theorem extensionEquiv_symm_inclusion (a : IdeleClassGroup (𝓞 E) E) :
    (extensionEquiv hcd).symm (inclusion d a) = inclusion c a :=
  NormalizedTwoCocycle.continuousEquivOfCohomologyClassEq_symm_inl hcd a

theorem projection_extensionEquiv_symm (t : Extension d) :
    projection c ((extensionEquiv hcd).symm t) = projection d t := rfl

end RelativeIdeleCocycle

namespace ClassExtension

variable (x : relativeIdeleClassCohomology K E 2)

/-- The normalized representative of `x` chosen by `cohomologyClass_surjective`. -/
def representative : RelativeIdeleCocycle K E :=
  (RelativeIdeleCocycle.cohomologyClass_surjective x).choose

theorem cohomologyClass_representative : (representative x).cohomologyClass = x :=
  (RelativeIdeleCocycle.cohomologyClass_surjective x).choose_spec

end ClassExtension

/-- The extension of `E ≃ₐ[K] E` by `C_E` constructed from the chosen representative of `x`. -/
abbrev ClassExtension (x : relativeIdeleClassCohomology K E 2) : Type v :=
  RelativeIdeleCocycle.Extension (ClassExtension.representative x)

namespace ClassExtension

variable (x : relativeIdeleClassCohomology K E 2)

instance isTopologicalGroup : IsTopologicalGroup (ClassExtension x) :=
  RelativeIdeleCocycle.extensionIsTopologicalGroup (representative x)

/-- The coefficient inclusion of the actual idele class group. -/
abbrev inclusion : IdeleClassGroup (𝓞 E) E →* ClassExtension x :=
  RelativeIdeleCocycle.inclusion (representative x)

/-- The projection to the relative automorphism group. -/
abbrev projection : ClassExtension x →* (E ≃ₐ[K] E) :=
  RelativeIdeleCocycle.projection (representative x)

/-- The distinguished continuous set-theoretic section. -/
abbrev sectionMap : (E ≃ₐ[K] E) → ClassExtension x :=
  RelativeIdeleCocycle.sectionMap (representative x)

theorem inclusion_injective : Function.Injective (inclusion x) :=
  RelativeIdeleCocycle.inclusion_injective _

theorem projection_surjective : Function.Surjective (projection x) :=
  RelativeIdeleCocycle.projection_surjective _

theorem exact : (inclusion x).range = (projection x).ker :=
  RelativeIdeleCocycle.exact _

theorem continuous_inclusion : Continuous (inclusion x) :=
  RelativeIdeleCocycle.continuous_inclusion _

theorem continuous_projection : Continuous (projection x) :=
  RelativeIdeleCocycle.continuous_projection _

theorem continuous_sectionMap : Continuous (sectionMap x) :=
  RelativeIdeleCocycle.continuous_sectionMap _

/-- The inclusion as a continuous homomorphism. -/
def continuousInclusion : IdeleClassGroup (𝓞 E) E →ₜ* ClassExtension x where
  toMonoidHom := inclusion x
  continuous_toFun := continuous_inclusion x

/-- The projection as a continuous homomorphism. -/
def continuousProjection : ClassExtension x →ₜ* (E ≃ₐ[K] E) where
  toMonoidHom := projection x
  continuous_toFun := continuous_projection x

theorem isOpenEmbedding_inclusion : IsOpenEmbedding (inclusion x) :=
  RelativeIdeleCocycle.isOpenEmbedding_inclusion _

theorem isOpenQuotientMap_projection : IsOpenQuotientMap (projection x) :=
  RelativeIdeleCocycle.isOpenQuotientMap_projection _

/-- The factor set of the distinguished section is the chosen representative. -/
theorem factorSet (σ τ : E ≃ₐ[K] E) :
    sectionMap x σ * sectionMap x τ * (sectionMap x (σ * τ))⁻¹ =
      inclusion x (representative x (σ, τ)) :=
  RelativeIdeleCocycle.factorSet _ σ τ

theorem conjugation (t : ClassExtension x) (a : IdeleClassGroup (𝓞 E) E) :
    t * inclusion x a * t⁻¹ =
      inclusion x (ideleClassEquiv (projection x t).toRingEquiv a) :=
  RelativeIdeleCocycle.conjugation _ t a

theorem conjugation_mk (t : ClassExtension x) (a : IdeleGroup (𝓞 E) E) :
    t * inclusion x (QuotientGroup.mk a) * t⁻¹ =
      inclusion x (QuotientGroup.mk (ideleEquiv (projection x t).toRingEquiv a)) :=
  RelativeIdeleCocycle.conjugation_mk _ t a

section Representative

variable {x} (c : RelativeIdeleCocycle K E) (hc : c.cohomologyClass = x)

/-- The extension of a supplied representative of `x`, compared with the chosen one. -/
abbrev equivOfRepresentative : RelativeIdeleCocycle.Extension c ≃ₜ* ClassExtension x :=
  RelativeIdeleCocycle.extensionEquiv (hc.trans (cohomologyClass_representative x).symm)

theorem equivOfRepresentative_left (t : RelativeIdeleCocycle.Extension c) :
    (equivOfRepresentative c hc t).left =
      t.left * RelativeIdeleCocycle.classCochain
        (hc.trans (cohomologyClass_representative x).symm) t.right := rfl

theorem equivOfRepresentative_right (t : RelativeIdeleCocycle.Extension c) :
    (equivOfRepresentative c hc t).right = t.right := rfl

theorem equivOfRepresentative_inclusion (a : IdeleClassGroup (𝓞 E) E) :
    equivOfRepresentative c hc (RelativeIdeleCocycle.inclusion c a) = inclusion x a :=
  RelativeIdeleCocycle.extensionEquiv_inclusion _ a

theorem projection_equivOfRepresentative (t : RelativeIdeleCocycle.Extension c) :
    projection x (equivOfRepresentative c hc t) = RelativeIdeleCocycle.projection c t := rfl

theorem equivOfRepresentative_symm_inclusion (a : IdeleClassGroup (𝓞 E) E) :
    (equivOfRepresentative c hc).symm (inclusion x a) = RelativeIdeleCocycle.inclusion c a :=
  RelativeIdeleCocycle.extensionEquiv_symm_inclusion _ a

theorem projection_equivOfRepresentative_symm (t : ClassExtension x) :
    RelativeIdeleCocycle.projection c ((equivOfRepresentative c hc).symm t) = projection x t :=
  rfl

include hc in
/-- Some continuous equivalence over both ends exists; none is claimed unique or canonical. -/
theorem exists_continuousMulEquiv :
    ∃ e : RelativeIdeleCocycle.Extension c ≃ₜ* ClassExtension x,
      (∀ a, e (RelativeIdeleCocycle.inclusion c a) = inclusion x a) ∧
        ∀ t, projection x (e t) = RelativeIdeleCocycle.projection c t :=
  ⟨equivOfRepresentative c hc, equivOfRepresentative_inclusion c hc,
    projection_equivOfRepresentative c hc⟩

end Representative

section FiniteGalois

variable [NumberField K] [IsGalois K E]

/-- For finite Galois number fields the quotient `Gal(E/K)` has order `[E : K]`. -/
theorem nat_card_quotient : Nat.card (E ≃ₐ[K] E) = Module.finrank K E :=
  IsGalois.card_aut_eq_finrank K E

/-- The idele-class subgroup has index `[E : K]` in the class extension. -/
theorem index_range_inclusion : (inclusion x).range.index = Module.finrank K E := by
  rw [exact, Subgroup.index_ker, MonoidHom.range_eq_top.2 (projection_surjective x),
    Subgroup.card_top, nat_card_quotient]

end FiniteGalois

end ClassExtension
end Langlands.ClassField.Global
