import Langlands.Representation.Category.Subquotients
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.GroupTheory.Subgroup.Center

/-!
# Semisimple base case for constituent extraction

This proposition bundles scalar-center transfer and extraction of actual
subquotients from a semisimple smooth representation.
-/

namespace Langlands.CuspidalSupport

universe uR uG uV

/-- Scalar-center semisimplicity transfer and semisimple constituent extraction,
with independent coefficient, group, and representation-carrier universes. -/
def SemisimpleConstituentExtractionTheorem : Prop :=
  (∀ {R : Type uR} [Field R] {G : Type uG} [Group G]
      {V : Type uV} [AddCommGroup V] [Module R V]
      (ρ : Representation R G V) (H : Subgroup G),
    (∀ z : Subgroup.center G, ∃ c : R, ∀ v : V, ρ z v = c • v) →
    Representation.IsSemisimpleRepresentation (ρ.comp H.subtype) →
    Representation.IsSemisimpleRepresentation
      (ρ.comp (H ⊔ Subgroup.center G).subtype)) ∧
  (∀ {R : Type uR} [Field R] {G : Type uG} [Group G] [TopologicalSpace G]
      {A D : SmoothRep.{uR, uG, uV} R G},
    Representation.IsSemisimpleRepresentation A.representation →
    SmoothRep.IsSubquotient D A →
    SmoothRep.IsSubrepresentation D A ∧ SmoothRep.IsQuotient D A)

end Langlands.CuspidalSupport
