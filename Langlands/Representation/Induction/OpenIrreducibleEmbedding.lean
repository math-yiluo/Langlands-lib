import Langlands.Representation.Induction.OpenIrreducibleExtension
import Langlands.Representation.Category.UniverseLift

/-! # Open-subgroup embeddings with independent carrier universes -/

noncomputable section

namespace Langlands.Induction

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : OpenSubgroup G)

/-- An ambient irreducible together with an embedding from the original,
independent-universe subgroup carrier. -/
structure OpenIrreducibleEmbedding (A : SmoothRep.{0, uG, uV} ℂ H) where
  obj : SmoothRep.{0, uG, max uG uV} ℂ G
  irreducible : obj.IsIrreducible
  embedding : A.representation.IntertwiningMap
    (obj.representation.comp H.toSubgroup.subtype)
  injective : Function.Injective embedding

/-- Lift only the source carrier to apply the published ambient extension,
then compose its embedding with the actual carrier-lift equivalence. -/
def openIrreducibleEmbedding (A : SmoothRep.{0, uG, uV} ℂ H)
    (hA : A.IsIrreducible) : OpenIrreducibleEmbedding H A := by
  let A' : SmoothRep.{0, uG, max uG uV} ℂ H := SmoothRep.universeLift.{uG} A
  let E := openIrreducibleExtension H.toSubgroup H.isOpen A'
    ((SmoothRep.isIrreducible_universeLift_iff A).mpr hA)
  exact
    { obj := E.obj
      irreducible := E.irreducible
      embedding := (SmoothRep.hom E.embedding).comp
        (SmoothRep.universeLiftEquiv.{uG} A).toIntertwiningMap
      injective := E.injective.comp (SmoothRep.universeLiftEquiv.{uG} A).injective }

/-- Every irreducible smooth open-subgroup action embeds in an ambient
irreducible, with no relation between the group and source universes. -/
theorem exists_irreducible_ambient_of_open_subgroup
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ H V) [σ.IsIrreducible] (hσ : IsSmooth σ) :
    ∃ C : SmoothRep.{0, uG, max uG uV} ℂ G, C.IsIrreducible ∧
      ∃ f : σ.IntertwiningMap (C.representation.comp H.toSubgroup.subtype),
        Function.Injective f := by
  let E := openIrreducibleEmbedding H (SmoothRep.of σ hσ) inferInstance
  exact ⟨E.obj, E.irreducible, E.embedding, E.injective⟩

end Langlands.Induction
