import Langlands.Representation.Category.Basic
import Langlands.Representation.Jacquet.FixedVectorsGenerationProof
import Langlands.Representation.Smooth.CompactCompletionAction
import Langlands.Representation.Smooth.CompactCompletionMaps

/-! # The normalizer action on a fixed compact-open completion -/

set_option autoImplicit false

noncomputable section

namespace Langlands.CompactCompletion

open CategoryTheory HarishChandraSchwartz

universe uG uH uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type uH} [Group H]
  (N : Subgroup G) (φ : H →* G) (hφ : ∀ h, φ h ∈ Subgroup.normalizer N)

section Representation

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

/-- Restrict completion translations along `φ` to the families fixed by `N`. -/
def fixedRepresentation : Representation ℂ H (completionFixed ρ hρ N) :=
  Representation.subrepresentation ((representation ρ hρ).comp φ) (completionFixed ρ hρ N) (by
    intro h x hx
    change representation ρ hρ (φ h) x ∈ completionFixed ρ hρ N
    rw [completionFixed_eq_fixedVectors] at hx ⊢
    exact Jacquet.apply_mem_fixedVectors_of_mem_normalizer (representation ρ hρ) N
      (hφ h) hx)

@[simp]
theorem fixedRepresentation_apply (h : H) (x : completionFixed ρ hρ N) :
    (fixedRepresentation N φ hφ ρ hρ h x).val = representation ρ hρ (φ h) x.val :=
  rfl

end Representation

private def fixedIntertwiner {V W : SmoothRep.{0, uG, uV} ℂ G} (f : V ⟶ W) :
    Representation.IntertwiningMap
      (fixedRepresentation N φ hφ V.representation V.isSmooth)
      (fixedRepresentation N φ hφ W.representation W.isSmooth) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (mapFixed V.isSmooth W.isSmooth N (SmoothRep.hom f)) (by
      intro h x
      apply Subtype.ext
      apply Subtype.ext
      exact map_translate V.isSmooth W.isSmooth (SmoothRep.hom f) (φ h) x.val)

/-- Completion followed by `N`-invariants, with the `H` action given by `φ`. -/
def fixedFunctor : SmoothRep.{0, uG, uV} ℂ G ⥤ Rep.{max uG uV} ℂ H where
  obj V := Rep.of (X := completionFixed V.representation V.isSmooth N)
    (fixedRepresentation N φ hφ V.representation V.isSmooth)
  map {V W} f := Rep.ofHom (X := completionFixed V.representation V.isSmooth N)
    (Y := completionFixed W.representation W.isSmooth N) (fixedIntertwiner N φ hφ f)
  map_id V := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact mapFixed_id V.isSmooth N
  map_comp {V W X} f g := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact mapFixed_comp V.isSmooth W.isSmooth X.isSmooth N (SmoothRep.hom f) (SmoothRep.hom g)

@[simp]
theorem fixedFunctor_map_apply {V W : SmoothRep.{0, uG, uV} ℂ G} (f : V ⟶ W)
    (x : completionFixed V.representation V.isSmooth N) (K : CompactOpenSubgroup G) :
    (((fixedFunctor N φ hφ).map f).hom x).val.val K =
      SmoothRep.hom f (x.val.val K) :=
  rfl

end Langlands.CompactCompletion
