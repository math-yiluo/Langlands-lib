import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Induction on smooth closed subgroups of an affine group over a field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- The closed support of a closed-subgroup inclusion. -/
def closedSubgroupSupport {H G : GroupScheme (Spec (CommRingCat.of k))}
    (j : H ⟶ G) (hj : IsClosedSubgroup j) : TopologicalSpace.Closeds G.X.left := by
  let : IsClosedImmersion j.hom.hom.left := hj
  exact ⟨Set.range j.hom.hom.left, j.hom.hom.left.isClosedEmbedding.isClosed_range⟩

/-- Smooth affine schemes over a field have Noetherian underlying spaces. -/
theorem noetherianSpace_of_smooth_affine (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] : NoetherianSpace G.X.left := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsNoetherian G.X.left :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian G.X.hom }
  infer_instance

/-- A proper smooth closed subgroup has strictly smaller support inside any
closed ambient group. -/
theorem closedSubgroupSupport_comp_lt {K H G : GroupScheme (Spec (CommRingCat.of k))}
    (i : K ⟶ H) (hi : IsClosedSubgroup i) (j : H ⟶ G) (hj : IsClosedSubgroup j)
    [Smooth H.X.hom] (hproper : ¬ IsIso i) :
    closedSubgroupSupport (i ≫ j) (hi.comp hj) < closedSubgroupSupport j hj := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsClosedImmersion j.hom.hom.left := hj
  refine lt_iff_le_not_ge.mpr ⟨?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨i.hom.hom.left x, rfl⟩
  · intro hle
    have hsurj : Function.Surjective i.hom.hom.left := by
      intro y
      obtain ⟨x, hx⟩ := hle (show j.hom.hom.left y ∈ closedSubgroupSupport j hj from
        ⟨y, rfl⟩)
      exact ⟨x, j.hom.hom.left.isClosedEmbedding.injective hx⟩
    let : Surjective i.hom.hom.left := ⟨hsurj⟩
    let : AlgebraicGeometry.IsReduced H.X.left :=
      Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
        k H.X.left H.X.hom
    let : IsIso i.hom.hom.left := isIso_of_isClosedImmersion_of_surjective _
    have : IsIso ((Over.forget _).map i.hom.hom) := by
      change IsIso i.hom.hom.left
      infer_instance
    have : IsIso i.hom.hom := isIso_of_reflects_iso i.hom.hom (Over.forget _)
    have : IsIso ((Mon.forget _).map i.hom) := by
      change IsIso i.hom.hom
      infer_instance
    have : IsIso i.hom := isIso_of_reflects_iso i.hom (Mon.forget _)
    have : IsIso ((Grp.forget₂Mon _).map i) := by
      change IsIso i.hom
      infer_instance
    exact hproper (isIso_of_reflects_iso i (Grp.forget₂Mon _))

/-- A property of smooth affine groups follows by induction if it follows for
any such group from the property for its proper smooth affine closed subgroups. -/
theorem smoothAffineGroup_closedSubgroup_induction
    (P : GroupScheme (Spec (CommRingCat.of k)) → Prop)
    (step : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom],
      (∀ (K : GroupScheme (Spec (CommRingCat.of k)))
        [Smooth K.X.hom] [IsAffineHom K.X.hom] (i : K ⟶ H),
        IsClosedSubgroup i → ¬ IsIso i → P K) → P H)
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] : P G := by
  let : NoetherianSpace G.X.left := noetherianSpace_of_smooth_affine G
  have h : ∀ Z : Closeds G.X.left,
      ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
        [Smooth H.X.hom] [IsAffineHom H.X.hom] (j : H ⟶ G) (hj : IsClosedSubgroup j),
        closedSubgroupSupport j hj = Z → P H := by
    intro Z
    apply wellFounded_lt.induction Z
    intro Z ih H _ _ j hj heq
    apply step H
    intro K _ _ i hi hproper
    apply ih (closedSubgroupSupport (i ≫ j) (hi.comp hj)) ?_
      K (i ≫ j) (hi.comp hj) rfl
    rw [← heq]
    exact closedSubgroupSupport_comp_lt i hi j hj hproper
  exact h _ G (𝟙 G) (IsClosedSubgroup.of_iso (Iso.refl G)) rfl

end Langlands.GroupScheme
