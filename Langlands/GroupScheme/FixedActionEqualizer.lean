import Langlands.GroupScheme.AutomorphicAction
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # The action equalizer and the all-test fixed condition -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry

namespace Langlands.GroupScheme.AutomorphicAction

variable {S : Scheme.{u}} {H G : GroupScheme S} (a : AutomorphicAction H G)

/-- The scheme on which action and projection agree, inside `H × G`. -/
abbrev actionEqualizer : Over S :=
  equalizer a.hom (snd H.X G.X)

/-- The inclusion of the action equalizer into `H × G`. -/
def actionEqualizerInclusion : a.actionEqualizer ⟶ H.X ⊗ G.X :=
  equalizer.ι _ _

/-- Separatedness of the target makes the action equalizer a closed subscheme. -/
instance actionEqualizerInclusion_isClosedImmersion [IsSeparated G.X.hom] :
    IsClosedImmersion a.actionEqualizerInclusion.left :=
  isClosedImmersion_equalizer_ι_left _ _

/-- A map into `H × G` factors through the action equalizer precisely when
action and projection agree on that map. -/
theorem factors_actionEqualizer_iff {T : Over S} (f : T ⟶ H.X ⊗ G.X) :
    (∃ q : T ⟶ a.actionEqualizer, q ≫ a.actionEqualizerInclusion = f) ↔
      f ≫ a.hom = f ≫ snd H.X G.X := by
  constructor
  · rintro ⟨q, rfl⟩
    exact congrArg (fun k => q ≫ k)
      (equalizer.condition a.hom (snd H.X G.X))
  · intro h
    exact ⟨equalizer.lift f h, equalizer.lift_ι _ _⟩

/-- All-refinement fixedness can be checked with the universal acting point on
`H × T`, in the product order used for factorization loci. -/
theorem mem_fixedSubgroup_iff_product {T : Over S} (g : T ⟶ G.X) :
    g ∈ a.fixedSubgroup.carrier T ↔
      (H.X ◁ g) ≫ a.hom = snd H.X T ≫ g := by
  rw [mem_fixedSubgroup]
  have hlift : lift (fst H.X T) (snd H.X T ≫ g) = H.X ◁ g := by
    apply hom_ext <;> simp
  constructor
  · intro hg
    simpa only [act, hlift] using hg (H.X ⊗ T) (snd H.X T) (fst H.X T)
  · intro hg T' b h
    have e := congrArg (fun k => lift h b ≫ k) hg
    simpa only [Category.assoc, lift_whiskerLeft_assoc, lift_snd_assoc, act] using e

/-- A point is fixed on every refinement exactly when its entire product with
the acting group factors through the action equalizer. -/
theorem mem_fixedSubgroup_iff_factors_actionEqualizer {T : Over S}
    (g : T ⟶ G.X) :
    g ∈ a.fixedSubgroup.carrier T ↔
      ∃ q : H.X ⊗ T ⟶ a.actionEqualizer, q ≫ a.actionEqualizerInclusion = H.X ◁ g := by
  rw [a.factors_actionEqualizer_iff, a.mem_fixedSubgroup_iff_product,
    whiskerLeft_snd]

end Langlands.GroupScheme.AutomorphicAction
