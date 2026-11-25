/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.EssentialFiniteness
import WeilConjectures.FieldTheory.SmoothFractionFieldLocalizations
import WeilConjectures.FieldTheory.SeparableExtensionFractionFieldOfSmoothAlgebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Finitely generated separable extensions and smooth subalgebras

Source: Stacks Project, Algebra, Lemma 10.158.11, Tag 07BV
(blueprint: corollary-open-direct-image-over-field--2).
-/

@[expose] public section

universe u v

namespace FieldTheory

/--
For a finitely generated separable extension of fields `L/K`, the field `L` is
the filtered colimit of its finitely generated smooth `K`-subalgebras, with
the transition maps given by inclusions.  The directed family and its union
are rendered by `Directed (· ≤ ·) A` and `∀ x, ∃ i, x ∈ A i`, respectively.
Source: Stacks Project, Algebra, Lemma 10.158.11, Tag 07BV
(blueprint: corollary-open-direct-image-over-field--2). First choose a smooth `K`-subalgebra
`B` of `L` whose fraction field is `L`, using the separability hypothesis.
For each nonzero `f` in `B`, identify `B[1/f]` with the principal localization
of `B`; it remains smooth and is finitely generated over `K`. The family of
these localizations is nonempty and directed by multiplication of denominators.
Every element of `L` belongs to one of them, so their directed union is `L`.
-/
theorem fg_separable_extension_is_filtered_colimit_smooth
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hsep : Algebra.IsSeparableExtension K L) [Algebra.EssFiniteType K L] :
    ∃ (ι : Type v) (A : ι → Subalgebra K L),
      Nonempty ι ∧
        (∀ i, Algebra.Smooth K (A i)) ∧
        (∀ i, (A i).FG) ∧
        Directed (· ≤ ·) A ∧
        ∀ x : L, ∃ i, x ∈ A i := by
  obtain ⟨B, hBsm, hfrac⟩ := exists_smooth_subalgebra_fraction_field
    (IntermediateField.fg_top_iff.mpr inferInstance) hsep
  exact exists_smooth_fg_localization_family B hBsm hfrac

end FieldTheory
