/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.YonedaExtension.YonedaExtensionData
public import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! # A concrete class of a finite extension

Source: Stacks Project, Derived Categories, Tag 06XU and the Yoneda composition
following Tag 06XV. Cut at the cokernel of the first injection and recursively
compose short exact connecting classes, with the positive-projection signs.
(blueprint: def-coef-yoneda-recursive-class)
-/

@[expose] public section

universe u v w

namespace CategoryTheory.YonedaExtension

open Limits Abelian

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The canonical first short complex of an extension, ending in the actual cokernel.
Source: Stacks Project, Tag 06XU, cutting an extension at its first image.
(blueprint: def-coef-yoneda-recursive-class) -/
noncomputable def head {V U : A} {n : ℕ} (E : YonedaExtension A V U (n + 1)) :
    ShortComplex A :=
  ShortComplex.mk (E.sequence.map' 0 1) (cokernel.π (E.sequence.map' 0 1))
    (cokernel.condition _)

/-- The remaining sequence after replacing the first two terms by their cokernel.
Source: Stacks Project, Tag 06XU, first-image cut.
(blueprint: def-coef-yoneda-recursive-class) -/
noncomputable def tailSequence {V U : A} {n : ℕ}
    (E : YonedaExtension A V U (n + 2)) : ComposableArrows A (n + 2) :=
  E.sequence.δ₀.δ₀.precomp
    (cokernel.desc (E.sequence.map' 0 1) (E.sequence.map' 1 2)
      (E.exact.toIsComplex.zero 0))

/-- Exactness of the cokernel tail. Source: Stacks Project, Tag 06XU.
Proof: its first arrow is monic by exactness of the first two original arrows.
At the next term, precomposing with the epic cokernel projection identifies the
new pair with the old exact pair; all later pairs are unchanged.
(blueprint: def-coef-yoneda-recursive-class) -/
theorem tailSequence_exact {V U : A} {n : ℕ} (E : YonedaExtension A V U (n + 2)) :
    E.tailSequence.Exact := by
  apply ComposableArrows.exact_of_δ₀
  · let f := cokernel.desc (E.sequence.map' 0 1) (E.sequence.map' 1 2)
      (E.exact.toIsComplex.zero 0)
    have hz : f ≫ E.sequence.map' 2 3 = 0 := by
      apply (cancel_epi (cokernel.π (E.sequence.map' 0 1))).1
      simp [f, ← Category.assoc, E.exact.toIsComplex.zero 1]
    apply ComposableArrows.exact₂_mk _ hz
    let φ : E.sequence.sc E.exact.toIsComplex 1 ⟶
        ShortComplex.mk f (E.sequence.map' 2 3) hz :=
      { τ₁ := cokernel.π (E.sequence.map' 0 1)
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by simp [f]
        comm₂₃ := by simp }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 (E.exact.exact 1)
  · exact E.exact.δ₀.δ₀

/-- The first arrow of the tail is monic, by the cokernel characterization of
exactness. Source: Stacks Project, Tag 06XU.
(blueprint: def-coef-yoneda-recursive-class) -/
theorem tailSequence_first_mono {V U : A} {n : ℕ}
    (E : YonedaExtension A V U (n + 2)) : Mono (E.tailSequence.map' 0 1) := by
  exact (E.exact.exact 0).mono_cokernelDesc

/-- The last epimorphism is unchanged. Source: Stacks Project, Tag 06XU.
(blueprint: def-coef-yoneda-recursive-class) -/
theorem tailSequence_last_epi {V U : A} {n : ℕ}
    (E : YonedaExtension A V U (n + 2)) : Epi (E.tailSequence.map' (n + 1) (n + 2)) := by
  change Epi (E.sequence.map' (n + 2) (n + 3))
  exact E.last_epi

/-- The cokernel tail as an extension of one smaller degree.
Source: Stacks Project, Tag 06XU. (blueprint: def-coef-yoneda-recursive-class) -/
noncomputable def tail {V U : A} {n : ℕ} (E : YonedaExtension A V U (n + 2)) :
    YonedaExtension A (cokernel (E.sequence.map' 0 1)) U (n + 1) where
  sequence := E.tailSequence
  leftIso := Iso.refl _
  rightIso := E.rightIso
  exact := E.tailSequence_exact
  first_mono := E.tailSequence_first_mono
  last_epi := E.tailSequence_last_epi

/-- Every degree-one extension gives its endpoint-normalized short exact sequence.
Source: Stacks Project, Tag 06XV. (blueprint: def-coef-yoneda-recursive-class) -/
theorem shortExact {V U : A} (E : YonedaExtension A V U 1) :
    (E.sequence.sc E.exact.toIsComplex 0).ShortExact := by
  exact { exact := E.exact.exact 0
          mono_f := E.first_mono
          epi_g := E.last_epi }

end CategoryTheory.YonedaExtension

namespace CategoryTheory.YonedaExtension

open Limits Abelian

variable {A : Type u} [Category.{v} A] [Abelian A]

end CategoryTheory.YonedaExtension

namespace CategoryTheory.YonedaExtension

open Limits Abelian

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

end CategoryTheory.YonedaExtension
