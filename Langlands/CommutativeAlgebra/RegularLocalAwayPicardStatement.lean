import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # The Picard group of a regular local ring with one element inverted is trivial -/

universe u

namespace Langlands.CommutativeAlgebra

/-- For every regular local ring `R` and every `f : R`, the Picard group of `R_f` is trivial
(Stacks Project, Lemma 15.123.1, Tag 0AFZ). This definition states the assertion without
proving it. -/
def RegularLocalAwayPicardStatement : Prop :=
  ∀ (R : Type u) [CommRing R], IsRegularLocalRing R →
    ∀ f : R, Subsingleton (CommRing.Pic (Localization.Away f))

end Langlands.CommutativeAlgebra
