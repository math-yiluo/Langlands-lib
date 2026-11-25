/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective

/-!
# Projective morphisms are stable under base change

## References

* Stacks Project, Morphisms of Schemes, Lemmas 01WF and 01K5
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Projectivity of a morphism is preserved by arbitrary base change. -/
theorem projective_base_change {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsProjective f] : IsProjective (pullback.snd f g) := by
  obtain ⟨n, hn, i, hi, hif⟩ := IsHProjective.exists_isClosedImmersion (f := f)
  have w : pullback.snd f g ≫ g = (pullback.fst f g ≫ i) ≫ ℙ(n; S) ↘ S := by
    rw [Category.assoc, hif, pullback.condition]
  let i' := ProjectiveSpace.liftBaseChange (pullback.snd f g) (pullback.fst f g ≫ i) w
  have hpb : IsPullback (pullback.fst f g) i' i (ProjectiveSpace.map n g) := by
    apply ProjectiveSpace.isPullback_liftBaseChange
    rw [hif]
    exact IsPullback.of_hasPullback f g
  have hi' : IsClosedImmersion i' := MorphismProperty.of_isPullback hpb hi
  exact { exists_isClosedImmersion :=
    ⟨n, hn, i', hi', ProjectiveSpace.liftBaseChange_over _ _ _⟩ }

end AlgebraicGeometry
