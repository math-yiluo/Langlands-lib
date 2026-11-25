/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Descent of separatedness along a flat surjective quasi-compact morphism

Source: Stacks Project, Descent, Lemma Tag 02KU (lemma-descending-property-separated),
the descent direction for a one-member fpqc covering
(blueprint: lem-weil-pbc-fpqc-descend-separated).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Separatedness descends along a flat surjective quasi-compact base change.
Source: Stacks Project, Descent, Tag 02KU, with Topologies Tag 03L7 (2).
(blueprint: lem-weil-pbc-fpqc-descend-separated)

Proof:
1. The diagonal of `pullback.snd f g` is a closed immersion by separatedness, hence
   universally closed by Mathlib's closed-immersion instance (Stacks Tag 01W5).
2. Apply Mathlib's descent instance for `MorphismProperty.diagonal @UniversallyClosed`
   along surjective flat quasi-compact morphisms. It combines universal-closedness descent
   (Tag 02KS) with the canonical base-change identification of diagonals. This gives
   universal closedness of the diagonal of `f` directly, without constructing an fpqc family.
3. Every scheme diagonal is an immersion (Tag 01KJ), hence a preimmersion. Universal
   closedness makes its range closed. `IsClosedImmersion.of_isPreimmersion` (Tag 01IQ)
   therefore makes the diagonal a closed immersion, which is precisely separatedness.
-/
theorem isSeparated_of_flat_surjective_baseChange {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [Flat g] [Surjective g] [QuasiCompact g]
    [IsSeparated (pullback.snd f g)] : IsSeparated f := by
  have hbase : (MorphismProperty.diagonal @UniversallyClosed) (pullback.snd f g) := by
    rw [MorphismProperty.diagonal_iff]
    infer_instance
  have hdiag : (MorphismProperty.diagonal @UniversallyClosed) f :=
    MorphismProperty.of_pullback_snd_of_descendsAlong
      (P := MorphismProperty.diagonal @UniversallyClosed)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hbase
  have : UniversallyClosed (pullback.diagonal f) :=
    MorphismProperty.diagonal_iff.mp hdiag
  exact ⟨IsClosedImmersion.of_isPreimmersion (pullback.diagonal f)
    (pullback.diagonal f).isClosedMap.isClosed_range⟩

end AlgebraicGeometry
