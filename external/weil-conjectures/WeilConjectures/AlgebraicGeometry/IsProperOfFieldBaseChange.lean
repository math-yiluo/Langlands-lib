/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.FieldExtensionFpqcCover
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# Properness descends along a field extension

Source: Stacks Project, Descent, Lemma 35.23.16 (Tag 02L1), specialized to a field extension
(blueprint: lem-pc-proper-descends-field).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite type scheme over a field is proper if its base change to an extension field is
proper. Source: Stacks Project, Descent, Tag 02L1 (lemma-descending-property-proper)
(blueprint: lem-pc-proper-descends-field).

Proof:
1. The map `Spec K → Spec k` is flat, surjective and quasi-compact
   (lem-pc-field-extension-fpqc-cover).
2. The stated properness of the second pullback projection gives separatedness of `f` by
   `isSeparated_of_flat_surjective_baseChange` (lem-weil-pbc-fpqc-descend-separated).
3. Universal closedness descends for this affine pullback along a flat, surjective,
   quasi-compact map by Mathlib's `DescendsAlong` instance
   (lem-weil-pbc-universally-closed-affine-descent).
4. The locally finite type and quasi-compact hypotheses, together with separatedness and
   universal closedness, give `IsProper f` by the `IsProper` constructor. -/
theorem isProper_of_field_baseChange {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    [IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))] :
    IsProper f := by
  obtain ⟨hflat, hsurj, hqc, _⟩ :=
    fpqcCover_specMap_algebraMap_of_field (k := k) (K := K)
  let := hflat
  let := hsurj
  let := hqc
  let := isSeparated_of_flat_surjective_baseChange f
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let : UniversallyClosed f := MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @UniversallyClosed) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨hsurj, hflat⟩, hqc⟩ inferInstance
  exact ⟨⟩

end AlgebraicGeometry
