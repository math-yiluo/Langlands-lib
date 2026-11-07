/-
Ported from `Definitions/Def_Mathlib_RingTheory_Invariant_FixedSubringGaloisGroup.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports. The paired Markdown file lists the changes.
-/
import Mathlib
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace FixedPoints

variable {S : Type*} [CommRing S] {G : Type*} [Group G] [MulSemiringAction G S]
  [FaithfulSMul G S]

theorem isGaloisGroup_subring : IsGaloisGroup G (FixedPoints.subring S G) S where
  faithful := inferInstance
  commutes := ⟨fun g r s => by
    show g • ((r : S) * s) = (r : S) * (g • s); rw [smul_mul', r.2 g]⟩
  isInvariant := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩

end FixedPoints

/--
info: 'FixedPoints.isGaloisGroup_subring' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FixedPoints.isGaloisGroup_subring
