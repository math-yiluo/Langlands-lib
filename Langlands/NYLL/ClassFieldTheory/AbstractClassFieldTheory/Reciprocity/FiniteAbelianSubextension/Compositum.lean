/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions

/-!
# NYLL M296.017: the compositum of finite abelian subextensions

Modified by Worker 448, 14 November 2026: extract the definition
`FiniteAbelianSubextension.compositum` M296.017 (source lines 212–249) from the
pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`, prefix the namespace with
`Langlands.NYLL`, and import only the published M296 data module. Inside the
proof of the `commutative` field, the four source lemmas not yet proved in the
Library (`FiniteGaloisSubextension.extensionQuotient_inductionOn`,
`FiniteGaloisSubextension.extensionQuotientMk_apply`,
`FiniteAbelianSubextension.extensionQuotientMk_apply` and
`KummerTheory.mem_extensionSubgroup_iff`) are replaced by local `have`s with
the source statements and source proofs. The paired Markdown records every
modification. See `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

/-- The compositum `L₁L₂`, contravariantly represented by
`G_{L₁} ∩ G_{L₂}`. -/
def compositum (L₁ L₂ : FiniteAbelianSubextension K) :
    FiniteAbelianSubextension K where
  toFiniteGaloisExtension :=
    L₁.toFiniteGaloisExtension.compositum L₂.toFiniteGaloisExtension
  commutative := by
    let P := L₁.toFiniteGaloisExtension.compositum
      L₂.toFiniteGaloisExtension
    let : (extensionSubgroup K L₁.field L₁.below).Normal := L₁.normal
    let : (extensionSubgroup K L₂.field L₂.below).Normal := L₂.normal
    let : (extensionSubgroup K P.field P.below).Normal := P.normal
    -- Local copies, with their source statements and source proofs, of the
    -- source lemmas `FiniteGaloisSubextension.extensionQuotient_inductionOn`
    -- (at `P`), `FiniteGaloisSubextension.extensionQuotientMk_apply` (at `P`),
    -- `FiniteAbelianSubextension.extensionQuotientMk_apply` (at `L₁`, `L₂`)
    -- and `KummerTheory.mem_extensionSubgroup_iff`.
    have P_extensionQuotient_inductionOn :
        ∀ {motive : P.extensionQuotient → Prop} (q : P.extensionQuotient),
          (∀ k : K.toSubgroup, motive (P.extensionQuotientMk k)) → motive q :=
      fun {motive} q mk =>
        @Quotient.inductionOn' K.toSubgroup
          (QuotientGroup.leftRel (extensionSubgroup K P.field P.below))
          motive q mk
    have P_extensionQuotientMk_apply : ∀ k : K.toSubgroup,
        P.extensionQuotientMulEquiv (P.extensionQuotientMk k) =
          (QuotientGroup.mk k :
            K.toSubgroup ⧸ extensionSubgroup K P.field P.below) :=
      fun _ => rfl
    have L₁_extensionQuotientMk_apply : ∀ k : K.toSubgroup,
        L₁.extensionQuotientMulEquiv (L₁.extensionQuotientMk k) =
          (QuotientGroup.mk k :
            K.toSubgroup ⧸ extensionSubgroup K L₁.field L₁.below) :=
      fun _ => rfl
    have L₂_extensionQuotientMk_apply : ∀ k : K.toSubgroup,
        L₂.extensionQuotientMulEquiv (L₂.extensionQuotientMk k) =
          (QuotientGroup.mk k :
            K.toSubgroup ⧸ extensionSubgroup K L₂.field L₂.below) :=
      fun _ => rfl
    have mem_extensionSubgroup_iff :
        ∀ (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
          (k : K.toSubgroup),
          k ∈ extensionSubgroup (G := G) K L hLK ↔ (k : G) ∈ L :=
      fun _ _ _ _ => Iff.rfl
    refine ⟨⟨?_⟩⟩
    intro x y
    refine P_extensionQuotient_inductionOn
      (motive := fun x => x * y = y * x) x ?_
    intro a
    refine P_extensionQuotient_inductionOn
      (motive := fun y => P.extensionQuotientMk a * y =
        y * P.extensionQuotientMk a) y ?_
    intro b
    apply P.extensionQuotientMulEquiv.injective
    simp only [map_mul, P_extensionQuotientMk_apply]
    apply QuotientGroup.eq.mpr
    apply (mem_extensionSubgroup_iff K P.field P.below _).2
    constructor
    · have hcomm := L₁.commutative.is_comm.comm
          (L₁.extensionQuotientMk a) (L₁.extensionQuotientMk b)
      have hcommRaw := congrArg L₁.extensionQuotientMulEquiv hcomm
      simp only [map_mul, L₁_extensionQuotientMk_apply] at hcommRaw
      exact (mem_extensionSubgroup_iff K L₁.field L₁.below _).1
        (QuotientGroup.eq.mp hcommRaw)
    · have hcomm := L₂.commutative.is_comm.comm
          (L₂.extensionQuotientMk a) (L₂.extensionQuotientMk b)
      have hcommRaw := congrArg L₂.extensionQuotientMulEquiv hcomm
      simp only [map_mul, L₂_extensionQuotientMk_apply] at hcommRaw
      exact (mem_extensionSubgroup_iff K L₂.field L₂.below _).1
        (QuotientGroup.eq.mp hcommRaw)

end FiniteAbelianSubextension

end GroupOnly

end Langlands.NYLL.ClassFormation
