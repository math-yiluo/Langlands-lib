import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Representation.Whittaker.EntrywiseCharacter
import Langlands.Representation.Induction.Definitions
import Langlands.Group.GL.Blocks

/-!
# Gelfand–Graev representations of general linear groups and product Levis

The Gelfand–Graev representation of `GL_(n+1)(F)` is compact induction from the upper
unipotent subgroup `N` of the standard character. For a block shape `B`, the Gelfand–Graev
representation of the product Levi `B.Levi F` is compact induction from the product of the
block upper unipotent subgroups of the product of the blockwise entrywise characters.
-/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis

universe uF

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

/-- The scalar representation of `N` given by the standard character. -/
abbrev gelfandGraevCharacterRepresentation (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    Representation ℂ (upperUnipotent (n + 1) F) ℂ :=
  characterRepresentation (standardCharacter ψ n)

/-- Carrier of the Gelfand–Graev representation: smooth `ψ`-equivariant functions with
compact support modulo `N`. -/
abbrev GelfandGraevFunctions (ψ : UnitaryAdditiveCharacter F) (n : ℕ) : Type uF :=
  Induction.CompactFunctions (upperUnipotent (n + 1) F) (gelfandGraevCharacterRepresentation ψ n)

/-- The Gelfand–Graev representation `c-Ind_N^G ψ` of `GL_(n+1)(F)`, by right translation. -/
abbrev gelfandGraev (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    Representation ℂ (Langlands.GeneralLinear (n + 1) F) (GelfandGraevFunctions ψ n) :=
  Induction.compactInduced (upperUnipotent (n + 1) F) (gelfandGraevCharacterRepresentation ψ n)

section Levi

variable {n : ℕ} (B : BlockShape n)

/-- The product of the block upper unipotent subgroups inside the product Levi. -/
def leviUpperUnipotent : Subgroup (B.Levi F) :=
  Subgroup.pi Set.univ fun i => upperUnipotent (B.size i) F

/-- The coordinate of a product unipotent element in one block. -/
def leviUpperUnipotentCoordinate (i : Fin B.length) :
    leviUpperUnipotent (F := F) B →* upperUnipotent (B.size i) F where
  toFun u := ⟨u.val i, u.property i (Set.mem_univ i)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The product of the blockwise entrywise characters of an additive character. -/
def leviWhittakerCharacter (ψ : AddChar F ℂ) : leviUpperUnipotent (F := F) B →* ℂˣ :=
  ∏ i : Fin B.length, (entrywiseCharacter ψ (B.size i)).comp (leviUpperUnipotentCoordinate B i)

@[simp] theorem leviWhittakerCharacter_apply (ψ : AddChar F ℂ) (u : leviUpperUnipotent (F := F) B) :
    leviWhittakerCharacter B ψ u =
      ∏ i : Fin B.length, entrywiseCharacter ψ (B.size i) (leviUpperUnipotentCoordinate B i u) := by
  simp [leviWhittakerCharacter]

/-- The scalar representation of the product unipotent subgroup given by the Levi character. -/
abbrev leviGelfandGraevCharacterRepresentation (ψ : AddChar F ℂ) :
    Representation ℂ (leviUpperUnipotent (F := F) B) ℂ :=
  characterRepresentation (leviWhittakerCharacter B ψ)

/-- Carrier of the Levi Gelfand–Graev representation. -/
abbrev LeviGelfandGraevFunctions (ψ : AddChar F ℂ) : Type uF :=
  Induction.CompactFunctions (leviUpperUnipotent (F := F) B)
    (leviGelfandGraevCharacterRepresentation B ψ)

/-- The Gelfand–Graev representation `c-Ind_{N_M}^M ψ_M` of the product Levi `M = B.Levi F`. -/
abbrev leviGelfandGraev (ψ : AddChar F ℂ) :
    Representation ℂ (B.Levi F) (LeviGelfandGraevFunctions B ψ) :=
  Induction.compactInduced (leviUpperUnipotent (F := F) B)
    (leviGelfandGraevCharacterRepresentation B ψ)

end Levi

end Langlands.Whittaker
