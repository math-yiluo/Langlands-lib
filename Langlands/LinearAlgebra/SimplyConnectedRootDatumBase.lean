import Langlands.LinearAlgebra.SimplyConnectedRootDatum
import Mathlib.LinearAlgebra.RootSystem.Base

/-! # The induced base of a full-coroot root datum -/

noncomputable section

namespace Langlands.LinearAlgebra.SimplyConnectedRootDatum

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum ι X Y) [Finite ι] (B : P.Base)

/-- The base induced on the full-coroot root datum has the same indices. -/
def base (hfinite : Finite (Y ⧸ P.corootSpan ℤ)) : (rootDatum P).Base where
  support := B.support
  linearIndepOn_root := by
    exact B.linearIndepOn_root.map_injOn (weightMap P)
      (injective_toRootDatum_weightMap P hfinite).injOn
  linearIndepOn_coroot := by
    apply LinearIndependent.of_comp (P.corootSpan ℤ).subtype
    exact B.linearIndepOn_coroot
  root_mem_or_neg_mem r := by
    have hmap : (AddSubmonoid.closure (P.root '' (B.support : Set ι))).map
        (weightMap P).toAddMonoidHom =
        AddSubmonoid.closure ((rootDatum P).root '' (B.support : Set ι)) := by
      rw [AddMonoidHom.map_mclosure, ← Set.image_comp]
      rfl
    rcases B.root_mem_or_neg_mem r with h | h
    · left
      rw [← hmap]
      exact ⟨P.root r, h, rfl⟩
    · right
      rw [← hmap]
      exact ⟨-P.root r, h, by simp [rootDatum_root, root]⟩
  coroot_mem_or_neg_mem r := by
    have hmap : (AddSubmonoid.closure ((rootDatum P).coroot '' (B.support : Set ι))).map
        (P.corootSpan ℤ).subtype.toAddMonoidHom =
        AddSubmonoid.closure (P.coroot '' (B.support : Set ι)) := by
      rw [AddMonoidHom.map_mclosure, ← Set.image_comp]
      rfl
    have hmem {y : P.corootSpan ℤ}
        (hy : (y : Y) ∈ AddSubmonoid.closure (P.coroot '' (B.support : Set ι))) :
        y ∈ AddSubmonoid.closure ((rootDatum P).coroot '' (B.support : Set ι)) := by
      rw [← hmap] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      have : z = y := Subtype.ext hzy
      rwa [this] at hz
    rcases B.coroot_mem_or_neg_mem r with h | h
    · exact Or.inl (hmem h)
    · exact Or.inr (hmem h)

end Langlands.LinearAlgebra.SimplyConnectedRootDatum
