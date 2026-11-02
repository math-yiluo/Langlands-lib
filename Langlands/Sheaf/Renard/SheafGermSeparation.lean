import Langlands.Sheaf.Renard.SheafGermSeparationStatements
import Langlands.Sheaf.Renard.BasisStalkRepresentatives

/-!
# Renard II.2.1: sheaf separation and corrected target compatibility

The common-refinement criterion yields a cover on which a zero-germ section
vanishes. Sheaf uniqueness separates sections, and separation in the target
sheaf turns equal source germs into literal image compatibility.
-/

open CategoryTheory Opposite

universe u v w

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X] {B : OpenBasis X}

/-- A raw sheaf section with zero germ everywhere is zero, including on empty opens. -/
theorem rawSheafZeroGermSeparation (F : RawPresheaf.{u,v} B) :
    RawSheafZeroGermSeparationStatement F := by
  intro hF U s hs
  let C : BasisCover U := {
    members := {W | ∃ hWU : W.obj ≤ U.obj, restriction F hWU s = 0}
    le := fun W hW => hW.choose
    covers := by
      intro x hx
      have hs0 : rawGerm F U x hx s = rawGerm F U x hx 0 := by
        simpa only [rawGerm_zero] using hs x hx
      obtain ⟨W, hxW, hWU, hWU', heq⟩ := (rawGerm_eq_iff F x U U hx hx s 0).mp hs0
      exact ⟨W, ⟨hWU, by simpa using heq⟩, hxW⟩ }
  have hcompat : Compatible F (fun W : C.members => W.val) (fun _ => 0) := by
    intro W Z T hTW hTZ
    simp
  obtain ⟨t, _, huniq⟩ := hF U C (fun _ => 0) hcompat
  have hsamalg : IsAmalgamation F C.familyCovers (fun _ => 0) s := by
    intro W
    exact W.property.choose_spec
  have h0amalg : IsAmalgamation F C.familyCovers (fun _ => 0) 0 := by
    intro W
    exact map_zero _
  exact (huniq s hsamalg).trans (huniq 0 h0amalg).symm

/-- Additivity reduces equality of sheaf sections to zero-germ separation of their difference. -/
theorem rawSheafGermEquality (F : RawPresheaf.{u,v} B) :
    RawSheafGermEqualityStatement F := by
  intro hF U s t hs
  apply sub_eq_zero.mp
  apply rawSheafZeroGermSeparation F hF U (s - t)
  intro x hx
  simp only [map_sub, hs x hx, sub_self]

/-- Zero-germ separation for the actual normalized basis-sheaf object. -/
theorem sheafZeroGermSeparation (G : BasisSheaf.{u,v} B) :
    SheafZeroGermSeparationStatement G :=
  rawSheafZeroGermSeparation G.obj.obj G.property

/-- Germ equality detects equality on the actual normalized basis-sheaf object. -/
theorem sheafGermEquality (G : BasisSheaf.{u,v} B) :
    SheafGermEqualityStatement G :=
  rawSheafGermEquality G.obj.obj G.property

/-- Equal source germs give compatible images by separating only in the target sheaf. -/
theorem rawTargetGermCompatibility (F G : RawPresheaf.{u,v} B) (ψ : F ⟶ G) :
    RawTargetGermCompatibilityStatement.{u,v,w} F G ψ := by
  intro hG ι U s hs i j W hWi hWj
  apply rawSheafGermEquality G hG W
  intro x hx
  calc
    rawGerm G W x hx (restriction G hWi (ψ.app (op (U i)) (s i))) =
        rawStalkMap ψ x (rawGerm F (U i) x (hWi hx) (s i)) := by
      rw [rawGerm_restriction, rawStalkMap_germ]
    _ = rawStalkMap ψ x (rawGerm F (U j) x (hWj hx) (s j)) :=
      congrArg (rawStalkMap ψ x) (hs i j x (hWi hx) (hWj hx))
    _ = rawGerm G W x hx (restriction G hWj (ψ.app (op (U j)) (s j))) := by
      rw [rawStalkMap_germ, rawGerm_restriction]

/-- The corrected compatibility for a normalized source and a bundled target sheaf. -/
theorem targetGermCompatibility (F : Presheaf.{u,v} B) (G : BasisSheaf.{u,v} B)
    (ψ : F ⟶ G.obj) : TargetGermCompatibilityStatement.{u,v,w} F G ψ := by
  intro ι U s hs i j W hWi hWj
  apply sheafGermEquality G W
  intro x hx
  calc
    germ G.obj W x hx (restriction G.obj.obj hWi (ψ.hom.app (op (U i)) (s i))) =
        stalkMap ψ x (germ F (U i) x (hWi hx) (s i)) := by
      rw [germ_restriction, stalkMap_germ]
    _ = stalkMap ψ x (germ F (U j) x (hWj hx) (s j)) :=
      congrArg (stalkMap ψ x) (hs i j x (hWi hx) (hWj hx))
    _ = germ G.obj W x hx (restriction G.obj.obj hWj (ψ.hom.app (op (U j)) (s j))) := by
      rw [stalkMap_germ, germ_restriction]

/-- The complete closed three-universe separation and corrected-compatibility aggregate. -/
theorem renardSheafGermSeparation : RenardSheafGermSeparationStatement.{u,v,w} := by
  intro X _ B
  exact ⟨rawSheafZeroGermSeparation, rawSheafGermEquality,
    sheafZeroGermSeparation, sheafGermEquality,
    rawTargetGermCompatibility, targetGermCompatibility⟩

end Langlands.Sheaf.Renard
