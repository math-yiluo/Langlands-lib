import Langlands.AlgebraicGeometry.AlgebraicSpace.BaseCompositionProperties
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopologyUniqueness
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # Structural diagonals after composition of bases -/

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.BaseComposition

variable {S T : Scheme.{u}} (g : S ⟶ T)

/-- The presheaf of the base scheme over itself is a terminal relative presheaf. -/
def schemeTerminalIso (S : Scheme.{u}) :
    (schemeYoneda S).obj (Over.mk (𝟙 S)) ≅ (⊤_ (Presheaf S)) :=
  (IsTerminal.isTerminalObj (schemeYoneda S) _ (Over.mkIdTerminal (X := S))).uniqueUpToIso
    terminalIsTerminal

/-- Composing the terminal relative presheaf gives the original base scheme over `T`. -/
def composedTerminalIso :
    presheaf g (⊤_ (Presheaf S)) ≅ (schemeYoneda T).obj ((Over.map g).obj (Over.mk (𝟙 S))) :=
  (presheafFunctor g).mapIso (schemeTerminalIso S).symm ≪≫ (schemeIso g (Over.mk (𝟙 S))).symm

/-- The absolute diagonal is the relative diagonal of the unique map to a terminal object,
up to its canonical pullback/product comparison. -/
theorem diag_iff_diagonal_terminal (W : MorphismProperty (Presheaf S)) [W.RespectsIso]
    (F : Presheaf S) : W (diag F) ↔ W.diagonal (terminal.from F) := by
  have hd : diag F = pullback.diagonal (terminal.from F) ≫ (prodIsoPullback F F).inv := by
    apply prod.hom_ext <;> simp
  rw [hd]
  exact MorphismProperty.cancel_right_of_respectsIso W
    (pullback.diagonal (terminal.from F)) (prodIsoPullback F F).inv

/-- A structural diagonal property survives base composition when it also holds for the
base morphism's diagonal and is stable under composition and base change. -/
theorem relative_diag_presheaf (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
    {F : Presheaf S}
    (hF : (MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S) (diag F))
    (hg : P (pullback.diagonal g)) :
    (MorphismProperty.inverseImage P (Over.forget T)).relative (schemeYoneda T)
      (diag (presheaf g F)) := by
  let WS : MorphismProperty (Presheaf S) :=
    (MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S)
  let WT : MorphismProperty (Presheaf T) :=
    (MorphismProperty.inverseImage P (Over.forget T)).relative (schemeYoneda T)
  let : WT.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange _
  have hrel : WT.diagonal (map g (terminal.from F)) :=
    relative_pullback_diagonal g P ((diag_iff_diagonal_terminal WS F).mp hF)
  have hbase : WT (diag (presheaf g (⊤_ (Presheaf S)))) := by
    apply relative_diag_of_iso P (composedTerminalIso g).symm
    apply relative_diag_schemeYoneda P
    change P (pullback.diagonal (𝟙 S ≫ g))
    exact (congrArg (fun a : S ⟶ T => P (pullback.diagonal a))
      (Category.id_comp g)).mpr hg
  have hbase' : WT.diagonal (terminal.from (presheaf g (⊤_ (Presheaf S)))) :=
    (diag_iff_diagonal_terminal WT _).mp hbase
  have htotal := WT.diagonal.comp_mem (map g (terminal.from F))
    (terminal.from (presheaf g (⊤_ (Presheaf S)))) hrel hbase'
  have heq : map g (terminal.from F) ≫ terminal.from (presheaf g (⊤_ (Presheaf S))) =
      terminal.from (presheaf g F) := terminalIsTerminal.hom_ext _ _
  exact (diag_iff_diagonal_terminal WT _).mpr (heq ▸ htotal)

/-- A quasi-separated space stays quasi-separated over a quasi-separated composed base map. -/
theorem quasiSeparated_space [QuasiSeparated g] {X : AlgebraicSpace S} (hX : IsQuasiSeparated X) :
    IsQuasiSeparated (space g X) := by
  have : MorphismProperty.IsStableUnderComposition (@QuasiCompact.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative (@QuasiCompact.{u})).toIsStableUnderComposition
  exact relative_diag_presheaf g (@QuasiCompact.{u}) hX inferInstance

/-- A separated space stays separated over a separated composed base map. -/
theorem separated_space [_root_.AlgebraicGeometry.IsSeparated g]
    {X : AlgebraicSpace S} (hX : IsSeparated X) : IsSeparated (space g X) := by
  have : MorphismProperty.IsStableUnderComposition (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})).toIsStableUnderComposition
  exact relative_diag_presheaf g (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) hX inferInstance

end Langlands.AlgebraicGeometry.AlgebraicSpace.BaseComposition
