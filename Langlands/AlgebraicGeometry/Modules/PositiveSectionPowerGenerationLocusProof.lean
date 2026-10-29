import Langlands.AlgebraicGeometry.Modules.PositiveSectionPowerGenerationLocusStatement
import Langlands.AlgebraicGeometry.Modules.TensorSectionGenerationLocusProof
import Langlands.AlgebraicGeometry.Picard.TensorRankOneProof

/-! # The generation locus of a positive power of a line-bundle section -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.SchemeModule

open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Picard

variable {X : Scheme.{u}}

/-- The zeroth power of any section, the unit section of the structure module, trivializes
on the whole scheme. -/
theorem trivializationOpen_sectionPow_zero (M : X.Modules) (s : GlobalSections M) :
    trivializationOpen (tensorPow M 0) (sectionPow M s 0) = ⊤ := by
  have : IsIso (sectionHom (tensorPow M 0) (sectionPow M s 0)) := by
    rw [sectionHom_sectionPow_zero]
    exact IsIso.id _
  refine top_unique (le_sSup ?_)
  change IsIso ((Scheme.Modules.restrictFunctor (⊤ : X.Opens).ι).map
    (sectionHom (tensorPow M 0) (sectionPow M s 0)))
  infer_instance

/-- For a line bundle, the whole trivialization open of the next power of a section is the
intersection of the whole trivialization opens of the section and of the current power. -/
theorem trivializationOpen_sectionPow_succ_eq_inf (L : LineBundle X)
    (s : GlobalSections L.obj) (n : ℕ) :
    trivializationOpen (tensorPow L.obj (n + 1)) (sectionPow L.obj s (n + 1)) =
      trivializationOpen L.obj s ⊓
        trivializationOpen (tensorPow L.obj n) (sectionPow L.obj s n) :=
  tensorSectionGenerationLocus X L ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne X L n⟩
    s (sectionPow L.obj s n)

/-- For a line bundle, the whole trivialization open of every successor power of a section
is the whole trivialization open of the section. -/
theorem trivializationOpen_sectionPow_succ (L : LineBundle X) (s : GlobalSections L.obj)
    (n : ℕ) :
    trivializationOpen (tensorPow L.obj (n + 1)) (sectionPow L.obj s (n + 1)) =
      trivializationOpen L.obj s := by
  induction n with
  | zero =>
    rw [trivializationOpen_sectionPow_succ_eq_inf, trivializationOpen_sectionPow_zero,
      inf_top_eq]
  | succ n ih => rw [trivializationOpen_sectionPow_succ_eq_inf, ih, inf_idem]

/-- For a line bundle on an arbitrary scheme, every positive power of a global section has
the same whole trivialization open as the section. -/
theorem positiveSectionPowerGenerationLocus :
    PositiveSectionPowerGenerationLocusStatement.{u} := by
  intro X L s n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact trivializationOpen_sectionPow_succ L s m

/-- Consumer form of `positiveSectionPowerGenerationLocus`. -/
theorem trivializationOpen_sectionPow {X : Scheme.{u}} (L : LineBundle X)
    (s : GlobalSections L.obj) {n : ℕ} (hn : 0 < n) :
    trivializationOpen (tensorPow L.obj n) (sectionPow L.obj s n) =
      trivializationOpen L.obj s :=
  positiveSectionPowerGenerationLocus X L s n hn

end Langlands.SchemeModule
