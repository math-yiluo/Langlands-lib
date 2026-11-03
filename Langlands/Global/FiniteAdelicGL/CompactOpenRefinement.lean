import Langlands.Global.FiniteAdelicGL.LocalFactor

/-! # Compact open refinement at an actual finite place -/

noncomputable section
universe uF
set_option autoImplicit false

namespace Langlands.Global.FiniteAdelicGL

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ) (v : FinitePlace F)

/-- Refine a given open subgroup by the existing compact integral subgroup. -/
def compactOpenRefinement (U : OpenSubgroup (FiniteLocalGL F n v)) :
    OpenSubgroup (FiniteLocalGL F n v) :=
  localIntegral F n v ⊓ U

theorem compactOpenRefinement_le (U : OpenSubgroup (FiniteLocalGL F n v)) :
    compactOpenRefinement F n v U ≤ U :=
  inf_le_right

theorem isCompact_compactOpenRefinement (U : OpenSubgroup (FiniteLocalGL F n v)) :
    IsCompact (compactOpenRefinement F n v U : Set (FiniteLocalGL F n v)) :=
  (isCompact_localIntegral F n v).inter_right U.isClosed

/-- Compact open subgroups are cofinal among the open subgroups of the actual
finite-completion matrix group, including rank zero. -/
theorem compactOpen_cofinal :
    ∀ U : OpenSubgroup (FiniteLocalGL F n v),
      ∃ L : OpenSubgroup (FiniteLocalGL F n v),
        IsCompact (L : Set (FiniteLocalGL F n v)) ∧ L ≤ U :=
  fun U => ⟨compactOpenRefinement F n v U,
    isCompact_compactOpenRefinement F n v U, compactOpenRefinement_le F n v U⟩

end Langlands.Global.FiniteAdelicGL
