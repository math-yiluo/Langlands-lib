import Langlands.Shimura.PEL.HarrisTaylorLieCondition
import Mathlib.CategoryTheory.Sites.Spaces

/-! # Integer Lie rank forced by the Harris–Taylor central trace test -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField _root_.Algebra
open Langlands.AbelianScheme Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.HarrisTaylor

variable (L K : Type) [Field L] [NumberField L] [IsCMField L]
    [Field K] [NumberField K] [IsCMField K] [Algebra L K]
    {S : Scheme.{0}} (s : S ⟶ Spec (.of K))
    {A : Type} [Ring A] [Algebra ℚ A] [Algebra K A]
    (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B) (n : ℕ)

/-- On a nonempty smaller open, the identity trace gives an equality of natural ranks. -/
theorem centralLieTraceConditionAt_card
    {U : S.Opens} {J : Type} [Fintype J]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) J ≅ B.Lie.over U)
    (V : Over U) [Nonempty V.left]
    (h : CentralLieTraceConditionAt L s B i n e 1 V) :
    Fintype.card J = Module.finrank L K * n ^ 2 := by
  let : CharZero Γ(S, V.left) :=
    charZero_of_injective_ringHom (secHom s V.left).hom.injective
  apply Nat.cast_injective (R := Γ(S, V.left))
  simpa only [Nat.cast_mul, Nat.cast_pow] using
    centralLieTraceConditionAt_one L s i n e V h

/-- The actual finite Lie charts on a nonempty open have the prescribed integer size. -/
theorem centralLieTraceCondition_card
    (h : CentralLieTraceCondition L s B i n)
    {U : S.Opens} [Nonempty U] {J : Type} [Fintype J]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) J ≅ B.Lie.over U) :
    Fintype.card J = Module.finrank L K * n ^ 2 := by
  let : Nonempty ((Over.mk (𝟙 U) : Over U).left) := ‹Nonempty U›
  exact centralLieTraceConditionAt_card L K s B i n e (Over.mk (𝟙 U))
    (h U J e 1 (Over.mk (𝟙 U)))

/-- Reindex the actual finite Lie basis cover by points contained in its members. -/
def liePointedFiniteLocalBasisData : SheafOfModules.LocalGeneratorsData.{0} B.Lie := by
  classical
  let q := lieFiniteLocalBasisData B
  have hcover : ∀ x : S, ∃ j : q.I, x ∈ q.X j := by
    have hc := (_root_.Opens.coversTop_iff S q.X).mp q.coversTop
    intro x
    exact TopologicalSpace.Opens.mem_iSup.mp (hc.ge (Set.mem_univ x))
  choose j hj using hcover
  exact {
    I := S
    X := fun x => q.X (j x)
    coversTop := (_root_.Opens.coversTop_iff S (fun x => q.X (j x))).mpr (by
      apply top_le_iff.mp
      intro x _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hj x⟩)
    generators := fun x => q.generators (j x) }

instance liePointedFiniteLocalBasisData_isLocallyFreeData :
    (liePointedFiniteLocalBasisData B).IsLocallyFreeData := by
  refine { isIso := fun x => ?_ }
  dsimp only [liePointedFiniteLocalBasisData]
  infer_instance

instance liePointedFiniteLocalBasisData_fintype (x : S) :
    Fintype ((liePointedFiniteLocalBasisData B).generators x).I := by
  dsimp only [liePointedFiniteLocalBasisData]
  infer_instance

/-- Each member of the point-indexed Lie cover contains its indexing point. -/
theorem liePointedFiniteLocalBasisData_mem (x : S) :
    x ∈ (liePointedFiniteLocalBasisData B).X x := by
  dsimp only [liePointedFiniteLocalBasisData]
  exact (Classical.choose_spec (by
    have hc := (_root_.Opens.coversTop_iff S (lieFiniteLocalBasisData B).X).mp
      (lieFiniteLocalBasisData B).coversTop
    exact TopologicalSpace.Opens.mem_iSup.mp (hc.ge (Set.mem_univ x))))

/-- The trace test itself forces fixed local rank for the actual Lie module.
The cover is reindexed by base points, so every member used to compare ranks is nonempty. -/
theorem centralLieTraceCondition_lieRank
    (h : CentralLieTraceCondition L s B i n) :
    IsLocallyFreeOfRank B.Lie (Module.finrank L K * n ^ 2) := by
  classical
  refine ⟨liePointedFiniteLocalBasisData B, inferInstance, ?_⟩
  intro x
  let : Nonempty ((liePointedFiniteLocalBasisData B).X x) :=
    ⟨⟨x, liePointedFiniteLocalBasisData_mem B x⟩⟩
  exact ⟨Fintype.equivFinOfCardEq
    (centralLieTraceCondition_card L K s B i n h
      (asIso ((liePointedFiniteLocalBasisData B).generators x).π))⟩

/-- A separately supplied geometric relative dimension must equal the trace-forced rank
when the base is nonempty. This is uniqueness, not a converse establishing dimension. -/
theorem centralLieTraceCondition_relativeDimension_eq [Nonempty S]
    (h : CentralLieTraceCondition L s B i n) (g : ℕ)
    (hg : B.HasRelativeDimension g) :
    g = Module.finrank L K * n ^ 2 := by
  classical
  obtain ⟨q, hq, hcard⟩ := (lieLocalFreenessRank B).2 g hg
  let := hq
  let x : S := Classical.choice inferInstance
  have hc := (_root_.Opens.coversTop_iff S q.X).mp q.coversTop
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp (hc.ge (Set.mem_univ x))
  let eJ := (hcard j).some
  let : Fintype (q.generators j).I := Fintype.ofEquiv (Fin g) eJ.symm
  let : Nonempty (q.X j) := ⟨⟨x, hj⟩⟩
  have hJ := centralLieTraceCondition_card L K s B i n h (asIso (q.generators j).π)
  simpa only [Fintype.card_congr eJ, Fintype.card_fin] using hJ

variable (E : Type) [Field E] [NumberField E] [IsTotallyReal E]
    [Algebra E K] [IsQuadraticExtension E K] [IsScalarTower ℚ E K]
    [IsQuadraticExtension ℚ L] [IsScalarTower ℚ L K]

/-- Under the two quadratic degree hypotheses, the forced Lie rank is `[E:ℚ] n²`. -/
theorem centralLieTraceCondition_lieRank_totallyReal
    (h : CentralLieTraceCondition L s B i n) :
    IsLocallyFreeOfRank B.Lie (Module.finrank ℚ E * n ^ 2) := by
  rw [← finrank_imaginary_eq_totallyReal L K E]
  exact centralLieTraceCondition_lieRank L K s B i n h

/-- Under the arithmetic degree comparison, any existing geometric dimension is the
prescribed Harris dimension. No geometric-dimension existence is assumed or proved here. -/
theorem centralLieTraceCondition_relativeDimension_eq_totallyReal [Nonempty S]
    (h : CentralLieTraceCondition L s B i n) (g : ℕ)
    (hg : B.HasRelativeDimension g) :
    g = Module.finrank ℚ E * n ^ 2 := by
  rw [← finrank_imaginary_eq_totallyReal L K E]
  exact centralLieTraceCondition_relativeDimension_eq L K s B i n h g hg

end Langlands.Shimura.HarrisTaylor
