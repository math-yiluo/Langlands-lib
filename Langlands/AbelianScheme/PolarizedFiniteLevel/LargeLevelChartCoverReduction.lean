import Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelChartCoverStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameChartRepresentabilityStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusBaseChangeStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusCoverStatement

/-! # Open charts covering the moduli functor from frame charts -/

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- The preimage of an open is everything exactly when the image lies in it. -/
theorem preimage_eq_top_iff_range_subset {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) :
    f ⁻¹ᵁ U = ⊤ ↔ Set.range f.base ⊆ (U : Set Y) := by
  constructor
  · rintro h _ ⟨x, rfl⟩
    have hx : x ∈ f ⁻¹ᵁ U := h ▸ trivial
    exact hx
  · intro h
    exact eq_top_iff.mpr fun x _ => h ⟨x, rfl⟩

/-- For a datum whose class is restricted along `f`, membership in a frame chart
is the condition that `f` lands in the frame locus. -/
theorem frameChart_mem_range_iff (Hbc : FrameLocusBaseChangeStatement.{0})
    {P : Prerequisites.{0}} {g d n : ℕ} (hd : 0 < d) (hn : 3 ≤ n)
    {ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2 * g) → ZMod n}
    {X : LevelBase n} (a : uliftYoneda.{1}.obj X ⟶ moduliFunctor P g d n hd hn)
    (ha : ∀ (T : LevelBase n) (b : Datum P T.obj g d n),
      b.classOf ∈ Set.range (a.app (op T)) ↔ b.frameLocus ρ = ⊤)
    {S T : LevelBase n} (b : Datum P S.obj g d n) (f : T ⟶ S) :
    (moduliFunctor P g d n hd hn).map f.op b.classOf ∈ Set.range (a.app (op T)) ↔
      Set.range f.hom.base ⊆ (b.frameLocus ρ : Set S.obj) := by
  refine (ha T (b.pullback f.hom)).trans ?_
  rw [Hbc P S.obj T.obj g d n hd b f.hom ρ]
  exact preimage_eq_top_iff_range_subset f.hom _

set_option linter.defProp false in
/-- Proved definition: frame-chart representability, base change of the frame
locus and covering by frame loci at large level imply the published
`LargeLevelChartCoverStatement`. -/
def largeLevelChartCover_of_frameCharts
    (Hframe : FrameChartRepresentabilityStatement)
    (Hbc : FrameLocusBaseChangeStatement.{0})
    (Hcov : FrameLocusCoverStatement.{0}) :
    LargeLevelChartCoverStatement := by
  intro P g d hg hd
  obtain ⟨N, hN⟩ := Hcov P g d hg hd
  refine ⟨N, fun n hNn hn => ?_⟩
  choose X a hinj hrange using Hframe P g d n hd hn
  refine ⟨Fin (cubicProjectiveDimension g d + 2) → Fin (2 * g) → ZMod n, X, a,
    fun ρ => ⟨hinj ρ, fun S ξ => ?_⟩, fun S ξ x => ?_⟩
  · change Moduli P S.obj g d n at ξ
    obtain ⟨b, rfl⟩ := Quotient.exists_rep ξ
    exact ⟨b.frameLocus ρ, fun T f =>
      frameChart_mem_range_iff Hbc hd hn (a ρ) (hrange ρ) b f⟩
  · change Moduli P S.obj g d n at ξ
    obtain ⟨b, rfl⟩ := Quotient.exists_rep ξ
    obtain ⟨ρ, hρ⟩ := hN n hNn S.obj S.level_isUnit b x
    exact ⟨ρ, b.frameLocus ρ, hρ, fun T f =>
      frameChart_mem_range_iff Hbc hd hn (a ρ) (hrange ρ) b f⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel
