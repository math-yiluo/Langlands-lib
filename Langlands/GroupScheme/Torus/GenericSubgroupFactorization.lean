import Langlands.AlgebraicGeometry.IntegralDominantImage
import Langlands.GroupScheme.ReducedBaseSmooth.Translation
import Langlands.GroupScheme.Torus.SelfCentralizingConjugacyClosedEmbeddingReduction

/-! # Extending subgroup factorizations across a dense base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GenericSubgroupFactorization

open Langlands.AlgebraicGeometry (HasNormalStalks integralDominantImageOpen
  integralDominantImageOpenLift integralDominantImageOpenLift_comp
  range_comp_subset_integralDominantImageOpen)
open SelfCentralizingConjugacyClosedEmbeddingReduction (exists_factor_of_fppf)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} {B Q L : GroupScheme S}

/-- A group homomorphism from a smooth group with geometrically connected fibres
factors through a monomorphic homomorphism if it does so on an open neighbourhood
of the unit section. -/
theorem exists_groupFactor_of_open [Smooth B.X.hom] [GeometricallyConnected B.X.hom]
    (j : Q ⟶ L) [Mono j.hom.hom] (b : B ⟶ L)
    {U : Over S} (i : U ⟶ B.X) [IsOpenImmersion i.left]
    (hunit : Set.range η[B.X].left ⊆ Set.range i.left)
    (v : U ⟶ Q.X) (hv : v ≫ j.hom.hom = i ≫ b.hom.hom) :
    ∃ c : B ⟶ Q, c ≫ j = b := by
  let p := (i ⊗ₘ i) ≫ μ[B.X]
  have : Surjective p.left := by
    rw [surjective_iff, ← Set.range_eq_univ]
    exact ReducedBaseSmooth.range_tensorHom_comp_mul_eq_univ B i (fun s => by
      change Smooth (pullback.snd B.X.hom (S.fromSpecResidueField s))
      infer_instance) (fun _ => inferInstance) hunit
  have : Smooth U.hom := by rw [← Over.w i]; infer_instance
  have : Smooth p.left := ReducedBaseSmooth.smooth_tensorHom_comp_mul B i
  obtain ⟨c, hc⟩ := exists_factor_of_fppf p j.hom.hom b.hom.hom ((v ⊗ₘ v) ≫ μ[Q.X]) (by
    dsimp only [p]
    simp only [Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, hv])
  have : IsMonHom c := by
    constructor
    · apply (cancel_mono j.hom.hom).mp
      rw [Category.assoc, hc, IsMonHom.one_hom, IsMonHom.one_hom]
    · apply (cancel_mono j.hom.hom).mp
      rw [Category.assoc, hc, IsMonHom.mul_hom b.hom.hom, Category.assoc,
        IsMonHom.mul_hom j.hom.hom, tensorHom_comp_tensorHom_assoc, hc]
  exact ⟨Grp.homMk c, (Grp.forget (Over S)).map_injective hc⟩

variable (j : Q ⟶ L) [Mono j.hom.hom.left]
  [LocallyOfFiniteType j.hom.hom.left] [QuasiCompact j.hom.hom.left] (b : B ⟶ L)

/-- The schematic image of a dominant lift in the pullback produces an open
neighbourhood of the unit in the normal source group. The unit is in the
image closure when its pullback to a dense test lies in the supplied lift. -/
theorem exists_openUnitFactor_of_denseLift [IsReduced S] [IsIntegral B.X.left]
    (hB : HasNormalStalks B.X.left)
    {Z : Over S} [IsIntegral Z.left] (z : Z ⟶ B.X) [QuasiCompact z.left] [IsDominant z.left]
    (l : Z ⟶ Q.X) (hl : l ≫ j.hom.hom = z ≫ b.hom.hom)
    {S₀ : Scheme.{u}} (s : S₀ ⟶ S) [IsDominant s]
    (a₀ : Over.mk s ⟶ Z) (ha₀ : a₀ ≫ z = toUnit (Over.mk s) ≫ η[B.X]) :
    ∃ (U : Over S) (i : U ⟶ B.X) (v : U ⟶ Q.X),
      IsOpenImmersion i.left ∧ Set.range η[B.X].left ⊆ Set.range i.left ∧
        v ≫ j.hom.hom = i ≫ b.hom.hom := by
  let P := pullback j.hom.hom b.hom.hom
  let pQ : P ⟶ Q.X := pullback.fst _ _
  let pB : P ⟶ B.X := pullback.snd _ _
  have hpb := (IsPullback.of_hasPullback j.hom.hom b.hom.hom).map (Over.forget S)
  have : Mono pB.left :=
    MorphismProperty.of_isPullback (P := .monomorphisms _) hpb
      (inferInstanceAs (Mono j.hom.hom.left))
  have : LocallyOfFiniteType pB.left :=
    MorphismProperty.of_isPullback hpb (inferInstanceAs (LocallyOfFiniteType j.hom.hom.left))
  have : QuasiCompact pB.left :=
    MorphismProperty.of_isPullback hpb (inferInstanceAs (QuasiCompact j.hom.hom.left))
  let p : Z ⟶ P := pullback.lift l z hl
  have hp : p ≫ pB = z := pullback.lift_snd _ _ _
  have hqc : QuasiCompact (p.left ≫ pB.left) := by rw [← Over.comp_left, hp]; infer_instance
  have : QuasiCompact p.left := QuasiCompact.of_comp p.left pB.left
  have : IsDominant (p.left ≫ pB.left) := by rw [← Over.comp_left, hp]; infer_instance
  let V := integralDominantImageOpen p.left pB.left hB
  let U : Over S := Over.mk (V.ι ≫ B.X.hom)
  let i : U ⟶ B.X := Over.homMk V.ι rfl
  let w := integralDominantImageOpenLift p.left pB.left hB
  have hw : w ≫ pB.left = V.ι := integralDominantImageOpenLift_comp p.left pB.left hB
  let v : U ⟶ P := Over.homMk w (by rw [← Over.w pB, ← Category.assoc, hw]; rfl)
  have hv : v ≫ pB = i := Over.OverMorphism.ext hw
  have hi : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion V.ι)
  let u : 𝟙_ (Over S) ⟶ P := pullback.lift η[Q.X] η[B.X] (by simp only [IsMonHom.one_hom])
  have hu : u ≫ pB = η[B.X] := pullback.lift_snd _ _ _
  have : Mono pB := Over.mono_of_mono_left _
  have hgen : a₀ ≫ p = toUnit (Over.mk s) ≫ u := by
    apply (cancel_mono pB).mp
    simpa only [Category.assoc, hu, hp] using ha₀
  have hgen' : a₀.left ≫ p.left = s ≫ u.left := congrArg Over.Hom.left hgen
  have hunit : Set.range η[B.X].left ⊆ Set.range i.left := by
    have : IsReduced (𝟙_ (Over S)).left := inferInstanceAs (IsReduced S)
    change Set.range η[B.X].left ⊆ Set.range V.ι
    rw [Scheme.Opens.range_ι, ← hu, Over.comp_left]
    exact range_comp_subset_integralDominantImageOpen p.left pB.left u.left s a₀.left hgen' hB
  refine ⟨U, i, v ≫ pQ, hi, hunit, ?_⟩
  rw [Category.assoc, show pQ ≫ j.hom.hom = pB ≫ b.hom.hom from pullback.condition,
    ← Category.assoc, hv]

/-- A dominant lift of a normal integral smooth group into a monomorphic
subgroup extends if that lift contains the unit after a dense base change
and the source has geometrically connected fibres. -/
theorem exists_groupFactor_of_denseLift [IsReduced S] [IsIntegral B.X.left]
    [Smooth B.X.hom] [GeometricallyConnected B.X.hom]
    (hB : HasNormalStalks B.X.left)
    {Z : Over S} [IsIntegral Z.left] (z : Z ⟶ B.X) [QuasiCompact z.left] [IsDominant z.left]
    (l : Z ⟶ Q.X) (hl : l ≫ j.hom.hom = z ≫ b.hom.hom)
    {S₀ : Scheme.{u}} (s : S₀ ⟶ S) [IsDominant s]
    (a₀ : Over.mk s ⟶ Z) (ha₀ : a₀ ≫ z = toUnit (Over.mk s) ≫ η[B.X]) :
    ∃ c : B ⟶ Q, c ≫ j = b := by
  obtain ⟨U, i, v, hi, hunit, hv⟩ := exists_openUnitFactor_of_denseLift j b hB z l hl s a₀ ha₀
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  exact exists_groupFactor_of_open j b i hunit v hv

/-- Choose the whole-group factor of a dense lift, with its defining equation. -/
def groupFactorOfDenseLift [IsReduced S] [IsIntegral B.X.left]
    [Smooth B.X.hom] [GeometricallyConnected B.X.hom]
    (hB : HasNormalStalks B.X.left)
    {Z : Over S} [IsIntegral Z.left] (z : Z ⟶ B.X) [QuasiCompact z.left] [IsDominant z.left]
    (l : Z ⟶ Q.X) (hl : l ≫ j.hom.hom = z ≫ b.hom.hom)
    {S₀ : Scheme.{u}} (s : S₀ ⟶ S) [IsDominant s]
    (a₀ : Over.mk s ⟶ Z) (ha₀ : a₀ ≫ z = toUnit (Over.mk s) ≫ η[B.X]) :
    { c : B ⟶ Q // c ≫ j = b } :=
  let h := exists_groupFactor_of_denseLift j b hB z l hl s a₀ ha₀
  ⟨h.choose, h.choose_spec⟩

end Langlands.GroupScheme.GenericSubgroupFactorization
