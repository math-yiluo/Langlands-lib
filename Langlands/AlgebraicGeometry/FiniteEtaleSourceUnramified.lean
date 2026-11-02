import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Unramifiedness detected by a finite etale source cover -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry

variable {W X S : Scheme.{u}} (p : W ⟶ X) (g : X ⟶ S)

/-- The comparison from the kernel pair over `X` to the kernel pair over `S`. -/
def sourceDiagonalComparison : pullback p p ⟶ pullback (p ≫ g) (p ≫ g) :=
  pullback.map p p (p ≫ g) (p ≫ g) (𝟙 W) (𝟙 W) g
    (by simp) (by simp)

@[reassoc (attr := simp)]
theorem sourceDiagonalComparison_fst :
    sourceDiagonalComparison p g ≫ pullback.fst (p ≫ g) (p ≫ g) =
      pullback.fst p p := by
  simp [sourceDiagonalComparison]

@[reassoc (attr := simp)]
theorem sourceDiagonalComparison_snd :
    sourceDiagonalComparison p g ≫ pullback.snd (p ≫ g) (p ≫ g) =
      pullback.snd p p := by
  simp [sourceDiagonalComparison]

/-- The map between products over `S` induced by the source cover on both factors. -/
def sourceDiagonalCover : pullback (p ≫ g) (p ≫ g) ⟶ pullback g g :=
  pullback.map (p ≫ g) (p ≫ g) g g p p (𝟙 S) (by simp) (by simp)

/-- The comparison is the base change of the diagonal of `g`. -/
theorem sourceDiagonalComparison_isPullback :
    IsPullback (pullback.fst p p ≫ p) (sourceDiagonalComparison p g)
      (pullback.diagonal g) (sourceDiagonalCover p g) := by
  exact pullback_map_diagonal_isPullback p p g

instance sourceDiagonalComparison_mono : Mono (sourceDiagonalComparison p g) :=
  (sourceDiagonalComparison_isPullback p g).mono_snd_of_mono

/-- With both source morphisms etale, the pulled-back diagonal is etale. -/
theorem sourceDiagonalComparison_etale [Etale p] [Etale (p ≫ g)] :
    Etale (sourceDiagonalComparison p g) := by
  have : Etale (sourceDiagonalComparison p g ≫ pullback.fst (p ≫ g) (p ≫ g)) := by
    rw [sourceDiagonalComparison_fst]
    infer_instance
  exact Etale.of_comp _ (pullback.fst (p ≫ g) (p ≫ g))

/-- The product map induced by a quasi-compact flat surjective cover is fpqc. -/
theorem sourceDiagonalCover_fpqc [Surjective p] [Flat p] [QuasiCompact p] :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (sourceDiagonalCover p g) := by
  exact MorphismProperty.pullbackMap
    (P := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ rfl rfl

/-- The diagonal is open if a quasi-compact surjective etale source cover and
its composite with the original morphism are etale. -/
theorem isOpenImmersion_diagonal_of_surjective_etale_comp
    [Etale p] [Surjective p] [QuasiCompact p] [Etale (p ≫ g)] :
    IsOpenImmersion (pullback.diagonal g) := by
  have : Etale (sourceDiagonalComparison p g) := sourceDiagonalComparison_etale p g
  have : IsOpenImmersion (sourceDiagonalComparison p g) :=
    IsOpenImmersion.of_flat_of_mono _
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsOpenImmersion) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (sourceDiagonalComparison_isPullback p g).flip
    (sourceDiagonalCover_fpqc p g) inferInstance

/-- Formal unramifiedness descends from an etale composite along a
quasi-compact surjective etale source cover. -/
theorem formallyUnramified_of_surjective_etale_comp
    [Etale p] [Surjective p] [QuasiCompact p] [Etale (p ≫ g)] :
    FormallyUnramified g := by
  have : IsOpenImmersion (pullback.diagonal g) :=
    isOpenImmersion_diagonal_of_surjective_etale_comp p g
  infer_instance

/-- In particular, a finite etale surjective source cover detects formal
unramifiedness when the composite is etale. -/
theorem formallyUnramified_of_finiteEtale_comp
    [IsFinite p] [Etale p] [Surjective p] [Etale (p ≫ g)] :
    FormallyUnramified g :=
  formallyUnramified_of_surjective_etale_comp p g

end Langlands.AlgebraicGeometry
