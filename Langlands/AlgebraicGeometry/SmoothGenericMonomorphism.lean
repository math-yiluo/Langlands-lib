import Langlands.AlgebraicGeometry.SmoothReducedBase
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Smooth morphisms detected as open immersions by a dominant base change -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SmoothGenericMonomorphism

variable {S T : Scheme.{u}} [IsReduced S] (b : T ⟶ S) [IsDominant b]
    {X Y : Over S} (f : X ⟶ Y) [Smooth X.hom] [IsSeparated X.hom]
    [Smooth f.left] [Mono ((Over.pullback b).map f)]

include b in
/-- A smooth map from a smooth separated family over a reduced base is a
monomorphism if a dominant base change makes it a monomorphism. -/
theorem mono_of_mono_baseChange : Mono f.left := by
  let P := pullback f.left f.left
  let pP : P ⟶ S := pullback.fst f.left f.left ≫ X.hom
  have hp : pullback.fst f.left f.left ≫ X.hom =
      pullback.snd f.left f.left ≫ X.hom := by
    rw [← Over.w f, ← Category.assoc, pullback.condition, Category.assoc]
  have : Smooth (pullback.fst f.left f.left) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : Smooth pP := by dsimp only [pP]; infer_instance
  have : IsReduced P := SmoothReducedBase.isReduced_of_smooth_of_isReduced pP
  let Z : Over S := Over.mk pP
  let a₁ : Z ⟶ X := Over.homMk (pullback.fst f.left f.left) rfl
  let a₂ : Z ⟶ X := Over.homMk (pullback.snd f.left f.left) hp.symm
  have ha : a₁ ≫ f = a₂ ≫ f := Over.OverMorphism.ext pullback.condition
  have hK : (Over.pullback b).map a₁ = (Over.pullback b).map a₂ := by
    apply (cancel_mono ((Over.pullback b).map f)).mp
    rw [← Functor.map_comp, ← Functor.map_comp, ha]
  let i : pullback pP b ⟶ P := pullback.fst pP b
  have : IsDominant i := by
    apply (isDominant_iff i).mpr
    change Dense (Set.range (pullback.fst pP b))
    rw [Scheme.Pullback.range_fst]
    exact ((isDominant_iff b).mp inferInstance).preimage pP.isOpenMap
  have hgen : i ≫ pullback.fst f.left f.left = i ≫ pullback.snd f.left f.left := by
    have h := congrArg (fun a => a.left ≫ pullback.fst X.hom b) hK
    simp only [Over.pullback_map_left, pullback.lift_fst] at h
    change i ≫ pullback.fst f.left f.left = i ≫ pullback.snd f.left f.left at h
    exact h
  have hpr : pullback.fst f.left f.left = pullback.snd f.left f.left :=
    ext_of_isDominant_of_isSeparated X.hom hp i hgen
  constructor
  intro W g h hgh
  calc
    g = pullback.lift g h hgh ≫ pullback.fst f.left f.left :=
      (pullback.lift_fst _ _ _).symm
    _ = pullback.lift g h hgh ≫ pullback.snd f.left f.left := by rw [hpr]
    _ = h := pullback.lift_snd _ _ _

include b in
/-- The same smooth map is an open immersion. -/
theorem isOpenImmersion_of_mono_baseChange : IsOpenImmersion f.left := by
  have : Mono f.left := mono_of_mono_baseChange b f
  exact IsOpenImmersion.of_flat_of_mono f.left

/-- The open image of a smooth map. -/
def openImage {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) [Smooth f.left] : Y.left.Opens :=
  ⟨Set.range f.left, f.left.isOpenMap.isOpen_range⟩

/-- The actual open-image isomorphism, with the original map as its composite
with the open inclusion. -/
def openImageIso : X.left ≅ (openImage f).toScheme := by
  have : IsOpenImmersion f.left := isOpenImmersion_of_mono_baseChange b f
  exact IsOpenImmersion.isoOfRangeEq f.left (openImage f).ι (by
    rw [Scheme.Opens.range_ι]
    rfl)

@[reassoc (attr := simp)]
theorem openImageIso_hom_ι : (openImageIso b f).hom ≫ (openImage f).ι = f.left := by
  have : IsOpenImmersion f.left := isOpenImmersion_of_mono_baseChange b f
  apply IsOpenImmersion.isoOfRangeEq_hom_fac
  rw [Scheme.Opens.range_ι]
  rfl

end Langlands.AlgebraicGeometry.SmoothGenericMonomorphism
