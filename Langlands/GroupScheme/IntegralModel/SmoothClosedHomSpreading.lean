import Langlands.GroupScheme.IntegralModel.ArithmeticClosedHomSpreading
import Langlands.GroupScheme.Absolute.Borel

/-! # Simultaneous smooth models of a supplied closed homomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Global
open scoped NumberField

namespace Langlands.GroupScheme.IntegralModel

/-- Two actual smooth integral models and a closed extension of the supplied map. -/
structure SmoothClosedHomModels (R K : Type u) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G H : GroupScheme (Spec (CommRingCat.of K))} (f : G ⟶ H) where
  source : IntegralModel R K G
  target : IntegralModel R K H
  sourceSmooth : Smooth source.group.X.hom
  targetSmooth : Smooth target.group.X.hom
  hom : source.Hom target f
  closed : IsClosedImmersion hom.hom.hom.hom.left

attribute [instance] SmoothClosedHomModels.sourceSmooth SmoothClosedHomModels.targetSmooth

namespace ArithmeticSpreading

variable (F : Type u) [Field F] [NumberField F]

/-- Two supplied smooth affine groups and their supplied closed homomorphism
have simultaneous smooth models with a closed extending homomorphism. -/
theorem exists_smooth_closedHomModels
    {G H : GroupScheme (Spec (CommRingCat.of F))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (f : G ⟶ H) [IsClosedImmersion f.hom.hom.left] :
    ∃ S : Finset (FinitePlace F),
      Nonempty (SmoothClosedHomModels ((S : Set (FinitePlace F)).integer F) F f) := by
  classical
  obtain ⟨S₁, M₁, hM₁⟩ := exists_smoothIntegralModel F G
  obtain ⟨S₂, N₂, hN₂⟩ := exists_smoothIntegralModel F H
  let : Smooth M₁.group.X.hom := hM₁
  let : Smooth N₂.group.X.hom := hN₂
  let S := S₁ ∪ S₂
  let M := enlargeModel F M₁ (show S₁ ⊆ S from Finset.subset_union_left)
  let N := enlargeModel F N₂ (show S₂ ⊆ S from Finset.subset_union_right)
  let : Smooth M.group.X.hom := smooth_enlargeModel F M₁ _
  let : Smooth N.group.X.hom := smooth_enlargeModel F N₂ _
  let D := enlargedHomData F S M N f
  let M' := enlargeModel F M D.contains
  let N' := enlargeModel F N D.contains
  let : Smooth M'.group.X.hom := smooth_enlargeModel F M D.contains
  let : Smooth N'.group.X.hom := smooth_enlargeModel F N D.contains
  let E := enlargedClosedHomData F D.hom
  exact ⟨E.places, ⟨{
    source := enlargeModel F M' E.contains
    target := enlargeModel F N' E.contains
    sourceSmooth := smooth_enlargeModel F M' E.contains
    targetSmooth := smooth_enlargeModel F N' E.contains
    hom := enlargeHom F D.hom E.contains
    closed := E.closed }⟩⟩

/-- A finite arithmetic base and simultaneous actual smooth closed models. -/
structure SmoothClosedHomModelData
    {G H : GroupScheme (Spec (CommRingCat.of F))} (f : G ⟶ H) where
  places : Finset (FinitePlace F)
  models : SmoothClosedHomModels ((places : Set (FinitePlace F)).integer F) F f

/-- Choose simultaneous smooth models and an actual closed extension of the
specified closed generic homomorphism. -/
def smoothClosedHomModelData
    {G H : GroupScheme (Spec (CommRingCat.of F))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (f : G ⟶ H) [IsClosedImmersion f.hom.hom.left] :
    SmoothClosedHomModelData F f :=
  let h := exists_smooth_closedHomModels F f
  { places := Classical.choose h
    models := Classical.choice (Classical.choose_spec h) }

/-- The smooth closed model part of simultaneous parabolic spreading, with
no conclusion yet about the special fibres. -/
def smoothClosedHomModelData_of_parabolic
    {G P : GroupScheme (Spec (CommRingCat.of F))}
    (hG : IsConnectedReductive G) (p : P ⟶ G) (hp : IsParabolicSubgroup p) :
    SmoothClosedHomModelData F p := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth P.X.hom := hp.smooth
  let : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  let : IsAffineHom P.X.hom := by
    rw [← p.hom.hom.w]
    infer_instance
  exact smoothClosedHomModelData F p

end ArithmeticSpreading
end Langlands.GroupScheme.IntegralModel
