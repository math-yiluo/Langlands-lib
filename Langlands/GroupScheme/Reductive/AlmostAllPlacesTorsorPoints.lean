import Langlands.GroupScheme.IntegralTorsorPoint
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.AlgebraicGeometry.GeometricallyConnectedDescent
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent
import Langlands.Global.NumberFieldAlmostAllLocalPoints

/-! # Local points of actual torsors at almost all finite places -/

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.AlmostAllPlacesTorsorPoints

/-- Separatedness descends from the trivialization supplied by the torsor shear. -/
theorem separated_of_isIso_leftSMul {S : Scheme.{u}} (G : GroupScheme S)
    [IsSeparated G.X.hom] (X : Over S) [ModObj G.X X] (hfl : Flat X.hom)
    (hs : Surjective X.hom) (hqc : QuasiCompact X.hom)
    (hiso : IsIso (ModObj.leftSMul G.X X)) : IsSeparated X.hom := by
  have h1 : (ModObj.leftSMul G.X X).left ≫ pullback.snd X.hom X.hom =
      pullback.snd G.X.hom X.hom :=
    congrArg CommaMorphism.left (ModObj.leftSMul_snd (M := G.X) (X := X))
  have : IsIso (ModObj.leftSMul G.X X).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (ModObj.leftSMul G.X X)))
  have h2 : IsSeparated (pullback.snd X.hom X.hom) := by
    rw [← IsIso.inv_hom_id_assoc (ModObj.leftSMul G.X X).left
      (pullback.snd X.hom X.hom), h1]
    infer_instance
  exact MorphismProperty.of_pullback_snd_of_descendsAlong (P := @IsSeparated)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := X.hom) (g := X.hom)
    ⟨⟨hs, hfl⟩, hqc⟩ h2

/-- A torsor under a group with geometrically connected fibres has
geometrically connected fibres. -/
theorem geometricallyConnected_of_isIso_leftSMul {S : Scheme.{u}} (G : GroupScheme S)
    [GeometricallyConnected G.X.hom] (X : Over S) [ModObj G.X X]
    (hs : Surjective X.hom) (hiso : IsIso (ModObj.leftSMul G.X X)) :
    GeometricallyConnected X.hom := by
  have : MorphismProperty.RespectsIso @GeometricallyConnected.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have h1 : (ModObj.leftSMul G.X X).left ≫ pullback.snd X.hom X.hom =
      pullback.snd G.X.hom X.hom :=
    congrArg CommaMorphism.left (ModObj.leftSMul_snd (M := G.X) (X := X))
  have : IsIso (ModObj.leftSMul G.X X).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (ModObj.leftSMul G.X X)))
  have : GeometricallyConnected (pullback.snd X.hom X.hom) := by
    rw [← IsIso.inv_hom_id_assoc (ModObj.leftSMul G.X X).left
      (pullback.snd X.hom X.hom), h1]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (@GeometricallyConnected : MorphismProperty Scheme.{u}) _ _).mpr inferInstance
  let : Surjective X.hom := hs
  exact Langlands.AlgebraicGeometry.geometricallyConnected_of_surjective_baseChange
    X.hom X.hom

/-- Every actual fpqc torsor under a connected reductive number-field
group has points over almost all finite completions. -/
theorem eventually_nonempty_ringPoint_of_torsor
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (X : Over (Spec (CommRingCat.of F))) [ModObj G.X X]
    (hfl : Flat X.hom) (hs : Surjective X.hom) (hqc : QuasiCompact X.hom)
    (hiso : IsIso (ModObj.leftSMul G.X X)) :
    ∀ᶠ v in Filter.cofinite (α := Langlands.Global.FinitePlace F),
      Nonempty (RingPoint F X (Langlands.Global.FiniteCompletion F v)) := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : GeometricallyConnected G.X.hom := G.geometricallyConnected_of_connected
  let : Smooth X.hom :=
    IntegralTorsorPoint.smooth_of_isIso_leftSMul G X hfl hs hqc hiso
  let : QuasiCompact X.hom := hqc
  let : IsSeparated X.hom := separated_of_isIso_leftSMul G X hfl hs hqc hiso
  let : GeometricallyConnected X.hom :=
    geometricallyConnected_of_isIso_leftSMul G X hs hiso
  exact Langlands.Global.eventually_nonempty_ringPoint_of_smooth_geometricallyConnected F X

/-- Choose a finite exceptional set and an actual point of the given torsor
over every finite completion outside that set. -/
def torsorCompletionPoints
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (X : Over (Spec (CommRingCat.of F))) [ModObj G.X X]
    (hfl : Flat X.hom) (hs : Surjective X.hom) (hqc : QuasiCompact X.hom)
    (hiso : IsIso (ModObj.leftSMul G.X X)) :
    Σ S : Finset (Langlands.Global.FinitePlace F),
      (v : Langlands.Global.FinitePlace F) → v ∉ S →
        RingPoint F X (Langlands.Global.FiniteCompletion F v) := by
  classical
  let bad : Set (Langlands.Global.FinitePlace F) :=
    {v | ¬Nonempty (RingPoint F X (Langlands.Global.FiniteCompletion F v))}
  have hbad : bad.Finite := Filter.eventually_cofinite.mp
    (eventually_nonempty_ringPoint_of_torsor F G hG X hfl hs hqc hiso)
  refine ⟨hbad.toFinset, fun v hv => Classical.choice ?_⟩
  by_contra h
  exact hv (hbad.mem_toFinset.mpr h)

end Langlands.GroupScheme.AlmostAllPlacesTorsorPoints
