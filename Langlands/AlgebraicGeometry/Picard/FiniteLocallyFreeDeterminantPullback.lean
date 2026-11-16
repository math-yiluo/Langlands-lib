import Langlands.AlgebraicGeometry.Picard.FiniteLocallyFreeDeterminant

/-! # Coherent pullback of actual finite locally free determinants -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

namespace FiniteLocalFrames

variable {X Y Z : Scheme.{u}} {M : X.Modules}

/-- The frame determinant comparison respects identity pullback. -/
lemma pullbackIso_identity (a : FiniteLocalFrames M) :
    a.pullbackIso (𝟙 X) ≪≫
        (a.pullback (𝟙 X)).isoMap a ((Scheme.Modules.pullbackId X).app M) =
      (LineBundle.pullbackId X).app a.lineBundle :=
  VariableDeterminantFrames.lineBundlePullbackIso_identity a.frame a.covers

set_option maxHeartbeats 800000 in
/-- The frame determinant comparison respects successive pullback. -/
lemma pullbackIso_composition (a : FiniteLocalFrames M)
    (f : Z ⟶ Y) (g : Y ⟶ X) :
    (LineBundle.pullback f).mapIso (a.pullbackIso g) ≪≫
        (a.pullback g).pullbackIso f ≪≫
        ((a.pullback g).pullback f).isoMap (a.pullback (f ≫ g))
          ((Scheme.Modules.pullbackComp f g).app M) =
      (LineBundle.pullbackComp f g).app a.lineBundle ≪≫ a.pullbackIso (f ≫ g) :=
  VariableDeterminantFrames.lineBundlePullbackIso_composition a.frame f g a.covers

/-- Frame changes commute with pullback of the actual determinant lines. -/
lemma pullbackIso_changeIso (a b : FiniteLocalFrames M) (f : Y ⟶ X) :
    (LineBundle.pullback f).mapIso (a.changeIso b) ≪≫ b.pullbackIso f =
      a.pullbackIso f ≪≫ (a.pullback f).changeIso (b.pullback f) := by
  simpa only [changeIso, Functor.mapIso_refl] using
    a.pullbackIso_naturality b f (Iso.refl M)

end FiniteLocalFrames

/-- Pullback of the chosen actual determinant line, with the frame choices
compared on the target scheme. -/
def finiteLocallyFreeDeterminantPullbackIso
    {X Y : Scheme.{u}} {M : X.Modules} (hM : HasFiniteLocalBasis M) (f : Y ⟶ X) :
    (LineBundle.pullback f).obj (finiteLocallyFreeDeterminant hM) ≅
      finiteLocallyFreeDeterminant (hM.pullback f) :=
  (FiniteLocalFrames.choose hM).pullbackIso f ≪≫
    ((FiniteLocalFrames.choose hM).pullback f).changeIso
      (FiniteLocalFrames.choose (hM.pullback f))

/-- The chosen determinant pullback comparison is natural in every actual
module-sheaf isomorphism. -/
lemma finiteLocallyFreeDeterminantPullbackIso_naturality
    {X Y : Scheme.{u}} {M N : X.Modules}
    (hM : HasFiniteLocalBasis M) (hN : HasFiniteLocalBasis N)
    (f : Y ⟶ X) (φ : M ≅ N) :
    (LineBundle.pullback f).mapIso (finiteLocallyFreeDeterminantIso hM hN φ) ≪≫
        finiteLocallyFreeDeterminantPullbackIso hN f =
      finiteLocallyFreeDeterminantPullbackIso hM f ≪≫
        finiteLocallyFreeDeterminantIso (hM.pullback f) (hN.pullback f)
          ((Scheme.Modules.pullback f).mapIso φ) := by
  dsimp only [finiteLocallyFreeDeterminantPullbackIso, finiteLocallyFreeDeterminantIso,
    finiteLocallyFreeDeterminant]
  rw [← Iso.trans_assoc, FiniteLocalFrames.pullbackIso_naturality, Iso.trans_assoc,
    FiniteLocalFrames.isoMap_changeIso, Iso.trans_assoc,
    FiniteLocalFrames.changeIso_isoMap]

/-- The chosen determinant comparison agrees with canonical identity pullback. -/
lemma finiteLocallyFreeDeterminantPullbackIso_identity
    {X : Scheme.{u}} {M : X.Modules} (hM : HasFiniteLocalBasis M) :
    finiteLocallyFreeDeterminantPullbackIso hM (𝟙 X) ≪≫
        finiteLocallyFreeDeterminantIso (hM.pullback (𝟙 X)) hM
          ((Scheme.Modules.pullbackId X).app M) =
      (LineBundle.pullbackId X).app (finiteLocallyFreeDeterminant hM) := by
  dsimp only [finiteLocallyFreeDeterminantPullbackIso, finiteLocallyFreeDeterminantIso]
  rw [Iso.trans_assoc, FiniteLocalFrames.changeIso_isoMap]
  exact (FiniteLocalFrames.choose hM).pullbackIso_identity

/-- Pulling back the chosen determinant in two steps agrees with one-step
pullback through the canonical module and line-bundle comparisons. -/
lemma finiteLocallyFreeDeterminantPullbackIso_composition
    {X Y Z : Scheme.{u}} {M : X.Modules} (hM : HasFiniteLocalBasis M)
    (f : Z ⟶ Y) (g : Y ⟶ X) :
    (LineBundle.pullback f).mapIso (finiteLocallyFreeDeterminantPullbackIso hM g) ≪≫
        finiteLocallyFreeDeterminantPullbackIso (hM.pullback g) f ≪≫
        finiteLocallyFreeDeterminantIso ((hM.pullback g).pullback f)
          (hM.pullback (f ≫ g)) ((Scheme.Modules.pullbackComp f g).app M) =
      (LineBundle.pullbackComp f g).app (finiteLocallyFreeDeterminant hM) ≪≫
        finiteLocallyFreeDeterminantPullbackIso hM (f ≫ g) := by
  dsimp only [finiteLocallyFreeDeterminantPullbackIso, finiteLocallyFreeDeterminantIso,
    finiteLocallyFreeDeterminant]
  rw [Functor.mapIso_trans]
  simp only [Iso.trans_assoc, FiniteLocalFrames.changeIso_isoMap]
  rw [← Iso.trans_assoc
    ((LineBundle.pullback f).mapIso
      (((FiniteLocalFrames.choose hM).pullback g).changeIso
        (FiniteLocalFrames.choose (hM.pullback g)))),
    FiniteLocalFrames.pullbackIso_changeIso]
  simp only [Iso.trans_assoc, FiniteLocalFrames.changeIso_isoMap]
  rw [← FiniteLocalFrames.isoMap_changeIso
    (((FiniteLocalFrames.choose hM).pullback g).pullback f)
    ((FiniteLocalFrames.choose hM).pullback (f ≫ g))
    (FiniteLocalFrames.choose (hM.pullback (f ≫ g)))
    ((Scheme.Modules.pullbackComp f g).app M)]
  simp only [← Iso.trans_assoc]
  simpa only [Iso.trans_assoc] using congrArg
    (fun t => t ≪≫ ((FiniteLocalFrames.choose hM).pullback (f ≫ g)).changeIso
      (FiniteLocalFrames.choose (hM.pullback (f ≫ g))))
    ((FiniteLocalFrames.choose hM).pullbackIso_composition f g)

end Langlands.AlgebraicGeometry.Picard
