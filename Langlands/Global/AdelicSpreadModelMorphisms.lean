import Langlands.Global.AdelicFixedModelTransition
import Langlands.AlgebraicGeometry.SchemeLimitModelSpectrum
import Langlands.AlgebraicGeometry.SchemeLimitModelProof

/-! # Shared morphism descent for adelic arithmetic models -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology.SpreadModelMorphisms

@[reassoc (attr := simp)]
lemma pullbackSymmetry_hom_hom {C : Type*} [Category C]
    {A B D : C} (f : A ⟶ D) (g : B ⟶ D) [HasPullback f g] [HasPullback g f] :
    (pullbackSymmetry f g).hom ≫ (pullbackSymmetry g f).hom = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

open EtaleEquivalenceRelation.Action.TargetLimit AffineLimit
open SchemeLimitModel

variable {I : Type u} [Category.{u} I]
  (D : I ⥤ Scheme.{u}) {B : Scheme.{u}}
  (t : D ⟶ (Functor.const I).obj B)
  (c : Cone D) (p : c.pt ⟶ B)
  (hp : ∀ i, c.π.app i ≫ t.app i = p)
  (X : Over B)

/-- The actual cone projection, with the standard order of model pullbacks. -/
def modelConeLeg (i : I) :
    ((Over.pullback p).obj X).left ⟶ ((Over.pullback (t.app i)).obj X).left :=
  (pullbackSymmetry X.hom p).hom ≫
    (cone D t X.hom c p hp).π.app i ≫ (pullbackSymmetry (t.app i) X.hom).hom

@[reassoc (attr := simp)]
lemma modelConeLeg_fst (i : I) :
    modelConeLeg D t c p hp X i ≫ pullback.fst X.hom (t.app i) =
      pullback.fst X.hom p := by
  simp [modelConeLeg]

@[reassoc (attr := simp)]
lemma modelConeLeg_snd (i : I) :
    modelConeLeg D t c p hp X i ≫ pullback.snd X.hom (t.app i) =
      pullback.snd X.hom p ≫ c.π.app i := by
  simp [modelConeLeg]

variable [IsCofiltered I] [∀ i, IsAffine (D.obj i)]
  (hc : IsLimit c) (Z : Over B)

@[reassoc (attr := simp)]
lemma pullbackComp_snd {B T V : Scheme.{u}}
    (a : T ⟶ B) (b : V ⟶ T) (p : V ⟶ B) (w : b ≫ a = p)
    (X : Over B) :
    (modelPullbackCompIso a b p w X).hom.left ≫ pullback.snd X.hom p =
      pullback.snd ((Over.pullback a).obj X).hom b :=
  Over.w _

include hc in
/-- Descend a prescribed actual pullback morphism, retaining its cone square. -/
lemma exists_modelMorphism
    [QuasiCompact X.hom] [QuasiSeparated X.hom]
    [LocallyOfFinitePresentation Z.hom]
    (f : (Over.pullback p).obj X ⟶ (Over.pullback p).obj Z) :
    ∃ (i : I) (fi : (Over.pullback (t.app i)).obj X ⟶ (Over.pullback (t.app i)).obj Z),
      modelConeLeg D t c p hp X i ≫ fi.left =
        f.left ≫ modelConeLeg D t c p hp Z i := by
  let fs : LimitHom X.hom Z.hom p :=
    ⟨(pullbackSymmetry p X.hom).hom ≫ f.left ≫ (pullbackSymmetry Z.hom p).hom, by
      simpa using congrArg (fun q => (pullbackSymmetry p X.hom).hom ≫ q) (Over.w f)⟩
  obtain ⟨i, fi, h⟩ := exists_level_morphism D t X.hom Z.hom c hc p hp fs
  let fi' : (Over.pullback (t.app i)).obj X ⟶ (Over.pullback (t.app i)).obj Z :=
    Over.homMk ((pullbackSymmetry X.hom (t.app i)).hom ≫ fi.val ≫
      (pullbackSymmetry (t.app i) Z.hom).hom) (by
        simpa using congrArg (fun q => (pullbackSymmetry X.hom (t.app i)).hom ≫ q)
          fi.property)
  refine ⟨i, fi', ?_⟩
  have hs := toLimit_square D t X.hom Z.hom c p hp i fi
  rw [h] at hs
  have hs' := congrArg (fun q =>
    (pullbackSymmetry X.hom p).hom ≫ q ≫ (pullbackSymmetry (t.app i) Z.hom).hom) hs
  simpa [modelConeLeg, fi', fs, Category.assoc] using hs'

omit [IsCofiltered I] [∀ i, IsAffine (D.obj i)] in
lemma modelConeLeg_compIso (i : I) :
    (modelPullbackCompIso (t.app i) (c.π.app i) p (hp i) X).hom.left ≫
      modelConeLeg D t c p hp X i =
        pullback.fst ((Over.pullback (t.app i)).obj X).hom (c.π.app i) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, modelConeLeg_fst, modelPullbackCompIso_hom_left_fst]
  · rw [Category.assoc, modelConeLeg_snd, ← Category.assoc, pullbackComp_snd]
    exact pullback.condition.symm

omit [IsCofiltered I] [∀ i, IsAffine (D.obj i)] in
lemma modelConeLeg_naturality (i : I)
    (f : (Over.pullback p).obj X ⟶ (Over.pullback p).obj Z)
    (fi : (Over.pullback (t.app i)).obj X ⟶ (Over.pullback (t.app i)).obj Z)
    (h : modelConeLeg D t c p hp X i ≫ fi.left =
      f.left ≫ modelConeLeg D t c p hp Z i) :
    (Over.pullback (c.π.app i)).map fi ≫
        (modelPullbackCompIso (t.app i) (c.π.app i) p (hp i) Z).hom =
      (modelPullbackCompIso (t.app i) (c.π.app i) p (hp i) X).hom ≫ f := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hh := congrArg (fun q =>
      (modelPullbackCompIso (t.app i) (c.π.app i) p (hp i) X).hom.left ≫
        q ≫ pullback.fst Z.hom (t.app i)) h
    simp only [← Category.assoc, modelConeLeg_compIso] at hh
    simpa [Over.pullback_map_left, Category.assoc] using hh
  · have hf := Over.w f
    change f.left ≫ pullback.snd Z.hom p = pullback.snd X.hom p at hf
    simp [hf]

lemma pullbackComp_naturality {B T V : Scheme.{u}}
    (a : T ⟶ B) (b : V ⟶ T) (p : V ⟶ B) (w : b ≫ a = p)
    (X Z : Over B) (f : X ⟶ Z) :
    (Over.pullback b).map ((Over.pullback a).map f) ≫
        (modelPullbackCompIso a b p w Z).hom =
      (modelPullbackCompIso a b p w X).hom ≫ (Over.pullback p).map f := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext <;>
    simp [Over.pullback_map_left, modelPullbackCompIso_hom_left_fst_assoc]

end Langlands.AlgebraicGeometry.PointTopology.SpreadModelMorphisms
