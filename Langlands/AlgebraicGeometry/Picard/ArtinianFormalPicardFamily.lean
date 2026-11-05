import Langlands.AlgebraicGeometry.Picard.ArtinianAdicEvaluation
import Langlands.AlgebraicGeometry.Picard.ArtinianChartVersality
import Langlands.AlgebraicGeometry.Picard.InfinitesimalGluing

/-! # Actual pointed Picard objects evaluated from formal line bundles -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Deformation FormalLineBundle
open PicardGroupoid

namespace ArtinianFormalPicardFamily

private lemma quotient_lift_postcomp {R S T : Type u}
    [CommRing R] [CommRing S] [CommRing T] (I : Ideal R)
    (α : R →+* S) (β : S →+* T)
    (hα : I ≤ RingHom.ker α) (hβα : I ≤ RingHom.ker (β.comp α)) :
    β.comp (Ideal.Quotient.lift I α (fun _ hr ↦ RingHom.mem_ker.mp (hα hr))) =
      Ideal.Quotient.lift I (β.comp α) (fun _ hr ↦ RingHom.mem_ker.mp (hβα hr)) := by
  apply Ideal.Quotient.ringHom_ext
  rw [RingHom.comp_assoc, Ideal.Quotient.lift_comp_mk,
    Ideal.Quotient.lift_comp_mk]

variable {k K R : Type u} [CommRing k] [Field K] [Algebra k K]
  [CommRing R] [Algebra k R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- The actual total space over the source affine algebra. -/
abbrev totalMap :=
  (relativeProjection f).app (affineBase k R)

variable {A B : ArtinianTest k K} (α : R →ₐ[k] A.algebra)

/-- An actual comparison map from the Picard relative space to the
oppositely ordered ordinary base change used for adic evaluation. -/
def testSpaceMap :
    (relativeSpace f).obj (ArtinianTest.base A) ⟶
      ArtinianAdicEvaluation.testSpace α (totalMap (R := R) f) :=
  pullback.lift ((relativeSpace f).map (affineBaseMap α))
    ((relativeProjection f).app (ArtinianTest.base A))
    ((relativeProjection f).naturality (affineBaseMap α))

@[reassoc (attr := simp)]
lemma testSpaceMap_fst :
    testSpaceMap f α ≫ pullback.fst _ _ =
      (relativeSpace f).map (affineBaseMap α) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma testSpaceMap_snd :
    testSpaceMap f α ≫ pullback.snd _ _ =
      (relativeProjection f).app (ArtinianTest.base A) :=
  pullback.lift_snd _ _ _

/-- The actual finite-stage map on the original Picard relative space. -/
def finiteMap (n : ℕ) (h : ArtinianAdicEvaluation.IsBound I α n) :
    (relativeSpace f).obj (ArtinianTest.base A) ⟶
      adicSpace (totalMap (R := R) f) I n :=
  testSpaceMap f α ≫ ArtinianAdicEvaluation.spaceMap I α (totalMap f) n h

@[reassoc (attr := simp)]
lemma finiteMap_projection (n : ℕ) (h : ArtinianAdicEvaluation.IsBound I α n) :
    finiteMap I f α n h ≫ adicProjection (totalMap f) I n =
      (relativeSpace f).map (affineBaseMap α) := by
  rw [finiteMap, Category.assoc, ArtinianAdicEvaluation.spaceMap_projection,
    testSpaceMap_fst]

@[reassoc (attr := simp)]
lemma finiteMap_base (n : ℕ) (h : ArtinianAdicEvaluation.IsBound I α n) :
    finiteMap I f α n h ≫ pullback.snd (totalMap f) (adicBaseProjection I n) =
      (relativeProjection f).app (ArtinianTest.base A) ≫
        ArtinianAdicEvaluation.baseMap I α n h := by
  simp only [finiteMap, ArtinianAdicEvaluation.spaceMap, Category.assoc,
    pullback.lift_snd, testSpaceMap_snd_assoc]

@[reassoc (attr := simp)]
lemma finiteMap_transition (n : ℕ) (h : ArtinianAdicEvaluation.IsBound I α n) :
    finiteMap I f α n h ≫ adicTransition (totalMap f) I n =
      finiteMap I f α (n + 1)
        (ArtinianAdicEvaluation.IsBound.mono I α h (Nat.le_succ n)) := by
  rw [finiteMap, Category.assoc, ArtinianAdicEvaluation.spaceMap_transition]
  rfl

/-- The same finite bound is valid after an actual map of Artinian tests. -/
lemma bound_postcomp (q : A ⟶ B) (n : ℕ)
    (h : ArtinianAdicEvaluation.IsBound I α n) :
    ArtinianAdicEvaluation.IsBound I ((ArtinianTest.toAlgHom q).comp α) n := by
  intro r hr
  change ArtinianTest.toAlgHom q (α r) = 0
  have hr' : α r = 0 := RingHom.mem_ker.mp (h hr)
  rw [hr', map_zero]

/-- Quotient evaluation retains actual postcomposition of algebra maps. -/
lemma factor_postcomp (q : A ⟶ B) (n : ℕ)
    (h : ArtinianAdicEvaluation.IsBound I α n) :
    (ArtinianTest.toAlgHom q).toRingHom.comp
      (ArtinianAdicEvaluation.factor I α n h).toRingHom =
      (ArtinianAdicEvaluation.factor I ((ArtinianTest.toAlgHom q).comp α)
        n (bound_postcomp I α q n h)).toRingHom :=
  quotient_lift_postcomp _ _ _ h (bound_postcomp I α q n h)

@[reassoc]
lemma baseMap_postcomp (q : A ⟶ B) (n : ℕ)
    (h : ArtinianAdicEvaluation.IsBound I α n) :
    (ArtinianTest.baseMap q).left ≫ ArtinianAdicEvaluation.baseMap I α n h =
      ArtinianAdicEvaluation.baseMap I ((ArtinianTest.toAlgHom q).comp α)
        n (bound_postcomp I α q n h) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, factor_postcomp]

/-- The finite-stage maps commute with the actual relative test arrow. -/
@[reassoc]
lemma finiteMap_postcomp (q : A ⟶ B) (n : ℕ)
    (h : ArtinianAdicEvaluation.IsBound I α n) :
    (relativeSpace f).map (ArtinianTest.baseMap q) ≫ finiteMap I f α n h =
      finiteMap I f ((ArtinianTest.toAlgHom q).comp α)
        n (bound_postcomp I α q n h) := by
  apply pullback.hom_ext
  · change _ ≫ adicProjection (totalMap f) I n =
      _ ≫ adicProjection (totalMap f) I n
    rw [Category.assoc, finiteMap_projection, finiteMap_projection]
    change (relativeSpace f).map (affineBaseMap (ArtinianTest.toAlgHom q)) ≫
      (relativeSpace f).map (affineBaseMap α) = _
    rw [← Functor.map_comp, ← affineBaseMap_comp]
  · rw [Category.assoc, finiteMap_base, finiteMap_base, ← Category.assoc,
      (relativeProjection f).naturality (ArtinianTest.baseMap q), Category.assoc]
    simp only [Over.forget_map]
    rw [baseMap_postcomp]

variable (F : FormalLineBundleSystem (totalMap (R := R) f) I)

/-- Actual line-bundle evaluation on the Picard relative space. -/
def evaluate (n : ℕ) (h : ArtinianAdicEvaluation.IsBound I α n) :
    LineBundle ((relativeSpace f).obj (ArtinianTest.base A)) :=
  (LineBundle.pullback (finiteMap I f α n h)).obj (F.obj n)

/-- The direct evaluation is compared with the existing ordinary evaluation
by the actual pullback-composition isomorphism. -/
def evaluationIso (n : ℕ) (h : ArtinianAdicEvaluation.IsBound I α n) :
    (LineBundle.pullback (testSpaceMap f α)).obj
      (ArtinianAdicEvaluation.evaluate I α (totalMap f) F n h) ≅
        evaluate I f α F n h :=
  (LineBundle.pullbackComp (testSpaceMap f α)
    (ArtinianAdicEvaluation.spaceMap I α (totalMap f) n h)).app (F.obj n)

/-- Later evaluation uses the original formal-system transitions. -/
def laterIso {n m : ℕ} (h : ArtinianAdicEvaluation.IsBound I α n) (hnm : n ≤ m) :
    evaluate I f α F m (ArtinianAdicEvaluation.IsBound.mono I α h hnm) ≅
      evaluate I f α F n h :=
  (evaluationIso I f α F m _).symm ≪≫
    (LineBundle.pullback (testSpaceMap f α)).mapIso
      (ArtinianAdicEvaluation.laterIso I α (totalMap f) F h hnm) ≪≫
    evaluationIso I f α F n h

/-- Any two valid finite bounds give isomorphic actual evaluations. -/
def boundsIso (n m : ℕ) (hn : ArtinianAdicEvaluation.IsBound I α n)
    (hm : ArtinianAdicEvaluation.IsBound I α m) :
    evaluate I f α F n hn ≅ evaluate I f α F m hm :=
  (laterIso I f α F hn (Nat.le_max_left n m)).symm ≪≫
    laterIso I f α F hm (Nat.le_max_right n m)

/-- Actual evaluation commutes with every Artinian test arrow at a fixed bound. -/
def postcompIso (q : A ⟶ B) (n : ℕ)
    (h : ArtinianAdicEvaluation.IsBound I α n) :
    (LineBundle.pullback ((relativeSpace f).map (ArtinianTest.baseMap q))).obj
      (evaluate I f α F n h) ≅
        evaluate I f ((ArtinianTest.toAlgHom q).comp α) F n
          (bound_postcomp I α q n h) :=
  (LineBundle.pullbackComp ((relativeSpace f).map (ArtinianTest.baseMap q))
    (finiteMap I f α n h)).app (F.obj n) ≪≫
      ObjectProperty.isoMk _
        ((Scheme.Modules.pullbackCongr (finiteMap_postcomp I f α q n h)).app
          (F.obj n).obj)

/-- A supplied compatible algebraization realizes the actual evaluation
by ordinary relative pullback. -/
def algebraizationIso (L : LineBundle ((relativeSpace f).obj (affineBase k R)))
    (e : FormalLineBundleSystem.Comparison
      (FormalLineBundleSystem.ofLineBundle (totalMap f) I L) F)
    (n : ℕ) (h : ArtinianAdicEvaluation.IsBound I α n) :
    (LineBundle.pullback ((relativeSpace f).map (affineBaseMap α))).obj L ≅
      evaluate I f α F n h :=
  (ObjectProperty.isoMk _
    ((Scheme.Modules.pullbackCongr (finiteMap_projection I f α n h)).app L.obj)).symm ≪≫
    ((LineBundle.pullbackComp (finiteMap I f α n h)
      (adicProjection (totalMap f) I n)).app L).symm ≪≫
    (LineBundle.pullback (finiteMap I f α n h)).mapIso (e.component n)

variable (ε : R →ₐ[k] K) (hI : I ≤ RingHom.ker ε.toRingHom)

include hI in
/-- The residue augmentation already factors through the zeroth adic stage. -/
lemma residueBound :
    ArtinianAdicEvaluation.IsBound I (A := ArtinianTest.residue k K) ε 0 := by
  simpa only [ArtinianAdicEvaluation.IsBound, zero_add, pow_one] using hI

/-- The actual residue bundle of the supplied formal family. -/
def residueBundle :
    LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k K)) :=
  evaluate I f (A := ArtinianTest.residue k K) ε F 0 (residueBound I ε hI)

/-- The finite evaluation carries an actual residue identification obtained
from the original formal transitions and the actual augmentation arrow. -/
def residueIso (hα : A.augmentation.comp α = ε)
    (n : ℕ) (h : ArtinianAdicEvaluation.IsBound I α n) :
    residueBundle I f F ε hI ≅
      (LineBundle.pullback ((relativeSpace f).map (ArtinianTest.reduction A))).obj
        (evaluate I f α F n h) := by
  subst ε
  exact boundsIso I f (A := ArtinianTest.residue k K) (A.augmentation.comp α) F
      0 n (residueBound I (A.augmentation.comp α) hI)
        (bound_postcomp I α (ArtinianChartVersality.augmentationArrow A) n h) ≪≫
    (postcompIso I f α F (ArtinianChartVersality.augmentationArrow A) n h).symm

/-- Evaluate as an actual pointed deformation, retaining a prescribed
identification of the original residue bundle. -/
def pointed (hα : A.augmentation.comp α = ε)
    (M : LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k K)))
    (ρ : M ≅ residueBundle I f F ε hI)
    (n : ℕ) (h : ArtinianAdicEvaluation.IsBound I α n) :
    ArtinianTestDeformations.Deformations f M A :=
  ArtinianTestDeformations.mk f M A (evaluate I f α F n h)
    (ρ ≪≫ residueIso I f α F ε hI hα n h)

/-- The pointed object retains the original actual evaluated bundle. -/
lemma pointed_bundle (hα : A.augmentation.comp α = ε)
    (M : LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k K)))
    (ρ : M ≅ residueBundle I f F ε hI)
    (n : ℕ) (h : ArtinianAdicEvaluation.IsBound I α n) :
    (pointed I f α F ε hI hα M ρ n h).right.of = evaluate I f α F n h := rfl

/-- Its specified reduction is exactly the supplied identification followed
by the constructed residue comparison. -/
lemma pointed_reductionIso (hα : A.augmentation.comp α = ε)
    (M : LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k K)))
    (ρ : M ≅ residueBundle I f F ε hI)
    (n : ℕ) (h : ArtinianAdicEvaluation.IsBound I α n) :
    ArtinianTestDeformations.reductionIso f M (pointed I f α F ε hI hα M ρ n h) =
      ρ ≪≫ residueIso I f α F ε hI hα n h := rfl

end ArtinianFormalPicardFamily

end Langlands.AlgebraicGeometry.Picard
