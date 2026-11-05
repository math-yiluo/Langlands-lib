import Langlands.AlgebraicGeometry.Deformation.ArtinianTests
import Langlands.AlgebraicGeometry.Picard.FormalLineBundleSystem
import Mathlib.RingTheory.Ideal.Maps

/-! # Evaluation of actual formal line bundles on Artinian tests -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Deformation FormalLineBundle

namespace ArtinianAdicEvaluation

private lemma quotient_lift_comp_factor {R S : Type u} [CommRing R] [CommRing S]
    {I J : Ideal R} (hJI : J ≤ I) (β : R →+* S)
    (hI : I ≤ RingHom.ker β) (hJ : J ≤ RingHom.ker β) :
    (Ideal.Quotient.lift I β (fun _ hr ↦ RingHom.mem_ker.mp (hI hr))).comp
      (Ideal.Quotient.factor hJI) =
        Ideal.Quotient.lift J β (fun _ hr ↦ RingHom.mem_ker.mp (hJ hr)) := by
  apply Ideal.Quotient.ringHom_ext
  rw [RingHom.comp_assoc, Ideal.Quotient.factor_comp_mk,
    Ideal.Quotient.lift_comp_mk, Ideal.Quotient.lift_comp_mk]

variable {k K R : Type u} [CommRing k] [Field K] [Algebra k K]
  [CommRing R] [Algebra k R] (I : Ideal R)
  {A : ArtinianTest k K} (α : R →ₐ[k] A.algebra)

/-- A finite adic quotient through which the actual algebra map factors. -/
def IsBound (n : ℕ) : Prop :=
  I ^ (n + 1) ≤ RingHom.ker α.toRingHom

/-- A bound remains valid at every later adic stage. -/
lemma IsBound.mono {n m : ℕ} (h : IsBound I α n) (hnm : n ≤ m) :
    IsBound I α m :=
  (Ideal.pow_le_pow_right (Nat.add_le_add_right hnm 1)).trans h

/-- Every augmentation-compatible map to an Artinian test has a finite bound.
The source ideal need only vanish under the specified residue augmentation. -/
theorem exists_bound (ε : R →ₐ[k] K) (hI : I ≤ RingHom.ker ε.toRingHom)
    (hα : A.augmentation.comp α = ε) : ∃ n, IsBound I α n := by
  have hmap : I.map α.toRingHom ≤ IsLocalRing.maximalIdeal A.algebra := by
    rw [← ArtinianTest.ker_augmentation A, Ideal.map_le_iff_le_comap]
    intro r hr
    change A.augmentation (α r) = 0
    have hε : ε r = 0 := RingHom.mem_ker.mp (hI hr)
    exact (congrArg (fun e : R →ₐ[k] K ↦ e r) hα).trans hε
  obtain ⟨n, hn⟩ := A.maximalIdeal_isNilpotent
  refine ⟨n, ?_⟩
  have hpow : (I ^ (n + 1)).map α.toRingHom ≤ ⊥ := by
    rw [Ideal.map_pow]
    calc
      (I.map α.toRingHom) ^ (n + 1) ≤
          (IsLocalRing.maximalIdeal A.algebra) ^ (n + 1) :=
        pow_le_pow_left' hmap _
      _ = ⊥ := by rw [pow_succ, hn, zero_mul]; rfl
  exact Ideal.map_le_iff_le_comap.mp hpow

/-- The actual factor map through a bounded adic quotient, retaining scalars. -/
def factor (n : ℕ) (h : IsBound I α n) :
    R ⧸ I ^ (n + 1) →ₐ[k] A.algebra :=
  Ideal.Quotient.liftₐ _ α (fun _ hr ↦ RingHom.mem_ker.mp (h hr))

/-- The quotient factor is a factorization of the original actual map. -/
lemma factor_comp_mk (n : ℕ) (h : IsBound I α n) :
    (factor I α n h).comp (Ideal.Quotient.mkₐ k (I ^ (n + 1))) = α :=
  Ideal.Quotient.liftₐ_comp _ _ _

/-- The factor maps agree under the actual consecutive quotient map. -/
lemma factor_transition (n : ℕ) (h : IsBound I α n) :
    (factor I α n h).toRingHom.comp
      (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.add_le_add_right (Nat.le_succ n) 1))) =
      (factor I α (n + 1) (IsBound.mono I α h (Nat.le_succ n))).toRingHom := by
  exact quotient_lift_comp_factor _ α.toRingHom h
    (IsBound.mono I α h (Nat.le_succ n))

/-- The induced actual map from the Artinian test scheme to the adic base. -/
def baseMap (n : ℕ) (h : IsBound I α n) :
    (ArtinianTest.base A).left ⟶ adicBase I n :=
  Spec.map (CommRingCat.ofHom (factor I α n h).toRingHom)

@[reassoc (attr := simp)]
lemma baseMap_projection (n : ℕ) (h : IsBound I α n) :
    baseMap I α n h ≫ adicBaseProjection I n =
      Spec.map (CommRingCat.ofHom α.toRingHom) := by
  dsimp only [baseMap, adicBaseProjection]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

@[reassoc (attr := simp)]
lemma baseMap_transition (n : ℕ) (h : IsBound I α n) :
    baseMap I α n h ≫ adicBaseTransition I n =
      baseMap I α (n + 1) (IsBound.mono I α h (Nat.le_succ n)) := by
  dsimp only [baseMap, adicBaseTransition]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, factor_transition]

variable {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))

/-- The actual base change of the original scheme to the Artinian algebra. -/
abbrev testSpace :=
  pullback f (Spec.map (CommRingCat.ofHom α.toRingHom))

/-- The finite quotient factor induces the actual map of total spaces. -/
def spaceMap (n : ℕ) (h : IsBound I α n) :
    testSpace α f ⟶ adicSpace f I n :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ baseMap I α n h) (by
      rw [Category.assoc, baseMap_projection]
      exact pullback.condition)

@[reassoc (attr := simp)]
lemma spaceMap_projection (n : ℕ) (h : IsBound I α n) :
    spaceMap I α f n h ≫ adicProjection f I n = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma spaceMap_transition (n : ℕ) (h : IsBound I α n) :
    spaceMap I α f n h ≫ adicTransition f I n =
      spaceMap I α f (n + 1) (IsBound.mono I α h (Nat.le_succ n)) := by
  apply pullback.hom_ext
  · change (spaceMap I α f n h ≫ adicTransition f I n) ≫
      adicProjection f I (n + 1) =
        spaceMap I α f (n + 1) _ ≫ adicProjection f I (n + 1)
    rw [Category.assoc, adicTransition_projection, spaceMap_projection,
      spaceMap_projection]
  · simp only [spaceMap, adicTransition, pullback.lift_snd,
      pullback.lift_snd_assoc, Category.assoc, baseMap_transition]

/-- Evaluation is ordinary pullback of the actual bundle at a finite stage. -/
def evaluate (F : FormalLineBundleSystem f I) (n : ℕ) (h : IsBound I α n) :
    LineBundle (testSpace α f) :=
  (LineBundle.pullback (spaceMap I α f n h)).obj (F.obj n)

/-- Consecutive evaluations compare through the original specified transition. -/
def stepIso (F : FormalLineBundleSystem f I) (n : ℕ) (h : IsBound I α n) :
    evaluate I α f F (n + 1) (IsBound.mono I α h (Nat.le_succ n)) ≅
      evaluate I α f F n h :=
  (ObjectProperty.isoMk _
    ((Scheme.Modules.pullbackCongr (spaceMap_transition I α f n h)).app
      (F.obj (n + 1)).obj)).symm ≪≫
    ((LineBundle.pullbackComp (spaceMap I α f n h) (adicTransition f I n)).app
      (F.obj (n + 1))).symm ≪≫
    (LineBundle.pullback (spaceMap I α f n h)).mapIso (F.transition n)

/-- Iterating the specified transitions compares evaluation at any later bound. -/
def laterIso (F : FormalLineBundleSystem f I) {n m : ℕ}
    (h : IsBound I α n) (hnm : n ≤ m) :
    evaluate I α f F m (IsBound.mono I α h hnm) ≅
      evaluate I α f F n h :=
  Nat.leRec
    (motive := fun m hnm ↦
      evaluate I α f F m (IsBound.mono I α h hnm) ≅ evaluate I α f F n h)
    (Iso.refl _) (fun {m} hnm e ↦
      stepIso I α f F m (IsBound.mono I α h hnm) ≪≫ e) hnm

/-- Evaluation at two valid bounds is compared through their maximum. -/
def boundsIso (F : FormalLineBundleSystem f I) (n m : ℕ)
    (hn : IsBound I α n) (hm : IsBound I α m) :
    evaluate I α f F n hn ≅ evaluate I α f F m hm :=
  (laterIso I α f F hn (Nat.le_max_left n m)).symm ≪≫
    laterIso I α f F hm (Nat.le_max_right n m)

/-- A compatible comparison of formal systems induces an actual evaluation
isomorphism at each bounded stage. -/
def comparisonIso {F G : FormalLineBundleSystem f I}
    (e : FormalLineBundleSystem.Comparison F G) (n : ℕ) (h : IsBound I α n) :
    evaluate I α f F n h ≅ evaluate I α f G n h :=
  (LineBundle.pullback (spaceMap I α f n h)).mapIso (e.component n)

/-- A compatible algebraization gives the actual ordinary bundle realization
of every finite-stage evaluation. -/
def algebraizationIso (F : FormalLineBundleSystem f I) (L : LineBundle Y)
    (e : FormalLineBundleSystem.Comparison
      (FormalLineBundleSystem.ofLineBundle f I L) F)
    (n : ℕ) (h : IsBound I α n) :
    (LineBundle.pullback (pullback.fst f
      (Spec.map (CommRingCat.ofHom α.toRingHom)))).obj L ≅
        evaluate I α f F n h :=
  (ObjectProperty.isoMk _
    ((Scheme.Modules.pullbackCongr (spaceMap_projection I α f n h)).app L.obj)).symm ≪≫
    ((LineBundle.pullbackComp (spaceMap I α f n h) (adicProjection f I n)).app L).symm ≪≫
    (LineBundle.pullback (spaceMap I α f n h)).mapIso (e.component n)

end ArtinianAdicEvaluation

end Langlands.AlgebraicGeometry.Picard
