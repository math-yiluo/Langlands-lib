import Langlands.AlgebraicGeometry.Deformation.ArtinianQuotients
import Mathlib.RingTheory.LocalRing.Pullback
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Pullbacks of actual augmented Artinian tests -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.AlgebraicGeometry.Deformation

/-- A local algebra with the same specified residue field retains finite length
when scalars are restricted along an augmentation-preserving local map. -/
lemma isFiniteLength_of_common_augmentation
    {R S K : Type u} [CommRing R] [CommRing S] [Field K]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsArtinianRing S]
    (εR : R →+* K) (εS : S →+* K)
    (hR : Function.Surjective εR) (hS : Function.Surjective εS)
    (h : εS.comp (algebraMap R S) = εR) : IsFiniteLength R S := by
  let : IsLocalHom εS := IsLocalHom.of_surjective εS hS
  have hres : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)) := by
    intro x
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨r, hr⟩ := hR (εS s)
    refine ⟨IsLocalRing.residue R r, ?_⟩
    rw [IsLocalRing.ResidueField.algebraMap_residue]
    apply (IsLocalRing.ResidueField.lift εS).injective
    change εS (algebraMap R S r) = εS s
    change (εS.comp (algebraMap R S)) r = εS s
    rw [h]
    exact hr
  have hlength : Module.length (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S) = 1 := by
    rw [Module.length_eq_of_surjective (M := IsLocalRing.ResidueField S) hres]
    exact Module.length_eq_one _ _
  apply Module.length_ne_top_iff.mp
  rw [IsLocalRing.length_restrictScalars R S S, hlength, mul_one]
  exact Module.length_ne_top

namespace ArtinianTest.Pullback

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
variable {A B C : ArtinianTest k K} (q : A ⟶ C) (r : B ⟶ C)

/-- The ordinary subalgebra of compatible pairs. -/
abbrev algebra := AlgHom.pullback (toAlgHom q) (toAlgHom r)

instance : IsLocalRing (algebra q r) := by
  let : IsLocalHom (toAlgHom r) :=
    ⟨fun x hx ↦ isUnit_of_map_unit (toAlgHom r).toRingHom x hx⟩
  exact AlgHom.isLocalRing_pullback (toAlgHom q) (toAlgHom r)

/-- The common specified augmentation, written using the second projection. -/
def augmentation : algebra q r →ₐ[k] K :=
  B.augmentation.comp (AlgHom.pullbackSnd (toAlgHom q) (toAlgHom r))

lemma augmentation_fst :
    A.augmentation.comp (AlgHom.pullbackFst (toAlgHom q) (toAlgHom r)) =
      augmentation q r := by
  ext x
  change A.augmentation x.val.1 = B.augmentation x.val.2
  rw [← augmentation_comp q, ← augmentation_comp r]
  exact congrArg C.augmentation x.property

lemma augmentation_surjective (hq : Function.Surjective (toAlgHom q)) :
    Function.Surjective (augmentation q r) :=
  B.augmentation_surjective.comp
    (AlgHom.surjective_pullbackSnd_of_surjective (toAlgHom q) (toAlgHom r) hq)

/-- The compatible-pair ring is Artinian when the first leg is surjective. -/
lemma isArtinianRing (hq : Function.Surjective (toAlgHom q)) :
    IsArtinianRing (algebra q r) := by
  let P : Type u := algebra q r
  let : Algebra P A.algebra :=
    (AlgHom.pullbackFst (toAlgHom q) (toAlgHom r)).toRingHom.toAlgebra
  let : Algebra P B.algebra :=
    (AlgHom.pullbackSnd (toAlgHom q) (toAlgHom r)).toRingHom.toAlgebra
  let : IsLocalHom (algebraMap P A.algebra) :=
    RingHom.isLocalHom_pullbackFst (toAlgHom q).toRingHom (toAlgHom r).toRingHom
  let : IsLocalHom (algebraMap P B.algebra) :=
    RingHom.isLocalHom_pullbackSnd (toAlgHom q).toRingHom (toAlgHom r).toRingHom
  let : Module P (A.algebra × B.algebra) := Prod.instModule
  have hA : IsFiniteLength P A.algebra :=
    isFiniteLength_of_common_augmentation (augmentation q r).toRingHom
      A.augmentation.toRingHom (augmentation_surjective q r hq) A.augmentation_surjective
      (congrArg AlgHom.toRingHom (augmentation_fst q r))
  have hB : IsFiniteLength P B.algebra :=
    isFiniteLength_of_common_augmentation (augmentation q r).toRingHom
      B.augmentation.toRingHom (augmentation_surjective q r hq) B.augmentation_surjective rfl
  have : IsArtinian P A.algebra :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hA).2
  have : IsArtinian P B.algebra :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hB).2
  let e : P →ₗ[P] A.algebra × B.algebra :=
    { toFun := Subtype.val
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact isArtinian_of_injective e Subtype.val_injective

/-- The actual augmented Artinian test on the ordinary compatible-pair algebra. -/
def test (hq : Function.Surjective (toAlgHom q)) : ArtinianTest k K := by
  let := isArtinianRing q r hq
  exact ArtinianTest.mk (algebra q r) (augmentation q r) (augmentation_surjective q r hq)

/-- The first actual test projection. -/
def fst (hq : Function.Surjective (toAlgHom q)) : test q r hq ⟶ A :=
  homMk (AlgHom.pullbackFst (toAlgHom q) (toAlgHom r)) (augmentation_fst q r)

/-- The second actual test projection. -/
def snd (hq : Function.Surjective (toAlgHom q)) : test q r hq ⟶ B :=
  homMk (AlgHom.pullbackSnd (toAlgHom q) (toAlgHom r)) rfl

lemma condition (hq : Function.Surjective (toAlgHom q)) :
    fst q r hq ≫ q = snd q r hq ≫ r := by
  apply ArtinianTest.hom_ext
  exact AlgHom.pullback_comm_sq (toAlgHom q) (toAlgHom r)

lemma snd_surjective (hq : Function.Surjective (toAlgHom q)) :
    Function.Surjective (toAlgHom (snd q r hq)) :=
  AlgHom.surjective_pullbackSnd_of_surjective (toAlgHom q) (toAlgHom r) hq

/-- The ordinary universal algebra map to compatible pairs. -/
def liftAlgHom {D : Type u} [CommRing D] [Algebra k D]
    (a : D →ₐ[k] A.algebra) (b : D →ₐ[k] B.algebra)
    (hab : (toAlgHom q).comp a = (toAlgHom r).comp b) : D →ₐ[k] algebra q r :=
  (a.prod b).codRestrict (algebra q r) (fun x ↦ DFunLike.congr_fun hab x)

@[simp]
lemma fst_liftAlgHom {D : Type u} [CommRing D] [Algebra k D]
    (a : D →ₐ[k] A.algebra) (b : D →ₐ[k] B.algebra)
    (hab : (toAlgHom q).comp a = (toAlgHom r).comp b) :
    (AlgHom.pullbackFst (toAlgHom q) (toAlgHom r)).comp (liftAlgHom q r a b hab) = a := rfl

@[simp]
lemma snd_liftAlgHom {D : Type u} [CommRing D] [Algebra k D]
    (a : D →ₐ[k] A.algebra) (b : D →ₐ[k] B.algebra)
    (hab : (toAlgHom q).comp a = (toAlgHom r).comp b) :
    (AlgHom.pullbackSnd (toAlgHom q) (toAlgHom r)).comp (liftAlgHom q r a b hab) = b := rfl

/-- Compatible actual test arrows give their actual universal test arrow. -/
def lift (hq : Function.Surjective (toAlgHom q)) {D : ArtinianTest k K}
    (a : D ⟶ A) (b : D ⟶ B) (hab : a ≫ q = b ≫ r) : D ⟶ test q r hq :=
  homMk (liftAlgHom q r (toAlgHom a) (toAlgHom b) (congrArg toAlgHom hab)) (by
    ext x
    exact DFunLike.congr_fun (augmentation_comp b) x)

@[simp, reassoc]
lemma lift_fst (hq : Function.Surjective (toAlgHom q)) {D : ArtinianTest k K}
    (a : D ⟶ A) (b : D ⟶ B) (hab : a ≫ q = b ≫ r) :
    lift q r hq a b hab ≫ fst q r hq = a := by
  apply ArtinianTest.hom_ext
  rfl

@[simp, reassoc]
lemma lift_snd (hq : Function.Surjective (toAlgHom q)) {D : ArtinianTest k K}
    (a : D ⟶ A) (b : D ⟶ B) (hab : a ≫ q = b ≫ r) :
    lift q r hq a b hab ≫ snd q r hq = b := by
  apply ArtinianTest.hom_ext
  rfl

/-- The two projections determine every actual test arrow into the pullback. -/
lemma hom_ext (hq : Function.Surjective (toAlgHom q)) {D : ArtinianTest k K}
    {a b : D ⟶ test q r hq} (hfst : a ≫ fst q r hq = b ≫ fst q r hq)
    (hsnd : a ≫ snd q r hq = b ≫ snd q r hq) : a = b := by
  apply ArtinianTest.hom_ext
  ext x
  apply Subtype.ext
  exact Prod.ext (congrArg (fun f ↦ toAlgHom f x) hfst)
    (congrArg (fun f ↦ toAlgHom f x) hsnd)

/-- The actual test cone has the universal property of a pullback. -/
def isLimit (hq : Function.Surjective (toAlgHom q)) :
    Limits.IsLimit (Limits.PullbackCone.mk (fst q r hq) (snd q r hq) (condition q r hq)) :=
  Limits.PullbackCone.IsLimit.mk (condition q r hq)
    (fun s ↦ lift q r hq s.fst s.snd s.condition)
    (fun s ↦ lift_fst q r hq s.fst s.snd s.condition)
    (fun s ↦ lift_snd q r hq s.fst s.snd s.condition)
    (fun _ _ hm₁ hm₂ ↦ hom_ext q r hq (hm₁.trans (lift_fst q r hq _ _ _).symm)
      (hm₂.trans (lift_snd q r hq _ _ _).symm))

lemma isPullback (hq : Function.Surjective (toAlgHom q)) :
    IsPullback (fst q r hq) (snd q r hq) q r :=
  ⟨⟨condition q r hq⟩, ⟨isLimit q r hq⟩⟩

/-- Pulling back an elementary surjection gives an elementary surjection. -/
lemma snd_isElementary (hq : IsElementarySurjection q) :
    IsElementarySurjection (snd q r hq.1) := by
  refine ⟨snd_surjective q r hq.1, le_antisymm ?_ bot_le⟩
  apply Ideal.mul_le.mpr
  intro x hx y hy
  change x * y = 0
  apply Subtype.ext
  apply Prod.ext
  · have hxA : x.val.1 ∈ IsLocalRing.maximalIdeal A.algebra :=
      map_nonunit (toAlgHom (fst q r hq.1)).toRingHom x hx
    have hyB : y.val.2 = 0 := RingHom.mem_ker.mp hy
    have hyA : y.val.1 ∈ RingHom.ker (toAlgHom q).toRingHom := by
      change toAlgHom q y.val.1 = 0
      have hrel : toAlgHom q y.val.1 = toAlgHom r y.val.2 := y.property
      rw [hrel, hyB, map_zero]
    have hz := Ideal.mul_mem_mul hxA hyA
    rw [hq.2] at hz
    exact Ideal.mem_bot.mp hz
  · have hyB : y.val.2 = 0 := RingHom.mem_ker.mp hy
    change x.val.2 * y.val.2 = 0
    rw [hyB, mul_zero]

/-- The universal ring map also allows sources without a specified k-algebra structure. -/
def liftRingHom {D : Type u} [CommRing D]
    (a : D →+* A.algebra) (b : D →+* B.algebra)
    (hab : (toAlgHom q).toRingHom.comp a = (toAlgHom r).toRingHom.comp b) :
    D →+* algebra q r :=
  (a.prod b).codRestrict
    ((toAlgHom q).toRingHom.pullback (toAlgHom r).toRingHom)
    (fun x ↦ DFunLike.congr_fun hab x)

/-- The same ordinary compatible-pair square is Cartesian in commutative rings. -/
lemma ring_isPullback :
    IsPullback
      (CommRingCat.ofHom (AlgHom.pullbackFst (toAlgHom q) (toAlgHom r)).toRingHom)
      (CommRingCat.ofHom (AlgHom.pullbackSnd (toAlgHom q) (toAlgHom r)).toRingHom)
      (CommRingCat.ofHom (toAlgHom q).toRingHom)
      (CommRingCat.ofHom (toAlgHom r).toRingHom) := by
  refine ⟨⟨?_⟩, ⟨Limits.PullbackCone.isLimitAux' _ ?_⟩⟩
  · apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (AlgHom.pullback_comm_sq (toAlgHom q) (toAlgHom r))
  · intro s
    refine ⟨CommRingCat.ofHom (liftRingHom q r s.fst.hom s.snd.hom
      (congrArg CommRingCat.Hom.hom s.condition)), ?_, ?_, ?_⟩
    · apply CommRingCat.hom_ext
      rfl
    · apply CommRingCat.hom_ext
      rfl
    · intro m hm₁ hm₂
      apply CommRingCat.hom_ext
      ext x
      apply Subtype.ext
      exact Prod.ext (congrArg (fun f ↦ f.hom x) hm₁)
        (congrArg (fun f ↦ f.hom x) hm₂)

end ArtinianTest.Pullback

end Langlands.AlgebraicGeometry.Deformation
