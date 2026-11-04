import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Augmented local Artinian algebra tests and their pointed spectra -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Deformation

variable (k K : Type u) [CommRing k] [Field K] [Algebra k K]

/-- Local Artinian `k`-algebras with a specified surjective `k`-augmentation to `K`. -/
abbrev ArtinianTest :=
  ObjectProperty.FullSubcategory (fun A : Over (CommAlgCat.of k K) ↦
    IsLocalRing A.left ∧ IsArtinianRing A.left ∧ Function.Surjective A.hom.hom)

namespace ArtinianTest

variable {k K}

/-- The actual coefficient algebra of a test. -/
abbrev algebra (A : ArtinianTest k K) : CommAlgCat.{u} k := A.obj.left

instance (A : ArtinianTest k K) : IsLocalRing A.algebra := A.property.1

instance (A : ArtinianTest k K) : IsArtinianRing A.algebra := A.property.2.1

/-- The specified residue augmentation; no section of this map is chosen. -/
abbrev augmentation (A : ArtinianTest k K) : A.algebra →ₐ[k] K := A.obj.hom.hom

lemma augmentation_surjective (A : ArtinianTest k K) : Function.Surjective A.augmentation :=
  A.property.2.2

/-- Bundle any actual local Artinian algebra with its surjective augmentation. -/
def mk (R : Type u) [CommRing R] [Algebra k R] [IsLocalRing R] [IsArtinianRing R]
    (ε : R →ₐ[k] K) (hε : Function.Surjective ε) : ArtinianTest k K :=
  ⟨Over.mk (CommAlgCat.ofHom ε), (show IsLocalRing R from inferInstance),
    (show IsArtinianRing R from inferInstance), hε⟩

/-- A test arrow is an actual augmentation-preserving algebra homomorphism. -/
abbrev toAlgHom {A B : ArtinianTest k K} (q : A ⟶ B) : A.algebra →ₐ[k] B.algebra :=
  q.hom.left.hom

lemma augmentation_comp {A B : ArtinianTest k K} (q : A ⟶ B) :
    B.augmentation.comp (toAlgHom q) = A.augmentation :=
  congrArg CommAlgCat.Hom.hom (Over.w q.hom)

@[simp]
lemma toAlgHom_id (A : ArtinianTest k K) : toAlgHom (𝟙 A) = AlgHom.id k A.algebra := rfl

@[simp]
lemma toAlgHom_comp {A B C : ArtinianTest k K} (q : A ⟶ B) (r : B ⟶ C) :
    toAlgHom (q ≫ r) = (toAlgHom r).comp (toAlgHom q) := rfl

/-- Construct a test arrow from an actual compatible algebra map. -/
def homMk {A B : ArtinianTest k K} (q : A.algebra →ₐ[k] B.algebra)
    (hq : B.augmentation.comp q = A.augmentation) : A ⟶ B :=
  ObjectProperty.homMk (Over.homMk (CommAlgCat.ofHom q) (by
    apply CommAlgCat.hom_ext
    exact hq))

/-- The augmentation kernel is exactly the maximal ideal of the local test ring. -/
lemma ker_augmentation (A : ArtinianTest k K) :
    RingHom.ker A.augmentation.toRingHom = IsLocalRing.maximalIdeal A.algebra :=
  IsLocalRing.ker_eq_maximalIdeal _ A.augmentation_surjective

/-- Every augmentation-preserving arrow is local, including nonsurjective arrows. -/
instance isLocalHom {A B : ArtinianTest k K} (q : A ⟶ B) :
    IsLocalHom (toAlgHom q).toRingHom := by
  have hA : IsLocalHom A.augmentation.toRingHom :=
    IsLocalHom.of_surjective _ A.augmentation_surjective
  have heq : B.augmentation.toRingHom.comp (toAlgHom q).toRingHom =
      A.augmentation.toRingHom := congrArg AlgHom.toRingHom (augmentation_comp q)
  have : IsLocalHom (B.augmentation.toRingHom.comp (toAlgHom q).toRingHom) := heq.symm ▸ hA
  exact isLocalHom_of_comp _ B.augmentation.toRingHom

/-- The kernel of every test arrow lies in the maximal ideal of its source. -/
lemma ker_le_maximalIdeal {A B : ArtinianTest k K} (q : A ⟶ B) :
    RingHom.ker (toAlgHom q).toRingHom ≤ IsLocalRing.maximalIdeal A.algebra := by
  rw [← ker_augmentation A]
  intro x hx
  change A.augmentation x = 0
  rw [← augmentation_comp q]
  change B.augmentation (toAlgHom q x) = 0
  have hx' : toAlgHom q x = 0 := RingHom.mem_ker.mp hx
  rw [hx', map_zero]

/-- The maximal ideal of a local Artinian test is nilpotent. -/
lemma maximalIdeal_isNilpotent (A : ArtinianTest k K) :
    IsNilpotent (IsLocalRing.maximalIdeal A.algebra) := by
  rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  exact IsArtinianRing.isNilpotent_jacobson_bot

/-- The augmentation is an actual nilpotent thickening of its residue field. -/
lemma augmentation_ker_isNilpotent (A : ArtinianTest k K) :
    IsNilpotent (RingHom.ker A.augmentation.toRingHom) := by
  rw [ker_augmentation]
  exact maximalIdeal_isNilpotent A

/-- The fixed residue scheme over the original base ring. -/
def residueBase (k K : Type u) [CommRing k] [Field K] [Algebra k K] :
    Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))

/-- The actual affine scheme of a test, with its original `k`-structure. -/
def base (A : ArtinianTest k K) : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A.algebra)))

/-- The augmentation induces the actual residue-point map over `k`. -/
def reduction (A : ArtinianTest k K) : residueBase k K ⟶ base A :=
  Over.homMk (Spec.map (CommRingCat.ofHom A.augmentation.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact A.augmentation.comp_algebraMap)

/-- The actual affine scheme map induced contravariantly by a test arrow. -/
def baseMap {A B : ArtinianTest k K} (q : A ⟶ B) : base B ⟶ base A :=
  Over.homMk (Spec.map (CommRingCat.ofHom (toAlgHom q).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (toAlgHom q).comp_algebraMap)

@[simp]
lemma baseMap_id (A : ArtinianTest k K) : baseMap (𝟙 A) = 𝟙 (base A) := by
  apply Over.OverMorphism.ext
  exact Spec.map_id _

@[simp, reassoc]
lemma baseMap_comp {A B C : ArtinianTest k K} (q : A ⟶ B) (r : B ⟶ C) :
    baseMap r ≫ baseMap q = baseMap (q ≫ r) := by
  apply Over.OverMorphism.ext
  exact (Spec.map_comp _ _).symm

@[reassoc (attr := simp)]
lemma reduction_baseMap {A B : ArtinianTest k K} (q : A ⟶ B) :
    reduction B ≫ baseMap q = reduction A := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (augmentation_comp q)

/-- The affine pointed test remembers the actual specified residue map. -/
def pointedTest (A : ArtinianTest k K) : Under (residueBase k K) :=
  Under.mk (reduction A)

/-- Test arrows give actual pointed scheme maps, with the augmentation triangle. -/
def pointedMap {A B : ArtinianTest k K} (q : A ⟶ B) : pointedTest B ⟶ pointedTest A :=
  Under.homMk (baseMap q) (reduction_baseMap q)

/-- The contravariant spectrum functor from actual augmented local Artinian tests. -/
def pointedSpec (k K : Type u) [CommRing k] [Field K] [Algebra k K] :
    (ArtinianTest k K)ᵒᵖ ⥤ Under (residueBase k K) where
  obj A := pointedTest A.unop
  map q := pointedMap q.unop
  map_id A := by
    apply Under.UnderMorphism.ext
    exact baseMap_id A.unop
  map_comp q r := by
    apply Under.UnderMorphism.ext
    exact (baseMap_comp r.unop q.unop).symm

/-- A surjection whose kernel is annihilated by the maximal ideal of the source.
No restriction to a one-dimensional kernel is part of this internal convention. -/
def IsElementarySurjection {A B : ArtinianTest k K} (q : A ⟶ B) : Prop :=
  Function.Surjective (toAlgHom q) ∧
    IsLocalRing.maximalIdeal A.algebra * RingHom.ker (toAlgHom q).toRingHom = ⊥

/-- Maximal-ideal-annihilated kernels are square zero. -/
lemma IsElementarySurjection.ker_sq {A B : ArtinianTest k K} {q : A ⟶ B}
    (hq : IsElementarySurjection q) : (RingHom.ker (toAlgHom q).toRingHom) ^ 2 = ⊥ := by
  rw [pow_two]
  exact le_antisymm ((mul_le_mul' (ker_le_maximalIdeal q) le_rfl).trans_eq hq.2) bot_le

/-- Every surjective test arrow induces a genuine closed immersion of test schemes. -/
lemma baseMap_isClosedImmersion {A B : ArtinianTest k K} (q : A ⟶ B)
    (hq : Function.Surjective (toAlgHom q)) : IsClosedImmersion (baseMap q).left :=
  IsClosedImmersion.spec_of_surjective _ hq

/-- The specified residue-point map is a genuine closed immersion. -/
instance reduction_isClosedImmersion (A : ArtinianTest k K) :
    IsClosedImmersion (reduction A).left :=
  IsClosedImmersion.spec_of_surjective _ A.augmentation_surjective

end ArtinianTest

end Langlands.AlgebraicGeometry.Deformation
