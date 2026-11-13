import Langlands.AlgebraicGeometry.Deformation.ArtinianTests
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Arbitrary Artinian surjections as pointed Artinian tests -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Langlands.AlgebraicGeometry.Deformation.ArtinianSurjectionTests

variable {R S : Type u} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [IsArtinianRing R] [IsArtinianRing S]
  [Algebra R S]

local notation "φ" => algebraMap R S

/-- The target residue map is linear over the original source ring. -/
def targetAugmentation : S →ₐ[R] ResidueField S where
  __ := residue S
  commutes' _ := rfl

/-- The source ring, pointed by the residue field of the target ring. -/
def source (hφ : Function.Surjective φ) : ArtinianTest R (ResidueField S) :=
  ArtinianTest.mk R (Algebra.ofId R (ResidueField S))
    (residue_surjective.comp hφ)

/-- The target ring with its actual residue augmentation. -/
def target : ArtinianTest R (ResidueField S) :=
  ArtinianTest.mk S (targetAugmentation (R := R) (S := S)) residue_surjective

/-- The original surjection as an augmentation-preserving arrow of tests. -/
def arrow (hφ : Function.Surjective φ) : source (R := R) (S := S) hφ ⟶ target (R := R) (S := S) :=
  ArtinianTest.homMk (Algebra.ofId R S) rfl

@[simp]
lemma arrow_toRingHom (hφ : Function.Surjective φ) :
    (ArtinianTest.toAlgHom (arrow (R := R) (S := S) hφ)).toRingHom = φ := rfl

@[simp]
lemma source_augmentation (hφ : Function.Surjective φ) :
    (source (R := R) (S := S) hφ).augmentation.toRingHom = (residue S).comp φ := rfl

@[simp]
lemma target_augmentation :
    (target (R := R) (S := S)).augmentation.toRingHom = residue S := rfl

/-- The elementary condition is unchanged when the map is bundled as a test arrow. -/
lemma arrow_isElementary (hφ : Function.Surjective φ)
    (hker : maximalIdeal R * RingHom.ker φ = ⊥) :
    ArtinianTest.IsElementarySurjection (arrow (R := R) (S := S) hφ) :=
  ⟨hφ, hker⟩

/-- The source test is over the identity of the original affine base. -/
lemma source_base_hom (hφ : Function.Surjective φ) :
    (ArtinianTest.base (source (R := R) (S := S) hφ)).hom = 𝟙 (Spec (CommRingCat.of R)) := by
  exact Spec.map_id _

/-- The test arrow induces exactly the original affine closed immersion. -/
lemma arrow_baseMap_left (hφ : Function.Surjective φ) :
    (ArtinianTest.baseMap (arrow (R := R) (S := S) hφ)).left =
      Spec.map (CommRingCat.ofHom φ) := rfl

/-- The residue immersion of the source uses the actual composite residue map. -/
lemma source_reduction_left (hφ : Function.Surjective φ) :
    (ArtinianTest.reduction (source (R := R) (S := S) hφ)).left =
      Spec.map (CommRingCat.ofHom ((residue S).comp φ)) := rfl

end Langlands.AlgebraicGeometry.Deformation.ArtinianSurjectionTests
