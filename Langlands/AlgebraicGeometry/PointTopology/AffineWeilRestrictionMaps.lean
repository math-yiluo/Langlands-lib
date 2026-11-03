import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestriction
import Langlands.RingTheory.WeilRestriction.Functorial

/-! # Maps of actual affine finite-type Weil restrictions -/

noncomputable section

universe u

open CategoryTheory TensorProduct
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

open Langlands.Algebra

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]

/-- The algebra-point comparison commutes with the constructed coordinate maps. -/
theorem weilRestrictionAlgPointEquiv_precomp
    {C D : Type u} [CommRing C] [CommRing D] [Algebra B C] [Algebra B D]
    [Algebra.FiniteType B C] [Algebra.FiniteType B D]
    (φ : C →ₐ[B] D)
    (p : AlgPoint A (WeilRestrictionFiniteType A B D) A) :
    weilRestrictionAlgPointEquiv A B C
        (AlgPoint.precomp (WeilRestrictionFiniteType.map A B φ) p) =
      AlgPoint.precomp φ (weilRestrictionAlgPointEquiv A B D p) := by
  apply AlgPoint.ext
  intro c
  change Algebra.TensorProduct.rid A B B
      (WeilRestrictionFiniteType.homEquiv A B C A
        (p.toAlgHom.comp (WeilRestrictionFiniteType.map A B φ)) c) =
    Algebra.TensorProduct.rid A B B
      ((WeilRestrictionFiniteType.homEquiv A B D A p.toAlgHom).comp φ c)
  rw [WeilRestrictionFiniteType.homEquiv_comp_map]

/-- Postcomposition by a spectrum map is precomposition of algebra maps. -/
theorem affineRingPointEquiv_postcomp_ringTestMap
    {C D T : Type u} [CommRing C] [CommRing D] [CommRing T]
    [Algebra A C] [Algebra A D] [Algebra A T]
    (φ : C →ₐ[A] D) (p : RingPoint A (ringTest A D) T) :
    affineRingPointEquiv A C T (p ≫ ringTestMap A φ) =
      (affineRingPointEquiv A D T p).comp φ := by
  apply AlgHom.coe_ringHom_injective
  let p₀ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of D) := p.left
  change (Spec.preimage (p₀ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))).hom =
    (Spec.preimage p₀).hom.comp φ.toRingHom
  rw [Spec.preimage_comp, Spec.preimage_map, CommRingCat.hom_comp]
  rfl

variable {X Y Z : Over (Spec (CommRingCat.of B))}
  [IsAffine X.left] [IsAffine Y.left] [IsAffine Z.left]
  [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
  [LocallyOfFiniteType Z.hom]

/-- The actual morphism of affine Weil-restriction schemes induced by a
morphism of the original schemes. -/
def affineWeilRestrictionMap (f : X ⟶ Y) :
    affineWeilRestriction A B X ⟶ affineWeilRestriction A B Y :=
  ringTestMap A (WeilRestrictionFiniteType.map A B (affineCoordinatePullback B f))

@[simp]
theorem affineWeilRestrictionMap_id :
    affineWeilRestrictionMap A B (𝟙 X) = 𝟙 (affineWeilRestriction A B X) := by
  simp [affineWeilRestrictionMap, affineWeilRestriction]

theorem affineWeilRestrictionMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    affineWeilRestrictionMap A B (f ≫ g) =
      affineWeilRestrictionMap A B f ≫ affineWeilRestrictionMap A B g := by
  simp only [affineWeilRestrictionMap, affineCoordinatePullback_comp,
    WeilRestrictionFiniteType.map_comp, ringTestMap_comp]
  rfl

/-- The representing equivalence is the universal tensor-valued point map
in the original scheme's coordinates. -/
theorem affineWeilRestrictionPointEquiv_coordinates
    (T : Type u) [CommRing T] [Algebra A T]
    (p : RingPoint A (affineWeilRestriction A B X) T) :
    affineSchemePointEquiv B X (B ⊗[A] T)
        (affineWeilRestrictionPointEquiv A B X T p) =
      AlgPoint.ofAlgHom (WeilRestrictionFiniteType.homEquiv A B
        (AffineCoordinateRing B X) T (affineRingPointEquiv A
          (WeilRestrictionFiniteType A B (AffineCoordinateRing B X)) T p)) :=
  (affineSchemePointEquiv B X (B ⊗[A] T)).apply_symm_apply _

/-- Naturality in the original scheme at every affine test algebra. -/
theorem affineWeilRestrictionPointEquiv_natural
    (T : Type u) [CommRing T] [Algebra A T]
    (f : X ⟶ Y) (p : RingPoint A (affineWeilRestriction A B X) T) :
    affineWeilRestrictionPointEquiv A B Y T
        (p ≫ affineWeilRestrictionMap A B f) =
      affineWeilRestrictionPointEquiv A B X T p ≫ f := by
  dsimp only [RingPoint, affineWeilRestriction] at p
  apply (affineSchemePointEquiv B Y (B ⊗[A] T)).injective
  erw [affineWeilRestrictionPointEquiv_coordinates A B T
      (p ≫ affineWeilRestrictionMap A B f),
    affineSchemePointEquiv_natural B (B ⊗[A] T) f,
    affineWeilRestrictionPointEquiv_coordinates A B T p]
  change AlgPoint.ofAlgHom (WeilRestrictionFiniteType.homEquiv A B
      (AffineCoordinateRing B Y) T (affineRingPointEquiv A
        (WeilRestrictionFiniteType A B (AffineCoordinateRing B Y)) T
          (p ≫ ringTestMap A _))) = _
  erw [affineRingPointEquiv_postcomp_ringTestMap A
      (WeilRestrictionFiniteType.map A B (affineCoordinatePullback B f)) p,
    WeilRestrictionFiniteType.homEquiv_comp_map]
  rfl

variable [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace B] [IsTopologicalRing B] [IsModuleTopology A B]

/-- The actual point homeomorphism commutes with the actual scheme maps. -/
theorem affineWeilRestrictionPointHomeomorph_natural
    (f : X ⟶ Y) (p : RingPoint A (affineWeilRestriction A B X) A) :
    affineWeilRestrictionPointHomeomorph A B Y
        (p ≫ affineWeilRestrictionMap A B f) =
      affineWeilRestrictionPointHomeomorph A B X p ≫ f := by
  dsimp only [RingPoint, affineWeilRestriction] at p
  apply (affineSchemePointEquiv B Y B).injective
  erw [affineWeilRestrictionPointHomeomorph_apply A B Y
      (p ≫ affineWeilRestrictionMap A B f),
    affineSchemePointEquiv_natural B B f,
    affineWeilRestrictionPointHomeomorph_apply A B X p]
  change weilRestrictionAlgPointEquiv A B (AffineCoordinateRing B Y)
      (AlgPoint.ofAlgHom (affineRingPointEquiv A
        (WeilRestrictionFiniteType A B (AffineCoordinateRing B Y)) A
          (p ≫ ringTestMap A _))) = _
  erw [affineRingPointEquiv_postcomp_ringTestMap A
    (WeilRestrictionFiniteType.map A B (affineCoordinatePullback B f)) p]
  exact weilRestrictionAlgPointEquiv_precomp A B _ _

end Langlands.AlgebraicGeometry.PointTopology
