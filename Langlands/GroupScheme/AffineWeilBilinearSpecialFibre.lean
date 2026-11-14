import Langlands.GroupScheme.AffineWeilBilinearKernel
import Langlands.GroupScheme.AffineWeilBaseChange
import Langlands.GroupScheme.BilinearCoordinateBaseChange
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Special-fibre kernels of restricted bilinear homomorphisms -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.AffineWeil

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
  {G H : GroupScheme (Spec (CommRingCat.of B))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

/-- Restriction of an isomorphism retains the original restricted homomorphisms. -/
def mapIso (e : G ≅ H) : groupScheme A B G ≅ groupScheme A B H where
  hom := map A B e.hom
  inv := map A B e.inv
  hom_inv_id := by rw [← map_comp, e.hom_inv_id, map_id]
  inv_hom_id := by rw [← map_comp, e.inv_hom_id, map_id]

end Langlands.GroupScheme.AffineWeil

namespace Langlands.GroupScheme.AffineWeilBilinear

variable (A B k : Type u) [CommRing A] [CommRing B] [Field k]
  [Algebra A B] [Algebra A k]
  [Module.Finite A B] [Module.Projective A B]
  {I J : Type u} [Fintype I] [Fintype J]
  (c : I → I → B) (d : J → J → B)

attribute [local instance] bilinear_isAffine bilinear_locallyOfFiniteType
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The coefficient change from the original algebra to its fibre algebra. -/
abbrev fibreCoefficientMap : CommRingCat.of B ⟶ CommRingCat.of (k ⊗[A] B) :=
  CommRingCat.ofHom (algebraMap B (k ⊗[A] B))

/-- The actual base change of the restriction has the expected bilinear restriction model. -/
def restrictionFibreIso :
    AffineWeil.BaseChange.source A B k
        (BilinearCoordinate.groupScheme (CommRingCat.of B) c) ≅
      AffineWeil.groupScheme k (k ⊗[A] B)
        (BilinearCoordinate.groupScheme (CommRingCat.of (k ⊗[A] B))
          (BilinearCoordinate.mappedCoefficients (fibreCoefficientMap A B k) c)) :=
  AffineWeil.BaseChange.iso A B k
      (BilinearCoordinate.groupScheme (CommRingCat.of B) c) ≪≫
    AffineWeil.mapIso k (k ⊗[A] B)
      (BilinearCoordinate.baseChangeIso (fibreCoefficientMap A B k) c)

variable {c d} (M : I → J → B) (t : B) (h : BilinearCoordinate.IsCompatible c d M t)

theorem restrictionFibreIso_linearHom :
    (restrictionFibreIso A B k c).hom ≫
        AffineWeil.map k (k ⊗[A] B)
          (BilinearCoordinate.linearHom (CommRingCat.of (k ⊗[A] B))
            (fun i j => algebraMap B (k ⊗[A] B) (M i j))
            (algebraMap B (k ⊗[A] B) t) (h.map (algebraMap B (k ⊗[A] B)))) =
      AffineWeil.BaseChange.sourceMap A B k
          (BilinearCoordinate.groupScheme (CommRingCat.of B) c)
          (BilinearCoordinate.linearHom (CommRingCat.of B) M t h) ≫
        (restrictionFibreIso A B k d).hom := by
  dsimp only [restrictionFibreIso, Iso.trans_hom, AffineWeil.mapIso]
  have hbc := BilinearCoordinate.linearHom_baseChange (fibreCoefficientMap A B k) M t h
  simp only [fibreCoefficientMap, CommRingCat.hom_ofHom] at hbc
  rw [Category.assoc, ← AffineWeil.map_comp,
    hbc, AffineWeil.map_comp,
    ← Category.assoc, AffineWeil.BaseChange.iso_naturality]
  rfl

/-- The original base-changed kernel is the kernel of the explicit restricted fibre map. -/
def linearKernelFibreIso :
    kernel (AffineWeil.BaseChange.sourceMap A B k
      (BilinearCoordinate.groupScheme (CommRingCat.of B) c)
      (BilinearCoordinate.linearHom (CommRingCat.of B) M t h)) ≅
      kernel (AffineWeil.map k (k ⊗[A] B)
        (BilinearCoordinate.linearHom (CommRingCat.of (k ⊗[A] B))
          (fun i j => algebraMap B (k ⊗[A] B) (M i j))
          (algebraMap B (k ⊗[A] B) t) (h.map (algebraMap B (k ⊗[A] B))))) :=
  kernelSquareIso _ _ (restrictionFibreIso A B k c) (restrictionFibreIso A B k d)
    (restrictionFibreIso_linearHom A B k M t h)

/-- The actual kernel of the base change of a restricted bilinear linear map is
smooth, connected and unipotent over the field. -/
theorem linearKernelFibre_properties :
    Smooth (kernel (AffineWeil.BaseChange.sourceMap A B k
      (BilinearCoordinate.groupScheme (CommRingCat.of B) c)
      (BilinearCoordinate.linearHom (CommRingCat.of B) M t h))).X.hom ∧
      ConnectedSpace (kernel (AffineWeil.BaseChange.sourceMap A B k
        (BilinearCoordinate.groupScheme (CommRingCat.of B) c)
        (BilinearCoordinate.linearHom (CommRingCat.of B) M t h))).X.left ∧
        IsUnipotent (kernel (AffineWeil.BaseChange.sourceMap A B k
          (BilinearCoordinate.groupScheme (CommRingCat.of B) c)
          (BilinearCoordinate.linearHom (CommRingCat.of B) M t h))) :=
  smooth_connected_unipotent_of_groupIso (linearKernelFibreIso A B k M t h)
    (linearKernel_properties k (k ⊗[A] B) (Module.finBasis k (k ⊗[A] B))
      (fun i j => algebraMap B (k ⊗[A] B) (M i j))
      (algebraMap B (k ⊗[A] B) t) (h.map (algebraMap B (k ⊗[A] B))))

end Langlands.GroupScheme.AffineWeilBilinear
