import Langlands.GroupScheme.Examples.SU3RootUnitaryIntegralChart
import Langlands.GroupScheme.BilinearCoordinateDiagonalKernel
import Langlands.GroupScheme.IntegralModel.SpecialFibreKernelIso

/-! # Special-fibre kernels of diagonal integral unitary chart transitions -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Classical
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SU3Root.IntegralChart

open BilinearCoordinate IntegralModel

variable {O K L : Type u} [CommRing O] [IsDomain O] [IsLocalRing O]
  [Field K] [Algebra O K] [IsFractionRing O K]
  [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {I : Type u} [Fintype I] (C C' : IntegralChart O K L I)
  (a : I → O) (t : O)
  (h : C.data.IsChartChange C'.data
    (fun i j => algebraMap O K (diagonalMatrix a i j)) (algebraMap O K t))

include h

omit [IsDomain O] in
/-- The cocycle identity for the diagonal chart transition over the residue field. -/
theorem diagonal_residue_isCompatible :
    IsCompatible
      (mappedCoefficients (CommRingCat.ofHom (IsLocalRing.residue O)) C.coeff)
      (mappedCoefficients (CommRingCat.ofHom (IsLocalRing.residue O)) C'.coeff)
      (diagonalMatrix (fun i => IsLocalRing.residue O (a i))) (IsLocalRing.residue O t) := by
  have hh := (C.isCompatible_of_isChartChange C' (diagonalMatrix a) t h).map
    (CommRingCat.ofHom (IsLocalRing.residue O)).hom
  rw [map_diagonalMatrix] at hh
  exact hh

/-- The diagonal morphism of the residue coordinate groups associated to the chart change. -/
abbrev diagonalResidueHom :=
  diagonalHom (CommRingCat.of (IsLocalRing.ResidueField O))
    (fun i => IsLocalRing.residue O (a i)) (IsLocalRing.residue O t)
    (C.diagonal_residue_isCompatible C' a t h)

/-- Every extension of the generic identity has the same residue-coordinate square as the
explicit diagonal chart transition. -/
theorem diagonal_specialFibre_square
    (φ : C.model.Hom C'.model (𝟙 (unitaryParameterGroup K L))) :
    (baseChangeIso (CommRingCat.ofHom (IsLocalRing.residue O)) C.coeff).hom ≫
        C.diagonalResidueHom C' a t h =
      φ.specialFibreMap ≫
        (baseChangeIso (CommRingCat.ofHom (IsLocalRing.residue O)) C'.coeff).hom := by
  have hs := linearHom_baseChange (CommRingCat.ofHom (IsLocalRing.residue O))
    (diagonalMatrix a) t (C.isCompatible_of_isChartChange C' (diagonalMatrix a) t h)
  simp only [map_diagonalMatrix] at hs
  change _ = (GroupScheme.baseChange (residueBaseMap O)).map φ.hom ≫ _
  rw [φ.hom_eq (C.chartHom C' (diagonalMatrix a) t h)]
  exact hs

/-- The actual special-fibre kernel of any extension of the generic identity is the
scheme-theoretic kernel of the reduced diagonal coordinate morphism. -/
def diagonalSpecialFibreKernelIso
    (φ : C.model.Hom C'.model (𝟙 (unitaryParameterGroup K L))) :
    kernel φ.specialFibreMap ≅ kernel (C.diagonalResidueHom C' a t h) :=
  kernelSquareIso φ.specialFibreMap (C.diagonalResidueHom C' a t h)
    (baseChangeIso (CommRingCat.ofHom (IsLocalRing.residue O)) C.coeff)
    (baseChangeIso (CommRingCat.ofHom (IsLocalRing.residue O)) C'.coeff)
    (C.diagonal_specialFibre_square C' a t h φ)

@[reassoc (attr := simp)]
theorem diagonalSpecialFibreKernelIso_hom_ι
    (φ : C.model.Hom C'.model (𝟙 (unitaryParameterGroup K L))) :
    (C.diagonalSpecialFibreKernelIso C' a t h φ).hom ≫
        kernelι (C.diagonalResidueHom C' a t h) =
      kernelι φ.specialFibreMap ≫
        (baseChangeIso (CommRingCat.ofHom (IsLocalRing.residue O)) C.coeff).hom :=
  kernelSquareIso_hom_ι _ _ _ _ _

/-- If the scalar coefficient reduces to zero, the kernel is the bilinear coordinate
group restricted to the vanishing vector coefficients, with its scalar coordinate retained. -/
def diagonalZeroSpecialFibreKernelIso
    (φ : C.model.Hom C'.model (𝟙 (unitaryParameterGroup K L)))
    (ht : IsLocalRing.residue O t = 0) :
    kernel φ.specialFibreMap ≅
      BilinearCoordinate.groupScheme (CommRingCat.of (IsLocalRing.ResidueField O))
        (kernelCoefficients
          (c := mappedCoefficients (CommRingCat.ofHom (IsLocalRing.residue O)) C.coeff)
          (fun i => IsLocalRing.residue O (a i))) :=
  (C.diagonalSpecialFibreKernelIso C' a t h φ) ≪≫
    diagonalZeroKernelIso (fun i => IsLocalRing.residue O (a i)) (IsLocalRing.residue O t)
      (C.diagonal_residue_isCompatible C' a t h) ht

/-- If the scalar coefficient has nonzero reduction, the kernel is the vector group on
precisely the vanishing vector coefficients. -/
def diagonalNonzeroSpecialFibreKernelIso
    (φ : C.model.Hom C'.model (𝟙 (unitaryParameterGroup K L)))
    (ht : IsLocalRing.residue O t ≠ 0) :
    kernel φ.specialFibreMap ≅
      VectorGroup.groupScheme (CommRingCat.of (IsLocalRing.ResidueField O))
        (Fintype.card (kernelIndices (fun i => IsLocalRing.residue O (a i)))) :=
  (C.diagonalSpecialFibreKernelIso C' a t h φ) ≪≫
    diagonalNonzeroKernelIso (fun i => IsLocalRing.residue O (a i)) (IsLocalRing.residue O t)
      (C.diagonal_residue_isCompatible C' a t h) ht

/-- Every extension between these integral charts has a smooth, connected and unipotent
actual special-fibre kernel, independently of which transition coefficients vanish. -/
theorem diagonal_specialFibre_kernel_properties
    (φ : C.model.Hom C'.model (𝟙 (unitaryParameterGroup K L))) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) :=
  smooth_connected_unipotent_of_groupIso (C.diagonalSpecialFibreKernelIso C' a t h φ)
    (diagonal_kernel_properties (fun i => IsLocalRing.residue O (a i))
      (IsLocalRing.residue O t) (C.diagonal_residue_isCompatible C' a t h))

variable {M N : IntegralModel O K (unitaryParameterGroup K L)}

/-- Compatible alternative source and target presentations give the same reduced kernel. -/
def diagonalPresentationKernelIso
    (e : M.Iso C.model (CategoryTheory.Iso.refl _))
    (d : N.Iso C'.model (CategoryTheory.Iso.refl _))
    (φ : M.Hom N (𝟙 (unitaryParameterGroup K L))) :
    kernel φ.specialFibreMap ≅ kernel (C.diagonalResidueHom C' a t h) :=
  (e.specialFibreKernelIso d φ (C.chartHom C' (diagonalMatrix a) t h)) ≪≫
    C.diagonalSpecialFibreKernelIso C' a t h (C.chartHom C' (diagonalMatrix a) t h)

/-- The three kernel properties hold for every compatibly isomorphic pair of model
presentations and every extension of the generic identity between them. -/
theorem diagonal_presentation_kernel_properties
    (e : M.Iso C.model (CategoryTheory.Iso.refl _))
    (d : N.Iso C'.model (CategoryTheory.Iso.refl _))
    (φ : M.Hom N (𝟙 (unitaryParameterGroup K L))) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) :=
  e.specialFibreKernel_properties d φ (C.chartHom C' (diagonalMatrix a) t h)
    (C.diagonal_specialFibre_kernel_properties C' a t h (C.chartHom C' (diagonalMatrix a) t h))

end Langlands.GroupScheme.SU3Root.IntegralChart
