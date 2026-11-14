import Langlands.GroupScheme.AffineWeilBilinearSpecialFibre
import Langlands.GroupScheme.IntegralModel.SpecialFibreKernelIso

/-! # Field-fibre kernels after restriction of compatible integral models -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable (A k : Type u) [CommRing A] [Field k] [Algebra A k]
  {O K : Type u} [CommRing O] [IsDomain O] [Field K]
  [Algebra O K] [IsFractionRing O K] [Algebra A O]
  [Module.Finite A O] [Module.Projective A O]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  {M M' : IntegralModel O K G} {N N' : IntegralModel O K H}

local instance {G₀ : GroupScheme (Spec (CommRingCat.of K))}
    (P : IntegralModel O K G₀) : IsAffine P.group.X.left :=
  isAffine_of_isAffineHom P.group.X.hom

/-- A compatible model identification induces the actual field-fibre identification
after restriction of scalars. -/
def Iso.weilFibreIso (e : M.Iso M' (CategoryTheory.Iso.refl G)) :
    AffineWeil.BaseChange.source A O k M.group ≅
      AffineWeil.BaseChange.source A O k M'.group :=
  (GroupScheme.baseChange (Spec.algebraMap A k)).mapIso (AffineWeil.mapIso A O e.iso)

/-- The original generic-compatible square still commutes after restriction and field
base change, giving an isomorphism of actual pullback kernels. -/
def Iso.weilFibreKernelIso (e : M.Iso M' (CategoryTheory.Iso.refl G))
    (d : N.Iso N' (CategoryTheory.Iso.refl H)) {f : G ⟶ H}
    (φ : M.Hom N f) (ψ : M'.Hom N' f) :
    kernel (AffineWeil.BaseChange.sourceMap A O k M.group φ.hom) ≅
      kernel (AffineWeil.BaseChange.sourceMap A O k M'.group ψ.hom) :=
  kernelSquareIso _ _ (e.weilFibreIso A k) (d.weilFibreIso A k) (by
    change
      (GroupScheme.baseChange (Spec.algebraMap A k)).map (AffineWeil.map A O e.iso.hom) ≫
          (GroupScheme.baseChange (Spec.algebraMap A k)).map (AffineWeil.map A O ψ.hom) =
        (GroupScheme.baseChange (Spec.algebraMap A k)).map (AffineWeil.map A O φ.hom) ≫
          (GroupScheme.baseChange (Spec.algebraMap A k)).map (AffineWeil.map A O d.iso.hom)
    rw [← Functor.map_comp, ← Functor.map_comp,
      ← AffineWeil.map_comp, ← AffineWeil.map_comp, e.hom_square d φ ψ])

/-- The smooth, connected, unipotent kernel conclusion transfers to compatible model
presentations before restricting scalars and taking the field fibre. -/
theorem Iso.weilFibreKernel_properties
    (e : M.Iso M' (CategoryTheory.Iso.refl G))
    (d : N.Iso N' (CategoryTheory.Iso.refl H)) {f : G ⟶ H}
    (φ : M.Hom N f) (ψ : M'.Hom N' f)
    (hψ : Smooth (kernel (AffineWeil.BaseChange.sourceMap A O k M'.group ψ.hom)).X.hom ∧
      ConnectedSpace (kernel (AffineWeil.BaseChange.sourceMap A O k M'.group ψ.hom)).X.left ∧
        IsUnipotent (kernel (AffineWeil.BaseChange.sourceMap A O k M'.group ψ.hom))) :
    Smooth (kernel (AffineWeil.BaseChange.sourceMap A O k M.group φ.hom)).X.hom ∧
      ConnectedSpace (kernel (AffineWeil.BaseChange.sourceMap A O k M.group φ.hom)).X.left ∧
        IsUnipotent (kernel (AffineWeil.BaseChange.sourceMap A O k M.group φ.hom)) :=
  smooth_connected_unipotent_of_groupIso (e.weilFibreKernelIso A k d φ ψ) hψ

end Langlands.GroupScheme.IntegralModel
