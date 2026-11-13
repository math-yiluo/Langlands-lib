import Langlands.GroupScheme.IntegralModel.GenericRigidity
import Langlands.GroupScheme.IntegralModelReduction
import Langlands.GroupScheme.KernelSquareTransport

/-! # Special-fibre kernels are invariant under compatible model isomorphisms -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  {M M' : IntegralModel R K G} {N N' : IntegralModel R K H}

/-- A square of model extensions over the same generic map commutes whenever
the source and target identifications induce the identity on generic fibres. -/
theorem Iso.hom_square (e : M.Iso M' (CategoryTheory.Iso.refl G))
    (d : N.Iso N' (CategoryTheory.Iso.refl H)) {f : G ⟶ H}
    (φ : M.Hom N f) (ψ : M'.Hom N' f) :
    e.iso.hom ≫ ψ.hom = φ.hom ≫ d.iso.hom := by
  apply hom_eq_of_generic
  apply (cancel_mono N'.genericIso.hom).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [ψ.generic_comm, ← Category.assoc, e.generic_comm]
  simp only [CategoryTheory.Iso.refl_hom, Category.comp_id]
  rw [d.generic_comm]
  simp only [CategoryTheory.Iso.refl_hom, Category.comp_id]
  exact φ.generic_comm.symm

section Residue

variable [IsLocalRing R]

/-- A compatible model isomorphism induces an isomorphism of the actual
special fibres over the residue field of the same coefficient ring. -/
def Iso.specialFibreIso {f : G ≅ H} (e : M.Iso N f) :
    M.specialFibre ≅ N.specialFibre :=
  (GroupScheme.baseChange (residueBaseMap R)).mapIso e.iso

/-- The kernels of any two extensions of the same generic map are isomorphic
under compatible source and target model identifications. -/
def Iso.specialFibreKernelIso (e : M.Iso M' (CategoryTheory.Iso.refl G))
    (d : N.Iso N' (CategoryTheory.Iso.refl H)) {f : G ⟶ H}
    (φ : M.Hom N f) (ψ : M'.Hom N' f) :
    kernel φ.specialFibreMap ≅ kernel ψ.specialFibreMap :=
  kernelSquareIso φ.specialFibreMap ψ.specialFibreMap e.specialFibreIso d.specialFibreIso
    (by
      change (GroupScheme.baseChange (residueBaseMap R)).map e.iso.hom ≫
          (GroupScheme.baseChange (residueBaseMap R)).map ψ.hom =
        (GroupScheme.baseChange (residueBaseMap R)).map φ.hom ≫
          (GroupScheme.baseChange (residueBaseMap R)).map d.iso.hom
      simpa only [Functor.map_comp] using
        congrArg (GroupScheme.baseChange (residueBaseMap R)).map (e.hom_square d φ ψ))

/-- The complete smooth, connected, unipotent kernel conclusion transfers from
one pair of presentations to any compatibly isomorphic pair. -/
theorem Iso.specialFibreKernel_properties
    (e : M.Iso M' (CategoryTheory.Iso.refl G))
    (d : N.Iso N' (CategoryTheory.Iso.refl H)) {f : G ⟶ H}
    (φ : M.Hom N f) (ψ : M'.Hom N' f)
    (hψ : Smooth (kernel ψ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel ψ.specialFibreMap).X.left ∧
        IsUnipotent (kernel ψ.specialFibreMap)) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) :=
  smooth_connected_unipotent_of_groupIso (e.specialFibreKernelIso d φ ψ) hψ

end Residue

end Langlands.GroupScheme.IntegralModel
