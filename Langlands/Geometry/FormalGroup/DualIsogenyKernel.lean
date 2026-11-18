import Langlands.Geometry.FormalGroup.KernelTorsor
import Langlands.Geometry.FormalGroup.PiDivisible
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Finite locally free kernels of scalar-power duals -/

noncomputable section
universe u v
namespace Langlands.FormalGroup.ModuleLaw.Hom
open CategoryTheory
open scoped TensorProduct
attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {π : O}

/-- Scalar divisibility lifts the universal original-kernel point to the
scalar kernel on the other side of an integral scalar-power dual. -/
theorem exists_fppf_kernel_fibre_lift
    (hM : M.IsPiDivisible π) {f : Hom M N} {g : Hom N M} {j : ℕ}
    (hgf : g.comp f = M.scalarHom (π ^ j))
    (hfg : f.comp g = N.scalarHom (π ^ j)) (K : FiniteKernelModel f) :
    ∃ (B : CommAlgCat.{v} R) (β : K.coordinateAlgebra ⟶ B),
      β.hom.toRingHom.FaithfullyFlat ∧ β.hom.FinitePresentation ∧
      ∃ η : (N.scalarHom (π ^ j)).kernelPoints B,
        g.onAlgebraPoints η.val = (K.represents.homEquiv β).val := by
  obtain ⟨B, β, hff, hfp, x, hx⟩ :=
    hM.scalarPower_locallySurjective j K.coordinateAlgebra K.universalPoint.val
  have hη : g.onAlgebraPoints (f.onAlgebraPoints x) =
      (K.represents.homEquiv β).val := by
    rw [← onAlgebraPoints_comp, hgf, hx, K.universalPoint_map]
  refine ⟨B, β, hff, hfp, ⟨f.onAlgebraPoints x, ?_⟩, hη⟩
  change (N.scalarHom (π ^ j)).onAlgebraPoints (f.onAlgebraPoints x) = 0
  rw [← hfg, onAlgebraPoints_comp, hη]
  exact (K.represents.homEquiv β).property

/-- The quotient construction and the actual torsor fibre establish the
finite locally free kernel of an integral scalar-power dual. -/
theorem hasFiniteLocallyFreeKernel_of_comp_eq_scalarHom
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π)
    {f : Hom M N} (hf : f.IsIsogeny) {g : Hom N M} {j : ℕ}
    (hgf : g.comp f = M.scalarHom (π ^ j))
    (hfg : f.comp g = N.scalarHom (π ^ j)) : g.HasFiniteLocallyFreeKernel := by
  obtain ⟨C⟩ := hN.scalarPower_finiteKernel j
  obtain ⟨K⟩ := hf.2
  obtain ⟨B, β, hβ, _hfp, η, hη⟩ :=
    exists_fppf_kernel_fibre_lift hM hgf hfg K
  let A₀ : CommAlgCat.{v} R := CommAlgCat.of R R
  let ε : K.coordinateAlgebra ⟶ A₀ :=
    K.represents.homEquiv.symm ⟨0, by
      change f.onAlgebraPoints (A := A₀) 0 = 0
      exact map_zero _⟩
  have hK : Module.FaithfullyFlat R K.coordinateAlgebra := by
    apply Module.FaithfullyFlat.of_comap_surjective
    intro p
    refine ⟨p.comap ε.hom.toRingHom, ?_⟩
    have he : ε.hom.toRingHom.comp (algebraMap R K.coordinateAlgebra) = RingHom.id R :=
      RingHom.ext ε.hom.commutes
    rw [← PrimeSpectrum.comap_comp_apply, he, PrimeSpectrum.comap_id]
  let := hK
  have hKB : β.hom.toRingHom.comp (algebraMap R K.coordinateAlgebra) =
      algebraMap R B := RingHom.ext β.hom.commutes
  have hB : Module.FaithfullyFlat R B := by
    apply RingHom.faithfullyFlat_algebraMap_iff.mp
    rw [← hKB]
    exact RingHom.FaithfullyFlat.stableUnderComposition _ _
      (RingHom.faithfullyFlat_algebraMap_iff.mpr hK) hβ
  let D := KernelQuotient.coordinateAlgebra C g
  let T := KernelTorsor.tensorAlgebra C g B
  have hCT := KernelTorsor.fibreMap_flat C K hfg β η hη hβ.flat
  have hRT : Module.Flat R T := by
    apply RingHom.flat_algebraMap_iff.mp
    have he : (KernelTorsor.fibreMap C hfg η).hom.toRingHom.comp
        (algebraMap R C.coordinateAlgebra) = algebraMap R T :=
      RingHom.ext (KernelTorsor.fibreMap C hfg η).hom.commutes
    rw [← he]
    exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr inferInstance) hCT
  have hD : Module.Flat R D := by
    let := hB
    let : Module.Flat R (D ⊗[R] B) := hRT
    let : Module.Flat R (B ⊗[R] D) :=
      Module.Flat.of_linearEquiv (TensorProduct.comm R B D)
    rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
    intro X Y _ _ _ _ a ha
    rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective R B]
    have he : LinearMap.lTensor B (LinearMap.lTensor D a) =
        (TensorProduct.assoc R B D Y).toLinearMap ∘ₗ
          LinearMap.lTensor (B ⊗[R] D) a ∘ₗ
            (TensorProduct.assoc R B D X).symm.toLinearMap := by
      ext
      rfl
    rw [he]
    exact (TensorProduct.assoc R B D Y).injective.comp
      ((Module.Flat.lTensor_preserves_injective_linearMap a ha).comp
        (TensorProduct.assoc R B D X).symm.injective)
  let := hD
  let := KernelQuotient.finitePresentation C g
  exact ⟨{
    coordinateAlgebra := D
    finite := inferInstance
    projective := Module.Flat.projective_of_finitePresentation
    represents := KernelTorsor.quotientRepresents C hfg }⟩

end Langlands.FormalGroup.ModuleLaw.Hom
