import Langlands.AlgebraicGeometry.SmoothValuationStalkPicard
import Langlands.AlgebraicGeometry.Picard.LineBundleInverse
import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Actual affine line-bundle trivializations from module Picard vanishing -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.Picard

variable {X : Scheme.{u}}

private theorem portedIsInvertible (L : LineBundle X) :
    Scheme.Modules.IsInvertible L.obj :=
  ⟨fun x => by
    obtain ⟨U, hx, ⟨e⟩⟩ := L.property x
    exact ⟨U, hx, ⟨((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L.obj).symm ≪≫ e⟩⟩⟩

/-- The ported monoidal tensor and the explicit tensor are both the
sheafification of the same sectionwise tensor product. -/
def portedTensorExplicitIso (M N : X.Modules) :
    Scheme.Modules.tensor M N ≅ Langlands.Scheme.Modules.tensorObj M N :=
  (Scheme.Modules.tensorIsoSheafify M N).symm

/-- Sections of a line bundle on an affine scheme are an invertible module
over the actual ring of global functions. -/
theorem invertible_sections_of_lineBundle (L : LineBundle X) [IsAffine X] :
    Module.Invertible Γ(X, ⊤) Γ(L.obj, ⊤) := by
  let N := L.inverse
  let t : Γ(L.obj, ⊤) ⊗[Γ(X, ⊤)] Γ(N.obj, ⊤) ≃ₗ[Γ(X, ⊤)]
      Γ(Scheme.Modules.tensor L.obj N.obj, ⊤) :=
    LinearEquiv.ofBijective
      (TensorProduct.lift (Scheme.Modules.tensorSectionsBilin L.obj N.obj ⊤))
      ((portedIsInvertible L).bijective_lift_tensorSectionsBilin_monoidalV2
        (portedIsInvertible N) ⟨⊤, isAffineOpen_top X⟩)
  let e : Scheme.Modules.tensor L.obj N.obj ≅
      SheafOfModules.unit X.ringCatSheaf :=
    portedTensorExplicitIso L.obj N.obj ≪≫ L.tensorInverseIso
  let a := ((SheafOfModules.evaluation X.ringCatSheaf (.op ⊤)).mapIso e).toLinearEquiv
  exact Module.Invertible.left (t ≪≫ₗ a)

/-- Global sections of a line bundle on `Spec R` have an actual rank-one
module basis whenever the module Picard group of `R` is trivial. -/
theorem nonempty_sections_linearEquiv_of_pic_trivial
    {R : CommRingCat.{u}} [Subsingleton (CommRing.Pic R)]
    (L : LineBundle (Spec R)) :
    Nonempty ((moduleSpecΓFunctor.obj L.obj) ≃ₗ[R] R) := by
  have : Subsingleton (CommRing.Pic Γ(Spec R, ⊤)) :=
    Langlands.CommutativeAlgebra.subsingleton_pic_of_ringEquiv
      (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  have : Module.Invertible Γ(Spec R, ⊤) Γ(L.obj, ⊤) :=
    invertible_sections_of_lineBundle L
  obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv.mp
    (CommRing.Pic.subsingleton_iff.mp
      (inferInstance : Subsingleton (CommRing.Pic Γ(Spec R, ⊤)))
      Γ(L.obj, ⊤) (invertible_sections_of_lineBundle L))
  let a : R ≃ₗ[R] Γ(Spec R, ⊤) :=
    LinearEquiv.ofBijective (Algebra.linearMap R Γ(Spec R, ⊤))
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv)
  exact ⟨e.restrictScalars R ≪≫ₗ a.symm⟩

/-- The actual associated-sheaf equivalence turns the module basis into
an isomorphism of the given sheaf with the structure sheaf. -/
theorem nonempty_lineBundle_iso_structureSheaf_of_pic_trivial
    {R : CommRingCat.{u}} [Subsingleton (CommRing.Pic R)]
    (L : LineBundle (Spec R)) :
    Nonempty (L.obj ≅ SheafOfModules.unit (Spec R).ringCatSheaf) := by
  obtain ⟨e⟩ := nonempty_sections_linearEquiv_of_pic_trivial L
  exact ⟨(asIso L.obj.fromTildeΓ).symm ≪≫
    (tilde.functor R).mapIso e.toModuleIso ≪≫ tildeSelf⟩

/-- Choose an actual trivialization of a line bundle on an affine spectrum
whose module Picard group is trivial. -/
def affineLineBundleTrivialization
    {R : CommRingCat.{u}} [Subsingleton (CommRing.Pic R)]
    (L : LineBundle (Spec R)) :
    L.obj ≅ SheafOfModules.unit (Spec R).ringCatSheaf :=
  (nonempty_lineBundle_iso_structureSheaf_of_pic_trivial L).some

end Langlands.AlgebraicGeometry.Picard
