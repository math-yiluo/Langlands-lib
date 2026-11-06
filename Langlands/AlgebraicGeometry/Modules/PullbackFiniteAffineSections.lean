import Langlands.AlgebraicGeometry.Modules.CoherentLineBundle
import Langlands.AlgebraicGeometry.Modules.PullbackAffineSections
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Pullback preserves finite affine sections -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.Modules

namespace AffineSections

/-- The actual sections of a quasi-coherent pullback on an affine open are the
scalar extension of sections on any affine open containing its image. -/
def pullbackEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [M.IsQuasicoherent] {U : X.Opens} {V : Y.Opens} (h : U ≤ f ⁻¹ᵁ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    ((ModuleCat.extendScalars (f.appLE V U h).hom).obj
      (ModuleCat.of Γ(Y, V) Γ(M, V))) ≃ₗ[Γ(X, U)]
        Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, U) :=
  LinearEquiv.ofBijective (Langlands.Scheme.Modules.pullbackTensorMap f M h).hom
    (Langlands.Scheme.Modules.pullbackTensorMap_bijective f M h hU hV)

end AffineSections

namespace HasFiniteAffineSections

/-- Pullback of a quasi-coherent module preserves finite generation of affine sections. -/
lemma pullbackObj {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    [M.IsQuasicoherent] (hM : HasFiniteAffineSections M) :
    HasFiniteAffineSections ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M) := by
  apply HasLocallyFiniteSections.finiteAffineSections
  intro x
  obtain ⟨V, hV, hxV, -⟩ :=
    (Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens)
      (show f x ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUV⟩ :=
    (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
      (show x ∈ f ⁻¹ᵁ V from hxV)
  let := hM ⟨V, hV⟩
  let := (f.appLE V U hUV).hom.toAlgebra
  have : Module.Finite Γ(X, U)
      ((ModuleCat.extendScalars (f.appLE V U hUV).hom).obj
        (ModuleCat.of Γ(Y, V) Γ(M, V))) := by
    change Module.Finite Γ(X, U) (TensorProduct Γ(Y, V) Γ(X, U) Γ(M, V))
    infer_instance
  exact ⟨U, hU, hxU, Module.Finite.equiv (AffineSections.pullbackEquiv f M hUV hU hV)⟩

end HasFiniteAffineSections

end Langlands.AlgebraicGeometry.Modules
