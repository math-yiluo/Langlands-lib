import Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule
import Langlands.AlgebraicGeometry.Modules.CechHSuccBridge
import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent

/-! # Exactness of the Čech model in degree one from vanishing `H¹`

If the base change of a line bundle `L` to `Y_A` has vanishing `H¹`, then the Čech projective
representative of `L` is exact at `A ⊗ K₁`: a cocycle of `A ⊗ K₁` maps to a Čech `1`-cocycle,
which is a coboundary since Čech `H¹` is actual `H¹`, hence it comes from `A ⊗ K₀`. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule

open Scheme.TwoAffineOpenCover

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)} [IsSeparated π]
  {L : LineBundle X} {𝒰 : X.OrderedAffineCover} (C : CechRep π L.obj 𝒰)

/-- **Vanishing `H¹` after base change makes the Čech model exact at `A ⊗ K₁`.** -/
theorem exact_of_isZero_H1 (A : Type u) [CommRing A] [Algebra R A]
    (h : IsZero ((Modules.DerivedSections.relativeCohomology (pullback.snd π (specMap R A)) 1).obj
      ((Scheme.Modules.pullback (pullback.fst π (specMap R A))).obj L.obj)))
    (x : A ⊗[R] C.K₁) (hx : C.δ₁.lTensor A x = 0) :
    x ∈ LinearMap.range (C.δ.lTensor A) := by
  have hx' : C.δ₁.baseChange A x = 0 := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact hx
  have hcoc := C.Θ₁_cocycle A x hx'
  have : ((Scheme.Modules.pullback (pullback.fst π (specMap R A))).obj L.obj).IsQuasicoherent :=
    L.property.isQuasicoherent_pullback _
  let e := Modules.CechBridge.hsuccEquivRelativeCohomology (π := pullback.snd π (specMap R A))
    (𝒰.baseChange π A) ((Scheme.Modules.pullback (pullback.fst π (specMap R A))).obj L.obj) 0
  have hsub : Subsingleton ((baseChangePresheaf π L.obj A).HSucc (𝒰.baseChange π A) 0) := by
    have := ModuleCat.subsingleton_of_isZero h
    exact e.toEquiv.subsingleton
  have hmem : C.Θ₁ A x ∈
      LinearMap.range ((baseChangePresheaf π L.obj A).d (𝒰.baseChange π A) 0) := by
    have h0 := Subsingleton.elim
      (Submodule.Quotient.mk (⟨C.Θ₁ A x, hcoc⟩ :
        LinearMap.ker ((baseChangePresheaf π L.obj A).d (𝒰.baseChange π A) (0 + 1))) :
          (baseChangePresheaf π L.obj A).HSucc (𝒰.baseChange π A) 0) 0
    rw [Submodule.Quotient.mk_eq_zero] at h0
    exact h0
  obtain ⟨z, hz⟩ := C.Θ₁_exact A x hx' hmem
  refine ⟨z, ?_⟩
  rw [← hz, LinearMap.baseChange_eq_ltensor]

end Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule
