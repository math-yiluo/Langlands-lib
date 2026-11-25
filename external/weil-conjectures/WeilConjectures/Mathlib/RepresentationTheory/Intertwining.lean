/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RepresentationTheory.Intertwining
public import WeilConjectures.RepresentationTheory.Filtration

/-!
# Equivalences of representations: tensor products, homs and duals

Congruence of the representation `linHom ρ σ` on linear maps along equivalences of
representations, the bidual `ρ ≅ ρ^∨∨` of a finite-dimensional
representation, and the identification `ρ^∨ ⊗ σ ≅ Hom(ρ, σ)` given by `dualTensorHom`. Together
they identify `ρ ⊗ σ` with `Hom(ρ', σ)` for any representation `ρ'` equivalent to the
contragredient `ρ^∨` (`Representation.Equiv.tprodEquivLinHomOfDual`).
-/

@[expose] public section

namespace Representation

variable {k G V V' W W' : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup V'] [Module k V'] [AddCommGroup W] [Module k W] [AddCommGroup W']
  [Module k W'] {ρ : Representation k G V} {ρ' : Representation k G V'}
  {σ : Representation k G W} {σ' : Representation k G W'}

namespace Equiv

lemma map_apply (e : ρ.Equiv ρ') (g : G) (v : V) : e (ρ g v) = ρ' g (e v) :=
  LinearMap.congr_fun (e.isIntertwining' g) v

lemma symm_map_apply (e : ρ.Equiv ρ') (g : G) (v : V') : e.symm (ρ' g v) = ρ g (e.symm v) :=
  e.symm.map_apply g v

/-- The representation on linear maps `Hom(ρ, σ)` is functorial in equivalences: `f ↦ e₂ ∘ f ∘
e₁⁻¹`. -/
noncomputable def linHomCongr (e₁ : ρ.Equiv ρ') (e₂ : σ.Equiv σ') :
    (linHom ρ σ).Equiv (linHom ρ' σ') :=
  .mk (e₁.toLinearEquiv.arrowCongr e₂.toLinearEquiv) fun g ↦ LinearMap.ext fun f ↦
    LinearMap.ext fun v ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, linHom_apply,
        LinearEquiv.arrowCongr_apply]
      exact (e₂.map_apply g _).trans (congrArg _ (congrArg _ (congrArg _
        (e₁.symm_map_apply g⁻¹ v).symm)))

end Equiv

variable (ρ σ)

/-- A finite-dimensional representation is equivalent to its bidual. -/
noncomputable def dualDualEquiv [FiniteDimensional k V] : ρ.Equiv ρ.dual.dual :=
  .mk (Module.evalEquiv k V) fun g ↦ LinearMap.ext fun v ↦ LinearMap.ext fun φ ↦ by
    simp [dual_apply, Module.Dual.transpose_apply]

/-- The identification `ρ^∨ ⊗ σ ≅ Hom(ρ, σ)` of representations, for a finite-dimensional `ρ`,
given by `dualTensorHom`. -/
noncomputable def dualTensorHomEquiv [FiniteDimensional k V] :
    (ρ.dual.tprod σ).Equiv (linHom ρ σ) :=
  .mk (_root_.dualTensorHomEquiv k V W) fun g ↦ by
    rw [tprod_apply]
    exact dualTensorHom_comm ρ σ g

variable {ρ σ}

/-- The tensor product `ρ ⊗ σ` of a finite-dimensional representation `ρ` with `σ` is the
representation on `Hom(ρ', σ)`, for a representation `ρ'` equivalent to the contragredient of
`ρ`. -/
noncomputable def Equiv.tprodEquivLinHomOfDual [FiniteDimensional k V] (b : ρ'.Equiv ρ.dual) :
    (ρ.tprod σ).Equiv (linHom ρ' σ) :=
  ((Equiv.tprodCongr (dualDualEquiv ρ) (.refl σ)).trans (dualTensorHomEquiv ρ.dual σ)).trans
    (Equiv.linHomCongr b.symm (.refl σ))

end Representation
