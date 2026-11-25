/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DiagonalConormal
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import WeilConjectures.AlgebraicGeometry.DiagonalConormalMorphism

/-!
# The difference derivation into the diagonal conormal

Source: Stacks Project, Tag 08S2, construction of the two splittings modulo the square
of the diagonal ideal, before the affine calculation.
(blueprint: lem-sc-diagonal-conormal-derivation-exists).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- A derivation into the diagonal conormal has the prescribed difference formula if,
whenever the two projections pull a section `a` back to an ambient open `W`, its value
is the tensor-pullback class of their difference. The kernel section `s` is specified by
its image under the kernel inclusion. This uses the canonical tensor-pullback unit.
Source: Stacks Project, Tag 08S2, the derivation `s₂ - s₁`.
(blueprint: lem-sc-diagonal-conormal-derivation-exists). -/
def IsDiagonalConormalDerivation (f : X ⟶ S)
    (D : (diagonalConormal f).val.Derivation' f.pullbackPresheafToPresheaf) : Prop :=
  let δ := pullback.diagonal f
  let I := kernel (SheafOfModules.unitToPushforwardObjUnit δ.toRingCatSheafHom)
  ∀ (U : X.Opens) (W : (pullback f f).Opens)
    (h₁ : W ≤ (pullback.fst f f) ⁻¹ᵁ U) (h₂ : W ≤ (pullback.snd f f) ⁻¹ᵁ U)
    (hδ : U ≤ δ ⁻¹ᵁ W) (a : Γ(X, U)) (s : Γ(I, W)),
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit δ.toRingCatSheafHom)).val.app
      (op W) s = (pullback.snd f f).appLE U W h₂ a -
        (pullback.fst f f).appLE U W h₁ a →
    D.d (X := op U) a = (diagonalConormal f).presheaf.map (homOfLE hδ).op
      (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction δ)).unit.app I).val.app
        (op W) s)

/-- The difference of the two projections defines a relative derivation into the
conormal sheaf, with its sectionwise difference formula.
Source: Stacks Project, Tag 08S2, global construction preceding the affine calculation.
(blueprint: lem-sc-diagonal-conormal-derivation-exists).
Proof: restrict the actual kernel ideal to the neighbourhood of the diagonal in Tag 01KJ.
Modulo its square, inverse image along the diagonal gives a square-zero extension of
`O_X` by the conormal. Both projections split its quotient onto `O_X`. Their difference
lies in the kernel and satisfies the Leibniz rule: the error term is a product of two
kernel sections and vanishes modulo the square. The projections agree on functions
from the base, so the difference is relative to `f`. These constructions commute with
restriction and therefore define a sheaf derivation. Identify the square-zero kernel
with tensor pullback of the ideal: on a closed-immersion chart this is `I/I²`, and its
class map is the canonical tensor-pullback unit. This gives the displayed normalization
on every ambient open `W`; equality can be checked locally on the same charts. -/
theorem exists_diagonalConormalDerivation (f : X ⟶ S) :
    ∃ D : (diagonalConormal f).val.Derivation' f.pullbackPresheafToPresheaf,
      IsDiagonalConormalDerivation f D := by
  obtain ⟨φ, hφ⟩ := exists_diagonalConormalMorphism f
  refine ⟨f.relativeDifferentialsDerivation.postcomp φ.val, ?_⟩
  dsimp [IsDiagonalConormalDerivation]
  intro U W h₁ h₂ hδ a s hs
  exact hφ U W h₁ h₂ hδ a s hs

end AlgebraicGeometry
