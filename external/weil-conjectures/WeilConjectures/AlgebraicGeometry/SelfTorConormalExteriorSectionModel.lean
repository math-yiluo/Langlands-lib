/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SelfTorAffineSection
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
import WeilConjectures.AlgebraicGeometry.SelfTorConormalExteriorTensor
import WeilConjectures.AlgebraicGeometry.SelfTorAffineTensorSections

/-! # The algebraic exterior of conormal sections and the affine model

Source: Stacks Project, Tags 01R3(2), 01I6, and 0096.
(blueprint: new-q1-self-tor-conormal-exterior-section-model). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- Exterior powers of actual conormal sections identify with sections of the
pulled-back affine conormal exterior module. This statement does not use the
exterior sheaf or its sheafification.
Source: Stacks Project, Tag 01R3(2); Tag 01I6, Lemmas 26.7.1 and 26.7.3(1);
Tag 0096 for the pullback unit.
(blueprint: new-q1-self-tor-conormal-exterior-section-model).
Proof: Put A = Gamma(Y,U), I = ker(i).ideal(U), V = i inverse-image U,
and B = Gamma(Z,V). The closed immersion identifies B with A/I.
Apply affine_conormal_sections with R=A, r the identity, and I the kernel
ideal. Its equation identifies every pullback-unit ideal section with its
class in I/I squared. Its A-linearity is B-linearity: lift each scalar of
B through the surjection A to B and apply A-linearity. Exterior functoriality
then identifies the exterior B-module of N(V) with the exterior A/I-module
of I/I squared and sends the displayed pure wedges to selfTorIdealWedge.
On V, the restriction of the pushforward from U cancels with restriction
to U, and tensor pullback of the associated module M is associated to
B tensor_A M. Because I annihilates M, the map b tensor m to b*m identifies
this tensor product with M, with inverse m to 1 tensor m. The tilde unit
and tensor-pullback unit yield exactly selfTorAffineSection, by naturality
of the adjunction units. Compose the two identifications. In degree zero
the map is the ring identification sending the empty wedge to 1; for an
empty V both sides are zero. No regularity or finite-generation is needed. -/
theorem exists_selfTor_conormal_exterior_section_model
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (n : ℕ) (U : Y.affineOpens) :
    let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
    let M := conormalExteriorModule (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
      Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
    ∃ e : (⋀[Z.presheaf.obj (op (i ⁻¹ᵁ U.1))]^n
        (N.val.obj (op (i ⁻¹ᵁ U.1)))) ≃ₗ[Z.presheaf.obj (op (i ⁻¹ᵁ U.1))]
        (T.obj M).val.obj (op (i ⁻¹ᵁ U.1)),
      ∀ b : Fin n → i.ker.toModules.val.obj (op U.1),
        e (exteriorPower.ιMulti (Z.presheaf.obj (op (i ⁻¹ᵁ U.1))) n
          (fun j ↦ ((Classical.choose
            (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
              i.ker.toModules).val.app (op U.1) (b j))) =
          selfTorAffineSection i U M (selfTorIdealWedge i U n b) := by
  let : Algebra Γ(Y, U.1) Γ(Z, i ⁻¹ᵁ U.1) := (i.app U.1).hom.toAlgebra
  let M := conormalExteriorModule (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
  obtain ⟨e₁, h₁⟩ := exists_selfTor_conormal_exterior_tensor i n U
  obtain ⟨e₂, h₂⟩ := exists_selfTor_affine_tensor_sections i U M
  refine ⟨e₁.trans e₂, ?_⟩
  intro b
  change e₂ (e₁ _) = _
  rw [h₁ b, h₂, one_smul]

end AlgebraicGeometry
