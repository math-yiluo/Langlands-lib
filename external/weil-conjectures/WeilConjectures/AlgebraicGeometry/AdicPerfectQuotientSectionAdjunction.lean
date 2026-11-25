/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.AdicShortComplexCohomologyML
public import WeilConjectures.AlgebraicGeometry.AdicPerfectModuleFunctors
import WeilConjectures.AlgebraicGeometry.AdicPerfectQuotientSectionComparison

/-! # Quotient realization and its section adjunction

Source: Stacks Project, Modules on Sites, Tags 03CY and 03EK; Tag 09C6.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] derivedExtension extend change
  adicPerfectQuotientFunctor adicPerfectQuotientModuleStep
  AdicQuotientSections.rightAdjoint AdicQuotientSections.adjunction
  AdicQuotientSections.step

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The ordinary quotient realization is left adjoint to sections with algebraic
A-scalars. Its value followed by sections is constant-module sections of the algebraic
quotient. These identifications respect the successor quotient and the adjunction units.
Source: Stacks Project, Modules on Sites, Tags 03CY and 03EK, and proetale.tex,
Tag 09C6, the ordinary quotient calculation before the total-Hom calculation.
(auxiliary; not a blueprint node).

Proof: write T for the slice site and B_n for the restriction of the constant ring
A/J^(n+1). Define R_n on a B_n-module sheaf by its sections at the terminal object,
with A-action through A -> A/J^(n+1) -> B_n(terminal). A map out of the constant
A-module sheaf is determined by the corresponding A-linear map on terminal sections:
use the constant-presheaf adjunction followed by module sheafification. Tensor
extension is left adjoint to restriction of scalars. The ordinary scalar balancing
isomorphism and restriction to the slice therefore identify the given F_n with the
left adjoint of R_n. The completion cone equation says that the composite of the
coefficient map with the nth projection is the constant quotient map. Consequently
F_n(M) is the constant sheaf of (A/J^(n+1)) tensor_A M, restricted to T. Identify this
algebraic tensor with M/(J^(n+1) M). Constant module sheafification commutes with
restriction to T and with forgetting the quotient-ring scalars. This gives the
natural isomorphism e_n from H_n to F_n followed by R_n.

For kappa_n take insertion s -> 1 tensor s into change of scalars from B_(n+1) to B_n,
then terminal sections. It is A-linear because the two maps from A into B_n agree,
and natural because insertion is natural. The adjunction unit sends m to the
constant generator 1 tensor (1 tensor m). The fixed balancing isomorphism multiplies
adjacent scalar factors, so kappa followed by that isomorphism sends the unit at
level n+1 to the unit at level n. This is the first equation. For the second,
e_n sends a locally constant quotient class of m to its same tensor generator.
Both sides therefore send a constant class of m modulo J^(n+2) to its generator
modulo J^(n+1). Sheafification uniqueness gives equality on all locally constant
sections. These calculations also apply to zero modules, the zero ring, the unit
ideal and a slice with zero coefficient sheaf. No finiteness or Noetherian
hypothesis enters this ordinary tensor calculation. -/
theorem adicPerfectQuotientSectionAdjunction (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) :
    let G := AdicCohomology.sections
      ((coefficientProEtaleModelTopology.{u, v} X).over U) (Over.mk (𝟙 U))
    let H := fun n : ℕ ↦ AdicCohomology.quotient J (n + 1) ⋙ G
    let F := fun n : ℕ ↦ adicPerfectQuotientFunctor X J U n
    ∃ (R : ∀ n : ℕ,
        Mod ((finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U) ⥤
          ModuleCat.{max v (u + 1)} A)
      (a : ∀ n : ℕ, F n ⊣ R n)
      (e : ∀ n : ℕ, H n ≅ F n ⋙ R n)
      (κ : ∀ n : ℕ, R (n + 1) ⟶
        change (adicPerfectQuotientScalarStep X J U n) ⋙ R n),
      (∀ (n : ℕ) (M : ModuleCat.{max v (u + 1)} A),
        (a n).unit.app M = (a (n + 1)).unit.app M ≫
          (κ n).app ((F (n + 1)).obj M) ≫
            (R n).map ((adicPerfectQuotientModuleStep X J U n).hom.app M)) ∧
      (∀ (n : ℕ) (M : ModuleCat.{max v (u + 1)} A),
        G.map ((AdicCohomology.transition J
          (Nat.add_le_add_right (Nat.le_succ n) 1)).app M) ≫ (e n).hom.app M =
          (e (n + 1)).hom.app M ≫ (κ n).app ((F (n + 1)).obj M) ≫
            (R n).map ((adicPerfectQuotientModuleStep X J U n).hom.app M)) := by
  obtain ⟨e, he⟩ := adicPerfectQuotientSectionComparison X J U
  exact ⟨AdicQuotientSections.rightAdjoint X J U,
    AdicQuotientSections.adjunction X J U, e, AdicQuotientSections.step X J U,
    AdicQuotientSections.step_unit X J U, he⟩

end AlgebraicGeometry.Scheme
