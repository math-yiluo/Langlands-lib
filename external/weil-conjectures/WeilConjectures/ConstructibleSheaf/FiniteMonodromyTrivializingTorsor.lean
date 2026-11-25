/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Field.ULift
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
import WeilConjectures.ConstructibleSheaf.FiniteSetMonodromyTorsor
import WeilConjectures.ConstructibleSheaf.ModuleConstantOfSetPullback
import WeilConjectures.ConstructibleSheaf.KernelCokernel

/-!
# A connected finite monodromy torsor trivializing a module sheaf

Source: Stacks Project, Tags 0DV5 (3), 0DV6 and the proof of 0A3R.
(blueprint: lem-weil-pbc-finite-monodromy-trivializing-torsor)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale

/-- A finite locally constant vector-space sheaf is constant on a connected finite
monodromy torsor. Source: Stacks Project, Tag 0DV5 (3), Tag 0DV6, and Tag 0A3R,
proof before the choice of a Sylow subgroup.
(blueprint: lem-weil-pbc-finite-monodromy-trivializing-torsor)

Proof:
1. Choose a point of the nonempty connected scheme U and an algebraic closure of
its residue field. The finite-module correspondence of 0DV5 (3) identifies G with
its finite-dimensional geometric stalk A and a continuous action of the fundamental
group. Since the coefficient field is finite, A is a finite set and its group of
linear automorphisms is finite.
2. Let Q be the image of this action. Replace Q by an isomorphic finite group in
Type u. The action factors through a continuous surjection onto Q, whose kernel
is open and normal. The Galois correspondence gives a connected finite etale
Q-torsor c over U. Transport its action along Q equiv ULift Q.
3. The fundamental group of the total space maps into the kernel. Pullback
compatibility (0DV6) makes the pulled-back representation trivial. The module
correspondence therefore identifies c*G with the constant sheaf with value A.
The stalk is finite-dimensional over ULift (ZMod l), giving the asserted instance.
For G = 0 use Q = 1, the identity torsor, and A = 0. -/
theorem Scheme.IsFiniteLocallyConstantSheaf.exists_finite_monodromy_trivializing_torsor
    {U : Scheme.{u}} [ConnectedSpace U] (ℓ : ℕ) [Fact ℓ.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    [IsFiniteLocallyConstantSheaf G] :
    ∃ (Q : Type u) (_ : Group Q) (_ : Finite Q)
      (c : Scheme.GaloisCover (ULift.{u + 1} Q) U) (_ : ConnectedSpace c.P)
      (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
      (_ : FiniteDimensional (ULift.{u + 1} (ZMod ℓ)) A),
      Nonempty ((c.π)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj G ≅
        (constantSheaf c.P.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj A) := by
  classical
  let R := ULift.{u + 1} (ZMod ℓ)
  obtain ⟨d, hd⟩ := (Scheme.finite_locally_constant_module_values_iff G).1.mpr
    (inferInstance : IsFiniteLocallyConstantSheaf G)
  have hlisse : Scheme.IsLisseModuleSheaf G := ⟨d.cover, hd⟩
  have hsets := (Scheme.lisseModuleSheaf_iff_underlying_finiteLocallyConstant G).mp hlisse
  obtain ⟨Q, hQ, hfin, c, hconn, hconstant⟩ :=
    Scheme.exists_connected_torsor_constant_set_pullback
      ((sheafForget U.smallEtaleTopology).obj G) hsets
  let := hQ
  have := hfin
  have := hconn
  have hmodule := Scheme.module_pullback_isConstant_of_set_pullback R c.π G hconstant
  have := hmodule
  obtain ⟨A, ⟨e⟩⟩ :=
    ((Etale.upperStar (ModuleCat.{u + 1} R) c.π).obj G).mem_essImage_of_isConstant
  have : IsFiniteSheaf ((Etale.upperStar (ModuleCat.{u + 1} R) c.π).obj G) :=
    IsFiniteSheaf.upperStar c.π G
  have : IsFiniteSheaf ((constantSheaf c.P.smallEtaleTopology
      (ModuleCat.{u + 1} R)).obj A) := IsFiniteSheaf.of_iso e.symm
  have : Module.Finite R A := Scheme.moduleFinite_of_isFiniteSheaf_constantSheaf (Y := c.P) A
  exact ⟨Q, hQ, hfin, c, hconn, A, inferInstance, ⟨e.symm⟩⟩

end AlgebraicGeometry
