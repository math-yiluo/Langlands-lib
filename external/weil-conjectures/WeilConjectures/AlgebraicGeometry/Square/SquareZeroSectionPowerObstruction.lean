/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import WeilConjectures.AlgebraicGeometry.Square.SquareZeroSectionPowerLiftingCriterion
import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-! # Square-zero section-power obstruction

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS.
(blueprint: lem-sc-square-zero-section-power-obstruction).
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
universe u

/-- A section has a quasi-coherent degree-one obstruction on the closed subscheme.
If a tensor power of the section kills it, the next power lifts. No affine-open
hypothesis is needed to construct the obstruction or establish this implication.

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS, equation (30.17.5.1),
and Cohomology, Lemma 0B8S.
(blueprint: lem-sc-square-zero-section-power-obstruction).

Proof: Tensor the ideal sequence by L^d, which is invertible, to obtain an exact
sequence with kernel I tensor L^d and quotient j_*j^*(L^d). The kernel is killed
by I, since I^2=0. Identify it with the pushforward of its pullback using the
annihilated-module theorem. The affine-morphism edge isomorphism identifies its
H^1 with H^1 on Z. Take F=j^*(I tensor L^n), which is quasi-coherent, and take xi
to be the boundary of s under this identification. Form the direct sum of the
sequences over d. Local frames of L identify the resulting graded algebra with
a polynomial algebra, so it is commutative and its kernel is square zero.
The boundary derivation theorem and induction give boundary(s^(e+1)) =
(e+1) s^e xi. Inclusion and projection of graded summands identify this with
the degree n*(e+1) boundary. Naturality of the edge isomorphism identifies the
s^e action with the displayed H^1 map. Its vanishing therefore makes the
boundary zero. Exactness supplies a global lift t. Iterated tensor-pullback
comparisons (including the unit comparison when n=0) give a, and identify
restriction of t followed by a with the pure tensor power of s. -/
theorem exists_square_zero_section_power_obstruction
    {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j]
    (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) (s : (((tensorPullback j).obj L).tensorPow n).val.presheaf.obj
      (Opposite.op ⊤)) :
    let F := (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)
    F.IsQuasicoherent ∧ ∃ (xi : (RingedSpace.moduleCohomology Z.toRingedSpace 1).obj F),
      ∀ e : ℕ, (RingedSpace.moduleCohomology Z.toRingedSpace 1).map
        ((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection
          (((tensorPullback j).obj L).tensorPow n) s) e) xi = 0 →
      ∃ t : (L.tensorPow (n * (e + 1))).val.presheaf.obj (Opposite.op ⊤),
        ∃ a : (tensorPullback j).obj (L.tensorPow (n * (e + 1))) ≅
            (((tensorPullback j).obj L).tensorPow n).tensorPow (e + 1),
          homOfGlobalSection ((tensorPullback j).obj (L.tensorPow (n * (e + 1))))
              (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
                (L.tensorPow (n * (e + 1)))).val.app (Opposite.op ⊤) t) ≫ a.hom =
            tensorPowSection (homOfGlobalSection
              (((tensorPullback j).obj L).tensorPow n) s) (e + 1) := by
  dsimp only
  constructor
  · have := SheafOfModules.isQuasicoherent_unit (R := j.ker.subscheme.ringCatSheaf)
    have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
    have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
        ((SheafOfModules.pushforward j.ker.subschemeι.toRingCatSheafHom).obj
          (SheafOfModules.unit j.ker.subscheme.ringCatSheaf)) :=
      isQuasicoherent_pushforward_of_isClosedImmersion j.ker.subschemeι _
    have : j.ker.toModules.IsQuasicoherent :=
      isQuasicoherent_kernel j.ker.toPushforwardSubscheme
    have : (j.ker.toModules ⊗ L.tensorPow n).IsQuasicoherent :=
      isQuasicoherent_tensorObj _ _
    let a : tensorPullback j ≅ pullback j :=
      (Classical.choose (exists_tensorPullbackAdjunction j)).leftAdjointUniq
        (pullbackPushforwardAdjunction j)
    exact (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso
      (a.app _).symm (inferInstance : ((pullback j).obj _).IsQuasicoherent)
  · exact square_zero_section_power_obstruction_core j L hI n s

end AlgebraicGeometry.Scheme.Modules
