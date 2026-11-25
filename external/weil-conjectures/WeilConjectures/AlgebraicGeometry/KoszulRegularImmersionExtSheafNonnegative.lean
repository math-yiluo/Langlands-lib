/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.LinearAlgebra.Dimension.Finrank
import WeilConjectures.AlgebraicGeometry.ClosedImmersionExtIdealAction
import WeilConjectures.AlgebraicGeometry.KoszulRegularImmersionExtPullback
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitKernel

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

open MonoidalCategory in
private theorem closedImmersion_unit_isIso_of_idealAction_eq_zero
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] (F : Y.Modules)
    (hF : i.ker.toModulesι ▷ F ≫ (λ_ F).hom = 0) :
    let adj := Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction i)
    IsIso (adj.unit.app F) := by
  let adj := Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction i)
  let μ : i.ker.toModules ⊗ F ⟶ F := i.ker.toModulesι ▷ F ≫ (λ_ F).hom
  obtain ⟨hepi, w, ⟨hk⟩⟩ := Scheme.Modules.closedImmersion_unit_kernel i F
  have hι : image.ι μ = 0 := by
    apply (cancel_epi (factorThruImage μ)).mp
    simpa only [image.fac, comp_zero] using hF
  have : Epi (adj.unit.app F) := hepi
  have : Mono (adj.unit.app F) := by
    apply Preadditive.mono_of_cancel_zero
    intro T a ha
    obtain ⟨b, hb⟩ := KernelFork.IsLimit.lift' hk a ha
    change b ≫ image.ι μ = a at hb
    exact hb.symm.trans
      ((congrArg (fun c : image μ ⟶ F ↦ b ≫ c) hι).trans (comp_zero))
  exact isIso_of_mono_of_epi (adj.unit.app F)

/-- In nonnegative degree, the scalar Ext sheaf is the direct image of the determinant
on the degree-q rank stratum. This identifies sheaves, without reconstructing a derived object.

Source: Stacks Project, Tag 0BQZ, proof of Lemma 48.15.5
(blueprint: lem-sc-koszul-regular-immersion-ext-sheaf-nonnegative).

Proof:
1. Near each point of Z choose an affine chart with a Koszul-regular sequence
   generating the immersion ideal. The quotient-spectrum description of a closed
   immersion identifies the pushforward structure sheaf with the tilde of A/I.
   The local Koszul resolution in koszulRegular_closedImmersion_perfect provides
   its finite free model; extend the chain complex to integer cochain degrees.
2. Restrict derived internal Hom to this chart using
   derivedInternalHom_restrict_open. The finite free model computes it by
   derivedInternalHom_of_boundedAbove_finiteFree, with target O in degree zero.
   Sheaf Hom of finite free tilde modules agrees with tilde of module Hom.
3. Apply koszul_conormal_comparison_cohomology to the affine dual Koszul complex.
   Its only surviving cohomology is the dual conormal determinant in degree equal
   to the sequence length. The Koszul conormal basis identifies this length with
   the stalk finrank in hr. Shrink around the chosen point to the constant-rank
   stratum if necessary. Identify I/I² with the pullback of the immersion ideal,
   and its dual and determinant with the sheaf Hom and exterior sheaf in the goal.
4. On overlaps compare on smaller affine standard opens. The normalized affine
   comparison is independent of generators and commutes with localization, by
   koszul_conormal_comparison_change_generators and
   koszul_conormal_comparison_localization. Thus the cohomology-sheaf maps and
   their inverses agree and glue. Off the closed image the first argument is zero,
   so derived Hom and all its cohomology vanish. Only the rank-q stratum contributes
   in the specified nonnegative degree. Clopen direct image
   extends its determinant by zero, giving precisely locallyRankedExteriorTerm.
The zero-length sequence gives degree zero; an empty source gives zero everywhere.
No global boundedness, Noetherian hypothesis, or finite-image condition is used. -/
theorem koszulRegularImmersion_extSheaf_nonnegative
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (hregular : ∀ z : Z, ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (n : ℕ) (f : Fin n → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f)
    (r : LocallyConstant Z ℕ)
    (hr : ∀ z : Z, r z = Module.finrank (Z.presheaf.stalk z)
      ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)))
    {q : ℤ} (hq : 0 ≤ q) :
    Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) q).obj
        ((derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))),
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
                (SheafOfModules.unit Y.ringCatSheaf))) ≅
      (Scheme.Modules.pushforward i).obj
        (Scheme.Modules.locallyRankedExteriorTerm
          (SheafOfModules.homObj (R := Z.sheaf)
            ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
            (SheafOfModules.unit Z.ringCatSheaf)) r q)) := by
  open MonoidalCategory in
  let F : Y.Modules := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) q).obj
        ((derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))),
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
                (SheafOfModules.unit Y.ringCatSheaf)))
  let adj := Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction i)
  have hF : i.ker.toModulesι ▷ F ≫ (λ_ F).hom = 0 :=
    closedImmersion_ext_idealAction_eq_zero i q
  have : IsIso (adj.unit.app F) :=
    closedImmersion_unit_isIso_of_idealAction_eq_zero i F hF
  obtain ⟨e⟩ := koszulRegularImmersion_ext_pullback i hregular r hr hq
  exact ⟨asIso (adj.unit.app F) ≪≫ (Scheme.Modules.pushforward i).mapIso e⟩


end AlgebraicGeometry
