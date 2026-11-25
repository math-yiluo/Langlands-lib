/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.Algebra.Homology.KFlatPullback
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived
import WeilConjectures.AlgebraicGeometry.AffineAlgebraStalkFlat
import WeilConjectures.AlgebraicGeometry.StalkFlatTensorPullbackKernels
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-! # Exact tensor pullback to an affine morphism's direct-image algebra

Source: Stacks Project, Derived Categories of Schemes, Tag 0AVW, proof
(blueprint: lem-sc-affine-algebra-tensor-pullback-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The underived tensor pullback to the direct-image algebra of an affine
morphism is exact, with its action specified on objects and morphisms.
Source: Stacks Project, Tag 0AVW, Lemma 36.5.4, stalk calculation in the proof
(blueprint: lem-sc-affine-algebra-tensor-pullback-exact).

Proof: Work over an affine open Spec B of Y; its inverse image is Spec A
because f is affine. At x corresponding to p in Spec A, let q be its image
in Spec B. The stalk of f_*O_X at q is the localization of A at the images
of B minus q. The stalk O_X,x is A_p. None of those images lies in p, and
A_p is a further localization of A_q. Thus O_X,x is flat over (f_*O_X)_q.
The stalk of the displayed tensor pullback is O_X,x tensor over
(f_*O_X)_q with the stalk of the input module; the specified morphism formula
identifies its maps with tensor products of the stalk maps. Localization is
flat, so this functor takes short exact sequences to short exact sequences
at every stalk. Stalks detect exactness of sheaves. The affine opens cover Y,
and their inverse images cover X, proving exactness globally. In abelian
module-sheaf categories an additive exact functor preserves finite limits
and finite colimits; the tensor formula is additive. This applies to all
module sheaves, without a quasi-coherence or boundedness assumption. -/
theorem affine_algebra_tensorModulePullback_exact
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (P : SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (h : ∀ M, P.obj M = SheafOfModules.changeOfRings.{u, u, u}
      (CochainComplex.tensorPullbackRingMap
        (toDirectImageAlgebraSpace f).hom.base X.toRingedSpace.sheaf
        (directImageAlgebraSpace f).sheaf ⟨(toDirectImageAlgebraSpace f).hom.c⟩)
      (TopCat.Sheaf.inverseImageModule (toDirectImageAlgebraSpace f).hom.base
        (directImageAlgebraSpace f).sheaf M))
    (hm : ∀ {M N} (a : M ⟶ N),
      P.map a = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom.{u, u, u}
        (CochainComplex.tensorPullbackRingMap
          (toDirectImageAlgebraSpace f).hom.base X.toRingedSpace.sheaf
          (directImageAlgebraSpace f).sheaf ⟨(toDirectImageAlgebraSpace f).hom.c⟩)
        (TopCat.Sheaf.inverseImageModule (toDirectImageAlgebraSpace f).hom.base
          (directImageAlgebraSpace f).sheaf M)
        (TopCat.Sheaf.inverseImageModuleMap (toDirectImageAlgebraSpace f).hom.base
          (directImageAlgebraSpace f).sheaf M a) ≫ eqToHom (h N).symm) :
    PreservesFiniteLimits P ∧ PreservesFiniteColimits P := by
  obtain ⟨Q, hQ, hmQ, hadd, ⟨adj⟩⟩ :=
    RingedSpace.exists_tensorModulePullback (toDirectImageAlgebraSpace f)
  let e : P ≅ Q := NatIso.ofComponents
    (fun M ↦ eqToIso ((h M).trans (hQ M).symm)) (by
      intro M N a
      dsimp only [eqToIso]
      rw [hm, hmQ]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans])
  let : Q.Additive := hadd
  let : Q.IsLeftAdjoint := adj.isLeftAdjoint
  let : P.Additive := Functor.additive_of_iso e.symm
  let : PreservesFiniteColimits P := preservesFiniteColimits_of_natIso e.symm
  have {M N : SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))}
      (a : M ⟶ N) : PreservesLimit (parallelPair a 0) P :=
    RingedSpace.stalkFlat_tensorModulePullback_preservesKernels
      (toDirectImageAlgebraSpace f)
      (fun x ↦ affine_algebra_stalkMap_flat f x) P h hm a
  exact ⟨Functor.preservesFiniteLimits_of_preservesKernels P, inferInstance⟩

end AlgebraicGeometry
