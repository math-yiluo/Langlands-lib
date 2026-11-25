/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.IntrinsicFlatModuleTensorFlatAux
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits

/-! # Affine-local intrinsic flatness implies tensor flatness -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Intrinsic affine-local flatness of a quasi-coherent module implies tensor flatness.
Source: Stacks Project, Tags 01U4 (affine-local flatness) and 05NE (flat stalks).
(blueprint: lem-pc-intrinsic-flat-module-tensor-flat).

Proof: On an affine neighbourhood of each point, evaluate IsFlatOver at equal affine
opens. The identity ring map makes the section module flat over its own coordinate
ring. Quasi-coherence identifies the stalk with its localization, hence each stalk
is flat. Tensor products and exactness are computed on stalks, so tensoring with G
preserves short exact sequences. The argument also applies on an empty scheme and
to the zero module. -/
theorem isFlat_of_isFlatOver_identity {Y : Scheme.{u}} (G : Y.Modules)
    [SheafOfModules.IsQuasicoherent.{u} G]
    (hflat : Scheme.Modules.IsFlatOver G (𝟙 Y)) : SheafOfModules.IsFlat G :=
  open CategoryTheory.Limits MonoidalCategory in
  by
    classical
    let X := Y.toRingedSpace
    let : MonoidalCategory Y.Modules := SheafOfModules.monoidalCategory Y.sheaf
    let : SymmetricCategory Y.Modules := SheafOfModules.symmetricCategory Y.sheaf
    let S := RingedSpace.moduleStalkFunctor X
    have hst (x : X) : Module.Flat (X.presheaf.stalk x) ((S x).obj G) :=
      flat_stalk_of_affine_sections_flat G (fun V ↦ hflat V V le_rfl) x
    have hlim (x : X) : PreservesFiniteLimits (S x) := by
      let A := forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
      have : PreservesFiniteLimits (S x ⋙ A) := by
        change PreservesFiniteLimits (SheafOfModules.toSheaf _ ⋙
          (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x))
        have hb : PreservesFiniteLimits
            (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
              TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) := inferInstance
        exact comp_preservesFiniteLimits (SheafOfModules.toSheaf _) _
      exact preservesFiniteLimits_of_reflects_of_preserves (S x) A
    have hreflect : JointlyReflectIsomorphisms S := by
      constructor
      intro M N a ha
      let T := SheafOfModules.toSheaf ((sheafCompose
        (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)
      have hs (x : X) :
          IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (T.map a).hom) := by
        let A := forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
        exact A.map_isIso ((S x).map a)
      have : IsIso (T.map a) := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso (T.map a)
      exact isIso_of_reflects_iso a T
    have ht (x : X) : PreservesFiniteLimits (tensorRight G ⋙ S x) := by
      let : Module.Flat (X.presheaf.stalk x) ((S x).obj G) := hst x
      let : PreservesFiniteLimits (S x) := hlim x
      let : PreservesFiniteLimits (S x ⋙ tensorRight ((S x).obj G)) :=
        comp_preservesFiniteLimits (S x) _
      obtain ⟨Φ, _, hΦ⟩ := SheafOfModules.stalkTensorIso X x
      let e : tensorRight G ⋙ S x ≅ S x ⋙ tensorRight ((S x).obj G) :=
        NatIso.ofComponents (fun F ↦ Φ F G) (by
          intro F F' f
          simpa using hΦ F G F' G f (𝟙 G))
      exact preservesFiniteLimits_of_natIso e.symm
    have : PreservesFiniteLimits (tensorRight G) := by
      constructor
      intro J _ _
      constructor
      intro K
      let (x : X) := hlim x
      let (x : X) := ht x
      apply preservesLimit_of_preserves_limit_cone (limit.isLimit K)
      apply hreflect.jointlyReflectsLimit
      intro x
      exact isLimitOfPreserves (tensorRight G ⋙ S x) (limit.isLimit K)
    let : MonoidalClosed Y.Modules := SheafOfModules.monoidalClosed (R := Y.sheaf)
    change PreservesFiniteLimits (tensorRight G) ∧ PreservesFiniteColimits (tensorRight G)
    refine ⟨inferInstance, ?_⟩
    exact preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight G)
end AlgebraicGeometry
