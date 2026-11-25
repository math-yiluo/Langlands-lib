/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.DiagonalConormalDifferentials
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank

/-! # The ideal-sheaf conormal and its rank for a smooth closed diagonal

Source: Stacks Project, Tags 08S2 and 02G1
(blueprint: lem-sc-smooth-diagonal-ideal-conormal-rank).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The ideal module of a closed immersion is its actual structure-map kernel.
The factorization through the scheme-theoretic image gives a kernel lift; its sections
are bijective on the affine basis because both inclusions have the same ideal range. -/
private theorem ideal_kernel_iso {Y Z : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] :
    Nonempty (i.ker.toModules ≅
      kernel (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)) := by
  let η : SheafOfModules.unit Y.ringCatSheaf ⟶
      (SheafOfModules.pushforward i.toRingCatSheafHom).obj
        (SheafOfModules.unit Z.ringCatSheaf) :=
    SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom
  have hzero : i.ker.toModulesι ≫ η = 0 := by
    apply Scheme.Modules.hom_ext
    intro U
    ext s
    change i.app U (i.ker.toModulesι.app U s) = 0
    have hs := (i.ker.range_toModulesι_app_eq U).subset ⟨s, rfl⟩
    change i.ker.subschemeι.app U (i.ker.toModulesι.app U s) = 0 at hs
    have he := Scheme.Hom.congr_app i.toImage_imageι U
    have hs' : (i.toImage ≫ i.imageι).app U (i.ker.toModulesι.app U s) = 0 := by
      rw [Scheme.Hom.comp_app]
      simp only [CommRingCat.comp_apply, hs, map_zero]
    rw [he] at hs'
    rw [CommRingCat.comp_apply] at hs'
    exact (ConcreteCategory.bijective_of_isIso _).1 (hs'.trans (map_zero _).symm)
  let φ : i.ker.toModules ⟶ kernel η := kernel.lift η i.ker.toModulesι hzero
  have hφ : φ ≫ kernel.ι η = i.ker.toModulesι := kernel.lift_ι _ _ _
  have hbij (U : Y.affineOpens) : Function.Bijective (φ.app U.1) := by
    have hk := Scheme.Modules.injective_map_kernelι U.1 η
    constructor
    · intro a b hab
      apply i.ker.injective_toModulesι_app U.1
      simp only [← hφ, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, hab]
    · intro b
      have hb : Scheme.Modules.Hom.app (kernel.ι η) U.1 b ∈ i.ker.ideal U := by
        rw [Scheme.Hom.ker_apply]
        change Scheme.Modules.Hom.app η U.1 (Scheme.Modules.Hom.app (kernel.ι η) U.1 b) = 0
        exact congrArg (fun g ↦ Scheme.Modules.Hom.app g U.1 b) (kernel.condition η)
      obtain ⟨a, ha⟩ := (i.ker.range_toModulesι_app U).symm.subset hb
      refine ⟨a, hk ?_⟩
      change Scheme.Modules.Hom.app (kernel.ι η) U.1 (φ.app U.1 a) =
        Scheme.Modules.Hom.app (kernel.ι η) U.1 b
      simpa only [← hφ, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
        using ha
  have : IsIso ((SheafOfModules.toSheaf Y.ringCatSheaf).map φ) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis
      (show TopologicalSpace.Opens.IsBasis
        (Set.range (fun U : Y.affineOpens ↦ U.1)) from
        by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq]
          using Y.isBasis_affineOpens)
    intro U
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (hbij U)
  have : (SheafOfModules.toSheaf Y.ringCatSheaf ⋙
      sheafToPresheaf _ _).ReflectsIsomorphisms :=
    inferInstanceAs (Scheme.Modules.toPresheaf Y).ReflectsIsomorphisms
  have : (SheafOfModules.toSheaf Y.ringCatSheaf).ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_comp _ (sheafToPresheaf _ _)
  have : IsIso φ := isIso_of_reflects_iso φ (SheafOfModules.toSheaf Y.ringCatSheaf)
  exact ⟨asIso φ⟩

/-- The conormal used by Koszul duality agrees with relative differentials and has
stalk rank equal to the pure relative dimension. This concerns only module sheaves,
without derived categories or a duality adjunction.
Source: Stacks Project, Tags 08S2 and 02G1
(blueprint: lem-sc-smooth-diagonal-ideal-conormal-rank).

Proof: write i for the closed diagonal. The canonical isomorphism from X to the
closed subscheme defined by i.ker commutes with the maps to the fibre product.
Its pushforward identifies the two maps from the structure sheaf, hence their
kernels: i.ker.toModules is isomorphic to the module-sheaf kernel defining
 diagonalConormal. Tensor pullback carries this isomorphism to X. Compose with
 diagonalConormal_iso_relativeDifferentials. The theorem
 isFiniteLocallyFreeOfRank_relativeDifferentials gives local trivializations by
O_X^d. Taking stalks gives free modules O_{X,x}^d, whose finrank is d because
these local rings are nontrivial. Transport finrank along the stalk isomorphism.
For empty X the stalk assertion is vacuous; for d = 0 the free module is zero. -/
theorem smoothDiagonal_idealConormal_iso_and_rank {X S : Scheme.{u}}
    (f : X ⟶ S) (d : ℕ) [SmoothOfRelativeDimension d f]
    [IsClosedImmersion (pullback.diagonal f)] :
    Nonempty (((Scheme.Modules.tensorPullback (pullback.diagonal f)).obj
      (pullback.diagonal f).ker.toModules) ≅ f.relativeDifferentials) ∧
    ∀ x : X, Module.finrank (X.presheaf.stalk x)
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
        ((Scheme.Modules.tensorPullback (pullback.diagonal f)).obj
          (pullback.diagonal f).ker.toModules)) = d := by
  obtain ⟨eI⟩ := ideal_kernel_iso (pullback.diagonal f)
  obtain ⟨eΩ⟩ := diagonalConormal_iso_relativeDifferentials f
  let e := (Scheme.Modules.tensorPullback (pullback.diagonal f)).mapIso eI ≪≫ eΩ
  refine ⟨⟨e⟩, fun x ↦ ?_⟩
  have := f.isFiniteLocallyFreeOfRank_relativeDifferentials d
  exact ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapIso e).toLinearEquiv.finrank_eq
    |>.trans (Scheme.Modules.finiteLocallyFreeOfRank_stalk_finrank f.relativeDifferentials d x)

end AlgebraicGeometry
