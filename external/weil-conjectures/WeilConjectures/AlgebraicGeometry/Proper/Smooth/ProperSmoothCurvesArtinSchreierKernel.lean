/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.AlgebraicGeometry.Sites.ArtinSchreier
import WeilConjectures.AlgebraicGeometry.Proper.Smooth.ProperSmoothCurvesGaHigherDirectImage
import WeilConjectures.AlgebraicGeometry.Proper.Smooth.ProperSmoothCurvesGaHigherDirectImageVanishing
import WeilConjectures.AlgebraicGeometry.FrobeniusLinearVectorBundleLocallySurjective
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologySequence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# The Artin--Schreier sequence for a family of curves

For a proper smooth family `f: C ⟶ S` of curves with geometrically connected fibres over a
Noetherian base on which the prime `p` vanishes, the underlying abelian sheaf of `Rᵠf_* ℤ/p` is
the kernel of `F - 1` for a Frobenius-linear endomorphism `F` of a finite locally free module.

## References

* Stacks Project, Tag 0GKV, case (b)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The Artin--Schreier sequence `0 → ℤ/p → 𝔾ₐ → 𝔾ₐ → 0` on the small étale site of a scheme
on which the prime `p` vanishes, with first map the inclusion of the constants. -/
theorem shortExact_constantZModToGaSheaf_gaArtinSchreier (X : Scheme.{u}) (p : ℕ)
    [Fact p.Prime] (hp : (p : Γ(X, ⊤)) = 0) :
    (ShortComplex.mk (X.constantZModToGaSheaf p hp) (X.gaArtinSchreier p hp)
      (X.constantZModToGaSheaf_comp_gaArtinSchreier p hp)).ShortExact := by
  have : IsIso (X.constantZModToKernelGaArtinSchreier p hp) :=
    X.isIso_constantZModToKernelGaArtinSchreier p hp
  refine ShortComplex.shortExact_of_iso ?_ (X.artinSchreierSequence_shortExact p hp)
  refine ShortComplex.isoMk (asIso (X.constantZModToKernelGaArtinSchreier p hp)).symm
    (Iso.refl _) (Iso.refl _) ?_ ?_
  · dsimp [Scheme.artinSchreierSequence]
    rw [Category.comp_id, IsIso.inv_comp_eq]
    exact (kernel.lift_ι _ _ _).symm
  · dsimp [Scheme.artinSchreierSequence]
    rw [Category.comp_id, Category.id_comp]

/-- Postcomposition of sheaves with a functor preserving limits of a shape preserves limits of
that shape: limits of sheaves are computed on sections. -/
private instance preservesLimitsOfShape_sheafCompose {C : Type*} [Category* C]
    (J : GrothendieckTopology C) {D E : Type*} [Category* D] [Category* E] (G : D ⥤ E)
    [J.HasSheafCompose G] {K : Type*} [Category* K] [HasLimitsOfShape K D]
    [HasLimitsOfShape K E] [PreservesLimitsOfShape K G] :
    PreservesLimitsOfShape K (sheafCompose J G) := by
  have : PreservesLimitsOfShape K (sheafCompose J G ⋙ sheafToPresheaf J E) :=
    preservesLimitsOfShape_of_natIso
      (Iso.refl (sheafToPresheaf J D ⋙ (Functor.whiskeringRight _ _ _).obj G))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J E)

/-- The universe lift of a locally surjective morphism of abelian étale sheaves is an
epimorphism. -/
private theorem epi_sheafCompose_uliftFunctor_map {S : Scheme.{u}}
    {G H : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}} (φ : G ⟶ H)
    [Sheaf.IsLocallySurjective φ] :
    Epi ((sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map φ) := by
  have : Sheaf.IsLocallySurjective
      ((sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map φ) := by
    refine ⟨fun {U} s ↦ ?_⟩
    refine S.smallEtaleTopology.superset_covering ?_
      (Presheaf.imageSieve_mem S.smallEtaleTopology φ.hom (ULift.down s))
    rintro V g ⟨t, ht⟩
    exact ⟨ULift.up t, congrArg ULift.up ht⟩
  infer_instance

/-- **The Artin--Schreier sequence for a family of curves.** For a proper smooth family
`f: C ⟶ S` with geometrically connected one-dimensional fibres over a Noetherian base on
which the prime `p` vanishes, and every degree `q`, the underlying abelian sheaf of
`Rᵠf_* ℤ/p` is the universe lift of the kernel of `F - 1`, for a Frobenius-linear endomorphism
`F` of the étale sheaf of a finite locally free module. -/
theorem exists_forget₂_higherDirectImage_iso_frobeniusLinear_kernel
    {C S : Scheme.{u}} [IsNoetherian S]
    (f : C ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (h_dim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1)
    (p : ℕ) [Fact p.Prime] (hp : (p : Γ(S, ⊤)) = 0) (q : ℤ) :
    ∃ (E : S.Modules) (_ : E.IsQuasicoherent) (_ : E.IsFiniteLocallyFree)
      (F : Scheme.Modules.etaleTensorSectionsSheaf E ⟶
        Scheme.Modules.etaleTensorSectionsSheaf E),
      (∀ (U : S.Etale) (a : Γ(U.left, ⊤))
        (e : Γ((Scheme.Modules.tensorPullback U.hom).obj E, ⊤)),
        F.hom.app (op U)
            ((((Scheme.Modules.tensorPullback U.hom).obj E).smul a).asHom.hom e) =
          (((Scheme.Modules.tensorPullback U.hom).obj E).smul (a ^ p)).asHom.hom
            (F.hom.app (op U) e)) ∧
      Nonempty ((sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p))) AddCommGrpCat.{u + 1})).obj
            (higherDirectImage (ULift.{u + 1} (ZMod p)) f q
              ((constantSheaf C.smallEtaleTopology
                (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p)))).obj
                (ModuleCat.of (ULift.{u + 1} (ZMod p)) (ULift.{u + 1} (ZMod p))))) ≅
        (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          (kernel (F - 𝟙 _))) := by
  have hpC : (p : Γ(C, ⊤)) = 0 := by
    rw [← map_natCast f.appTop.hom, hp, map_zero]
  let Φ := lowerStar AddCommGrpCat.{u + 1} f
  let H (n : ℤ) := DerivedCategory.singleFunctor _ 0 ⋙ Φ.rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor _ n
  have hS := shortExact_constantZModToGaSheaf_gaArtinSchreier C p hpC
  obtain ⟨E, _, _, F, hF, e, he⟩ :=
    properSmoothCurves_higherDirectImage_ga_frobeniusLinear f h_dim p hp hpC q
  refine ⟨E, inferInstance, inferInstance, F, hF, ?_⟩
  have hepi : Epi ((H (q - 1)).map (C.gaArtinSchreier p hpC)) := by
    by_cases hq : q - 1 < 0
    · exact IsZero.epi ((DerivedCategory.isGE_iff _ 0).mp
        (Φ.isGE_rightDerivedFunctor_obj_singleFunctor C.gaSheaf) (q - 1) hq) _
    · obtain ⟨E', _, _, F', hF', e', he'⟩ :=
        properSmoothCurves_higherDirectImage_ga_frobeniusLinear f h_dim p hp hpC (q - 1)
      let : S.Over (Spec (.of (ULift.{u} (ZMod p)))) :=
        ⟨S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
          ((zmodRingHomOfNatCastEqZero p hp).comp ULift.ringEquiv.toRingHom))⟩
      have := Scheme.frobenius_linear_vector_bundle_locally_surjective p S E' F' hF'
      have := epi_sheafCompose_uliftFunctor_map (F' - 𝟙 _)
      have h : (H (q - 1)).map (C.gaArtinSchreier p hpC) = e'.hom ≫
          (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map
            (F' - 𝟙 _) ≫ e'.inv := by
        rw [← reassoc_of% he', Iso.hom_inv_id, Category.comp_id]
        rfl
      rw [h]
      infer_instance
  have hδ := (Φ.rightDerivedHomologySequence_exact₃ hS (q - 1) q (by omega)).epi_f_iff.mp hepi
  have hmono := (Φ.rightDerivedHomologySequence_exact₁ hS (q - 1) q (by omega)).mono_g hδ
  have hker := (Φ.rightDerivedHomologySequence_exact₂ hS q).fIsKernel
  obtain ⟨i₀⟩ := nonempty_higherDirectImage_forget_iso (ULift.{u + 1} (ZMod p)) f q
    ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p)))).obj
      (ModuleCat.of (ULift.{u + 1} (ZMod p)) (ULift.{u + 1} (ZMod p))))
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p))) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} _
  have : C.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p))) AddCommGrpCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification C.smallEtaleTopology _
  exact ⟨i₀ ≪≫ homologyRightDerivedLowerStarPlusIso f _ q ≪≫
    (H q).mapIso ((constantCommuteCompose C.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p))) AddCommGrpCat.{u + 1})).app
        (ModuleCat.of (ULift.{u + 1} (ZMod p)) (ULift.{u + 1} (ZMod p)))) ≪≫
    IsLimit.conePointUniqueUpToIso hker (kernelIsKernel _) ≪≫
    kernel.mapIso _ _ e e he ≪≫
    (PreservesKernel.iso
      (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}) (F - 𝟙 _)).symm⟩

end AlgebraicGeometry.Etale
