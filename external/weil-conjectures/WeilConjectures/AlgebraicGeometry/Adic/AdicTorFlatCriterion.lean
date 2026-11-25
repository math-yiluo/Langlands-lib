/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.LevelwiseAdicTruncations
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic

import WeilConjectures.AlgebraicGeometry.Adic.AdicCohomologyTorsionNormalForm
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.NoetherianStratumDetectionSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # The Padic Tor criterion for flat cohomology

This is the first independent half of the criterion in
`Sheaf.Paper.AdicTorFlatCohomology`. -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem flat_of_iso (X : Scheme.{u})
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {M N : pbcModules X R} (e : M ≅ N)
    (h : SheafOfModules.IsFlatOnSite (J := ProEt.topology X) (R := R) M) :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology X) (R := R) N := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let tensor : MonoidalCategory (pbcModules X R) := SheafOfModules.monoidalCategory R
  let e₁ := SheafOfModules.siteSheafTensorRightIso R M
  let e₂ := SheafOfModules.siteSheafTensorRightIso R N
  let e₃ := (@MonoidalCategory.curriedTensor (pbcModules X R) _ tensor).flip.mapIso e
  exact (exactFunctor _ _).prop_of_iso (e₁ ≪≫ e₃ ≪≫ e₂.symm) h

private theorem flat_of_sectionwise_flat (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (F : pbcModules X R) (hF : ∀ U : X.ProEtᵒᵖ, Module.Flat (R.obj.obj U) (F.val.obj U)) :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology X) (R := R) F := by
  apply SheafOfModules.isFlatOnSite_of_local_equationalCriterion R F
  intro U n a s hs
  refine ⟨⊤, (ProEt.topology X).top_mem U, ?_⟩
  intro V f _
  have : Module.Flat (R.obj.obj (op V)) (F.val.obj (op V)) := hF (op V)
  have he := congrArg (fun x ↦ (show F.val.obj (op V) from F.val.map f.op x)) hs
  rw [map_sum, map_zero] at he
  have he' : (∑ p : Fin n, (show F.val.obj (op V) from
      F.val.map f.op (a p • s p))) = 0 := he
  have hr : (∑ p : Fin n, R.obj.map f.op (a p) •
      (show F.val.obj (op V) from F.val.map f.op (s p))) = 0 := by
    calc
      _ = ∑ p : Fin n, (show F.val.obj (op V) from
          F.val.map f.op (a p • s p)) := by
        apply Finset.sum_congr rfl
        intro p _
        exact (F.val.map_smul f.op (a p) (s p)).symm
      _ = 0 := he'
  obtain ⟨k, b, t, hb, ht⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hr
  exact ⟨k, b, t, hb, ht⟩

private theorem isZero_of_nilpotent_cokernel
    {C : Type*} [Category* C] [Abelian C] {N : C} (f : End N)
    (hnil : IsNilpotent f) (hc : IsZero (cokernel f.asHom)) : IsZero N := by
  have : Epi f.asHom := Abelian.epi_of_cokernel_π_eq_zero f.asHom (hc.eq_of_tgt _ _)
  have hp : ∀ n : ℕ, Epi (f ^ n).asHom := by
    intro n
    induction n with
    | zero => change Epi (𝟙 N); infer_instance
    | succ n ih =>
      rw [pow_succ]
      change Epi (f.asHom ≫ (f ^ n).asHom)
      infer_instance
  obtain ⟨n, hn⟩ := hnil
  have := hp n
  exact IsZero.of_epi_eq_zero (f ^ n).asHom (by rw [hn, End.zero_asHom])

private theorem module_zero_of_stratum_cover
    (T : Scheme.{u}) [IsNoetherian T] (S : Stratification T)
    (V : ∀ a : Fin S.n, Cover.{u + 1} proetalePrecoverage (S.domain a))
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (F : proEtaleRingModules T R)
    (hF : ∀ a j, IsZero ((proEtaleRingModulePullback
      ((V a).f j ≫ S.immersion a) R
      ((adicTowerInverseImage ((V a).f j ≫ S.immersion a)).obj R)
      (Iso.refl _)).obj F)) : IsZero F := by
  have hz : IsZero ((SheafOfModules.toSheaf _).obj F) := by
    apply proEtale_isZero_of_stratum_cover T S V
    intro a j
    let g := (V a).f j ≫ S.immersion a
    let R' := (adicTowerInverseImage g).obj R
    let P := proEtaleRingModulePullback g R R' (Iso.refl _)
    let adj := proEtaleRingModuleAdjunction g R R' (Iso.refl _)
    let c := ((proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).homEquiv
      ((SheafOfModules.toSheaf _).obj F)
      ((SheafOfModules.toSheaf _).obj (P.obj F))).symm
        ((SheafOfModules.toSheaf _).map (adj.unit.app F))
    have : IsIso c := ringUnitComparison g R R' (Iso.refl _) adj F
    exact ((SheafOfModules.toSheaf _).map_isZero (hF a j)).of_iso (asIso c)
  apply (IsZero.iff_id_eq_zero F).2
  apply (SheafOfModules.toSheaf _).map_injective
  simpa using hz.eq_of_src ((SheafOfModules.toSheaf _).map (𝟙 F))
    ((SheafOfModules.toSheaf _).map (0 : F ⟶ F))

set_option backward.isDefEq.respectTransparency false in
private theorem flat_of_stratum_cover
    (T : Scheme.{u}) [IsNoetherian T] (S : Stratification T)
    (V : ∀ a : Fin S.n, Cover.{u + 1} proetalePrecoverage (S.domain a))
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (F : proEtaleRingModules T R)
    (hF : ∀ a j, SheafOfModules.IsFlatOnSite (J := ProEt.topology ((V a).X j))
      (R := (adicTowerInverseImage ((V a).f j ≫ S.immersion a)).obj R)
      ((proEtaleRingModulePullback ((V a).f j ≫ S.immersion a) R
        ((adicTowerInverseImage ((V a).f j ≫ S.immersion a)).obj R)
        (Iso.refl _)).obj F)) :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology T) (R := R) F := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  have hl := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R F
  have : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft F) :=
    preservesColimitsOfSize_shrink _
  have : PreservesFiniteColimits (MonoidalCategory.tensorLeft F) := inferInstance
  have hc : PreservesFiniteColimits (MonoidalCategory.tensorRight F) :=
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight F)
  have : (MonoidalCategory.tensorRight F).Additive :=
    (rightExactFunctor_le_additiveFunctor _ _) _ hc
  have hm {M N : proEtaleRingModules T R} (f : M ⟶ N) [Mono f] :
      Mono ((MonoidalCategory.tensorRight F).map f) := by
    let t := (MonoidalCategory.tensorRight F).map f
    have hz : IsZero (kernel t) := by
      apply module_zero_of_stratum_cover T S V R
      intro a j
      let g := (V a).f j ≫ S.immersion a
      let R' := (adicTowerInverseImage g).obj R
      let P := proEtaleRingModulePullback g R R' (Iso.refl _)
      let := SheafOfModules.isMonoidal_W_independentCoefficients R'
      let := SheafOfModules.monoidalCategory R'
      have hf : exactFunctor _ _ (MonoidalCategory.tensorRight (P.obj F)) :=
        (exactFunctor _ _).prop_of_iso
          (SheafOfModules.siteSheafTensorRightIso R' (P.obj F)) (hF a j)
      have : PreservesFiniteLimits (MonoidalCategory.tensorRight (P.obj F)) := hf.1
      have he := proEtaleOrdinaryTensorPullback_naturality g R R' (Iso.refl _)
        M N F F f (𝟙 F)
      rw [((proEtaleOrdinaryTensor T R).obj N).map_id, Category.comp_id,
        (proEtaleRingModulePullback g R R' (Iso.refl _)).map_id,
        ((proEtaleOrdinaryTensor ((V a).X j) R').obj (P.obj N)).map_id,
        Category.comp_id] at he
      change P.map t ≫ (proEtaleOrdinaryTensorPullback g R R' (Iso.refl _) N F).hom =
        (proEtaleOrdinaryTensorPullback g R R' (Iso.refl _) M F).hom ≫
          (MonoidalCategory.tensorRight (P.obj F)).map (P.map f) at he
      have : Mono (P.map t ≫
          (proEtaleOrdinaryTensorPullback g R R' (Iso.refl _) N F).hom) := by
        rw [he]
        infer_instance
      have : Mono (P.map t) := mono_of_mono (P.map t)
        (proEtaleOrdinaryTensorPullback g R R' (Iso.refl _) N F).hom
      exact (isZero_kernel_of_mono (P.map t)).of_iso (PreservesKernel.iso P t)
    exact Abelian.mono_of_kernel_ι_eq_zero t (hz.eq_of_src _ _)
  have : (MonoidalCategory.tensorRight F).PreservesMonomorphisms := ⟨fun f _ ↦ hm f⟩
  have hleft : PreservesFiniteLimits (MonoidalCategory.tensorRight F) := by
    apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).2
    intro C hC
    have := hC.mono_f
    exact ⟨hC.exact.map_of_epi_of_preservesCokernel _ hC.epi_g inferInstance,
      inferInstance⟩
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R F).symm ⟨hleft, hc⟩

end AlgebraicGeometry.Scheme
