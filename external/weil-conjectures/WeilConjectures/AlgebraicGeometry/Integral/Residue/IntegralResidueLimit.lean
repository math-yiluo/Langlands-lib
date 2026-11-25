/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import Mathlib.Topology.Connected.TotallyDisconnected
public import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
public import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
public import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Category.Ring.Basic
public import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
public import WeilConjectures.AlgebraicGeometry.ContinuousRegularFunctions
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# The integral coefficient module as the limit of its residue modules

The residue maps are the actual continuous reductions,
composed with the canonical condensed-to-continuous coefficient comparison.
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory MonObj Limits Opposite Preadditive
open scoped CategoryTheory.Obj Topology
open Filter
namespace PadicInt
variable {p : ℕ} [Fact p.Prime]
private theorem exists_unique_continuous_lift (S : Type*) [TopologicalSpace S]
    (a : ∀ n : ℕ, C(S, ZMod (p ^ n)))
    (ha : ∀ n x, ZMod.castHom (pow_dvd_pow p (Nat.le_add_right n 1))
      (ZMod (p ^ n)) (a (n + 1) x) = a n x) :
    ∃! f : C(S, ℤ_[p]), ∀ n x, toZModPow n (f x) = a n x := by
  let f : S → ℤ_[p] := fun x ↦ ofCompatible (fun n ↦ a n x) (fun n ↦ ha n x)
  have hres (n : ℕ) (x : S) : toZModPow n (f x) = a n x :=
    toZModPow_ofCompatible _ (fun n ↦ ha n x) n
  have hcont : Continuous f := by
    refine continuous_iff_continuousAt.mpr fun x ↦ ?_
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_neg_lt p hε
    have hU : IsOpen ((a n) ⁻¹' {a n x}) :=
      (isOpen_discrete _).preimage (a n).continuous
    filter_upwards [hU.mem_nhds (by simp)] with y hy
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
    have hz : toZModPow n (f y - f x) = 0 := by rw [map_sub, hres, hres, hy, sub_self]
    rw [← RingHom.mem_ker, ker_toZModPow, ← norm_le_pow_iff_mem_span_pow] at hz
    rw [dist_eq_norm]
    exact hz.trans_lt hn
  refine ⟨⟨f, hcont⟩, hres, ?_⟩
  intro g hg
  ext x : 1
  apply ext_of_toZModPow.mp
  intro n
  exact (hg n x).trans (hres n x).symm
end PadicInt

namespace AlgebraicGeometry.ProEtale
open CondensedRing
/-- Reduction of continuous integral coefficients modulo `ℓ^n`. -/
noncomputable def tateResidueMap (X : Scheme.{u}) (ℓ n : ℕ) [Fact ℓ.Prime] :
    continuousAbRing X ℤ_[ℓ] ⟶ continuousAbRing X (ZMod (ℓ ^ n)) :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (continuousMapRingSheafMap X (PadicInt.toZModPow n) (PadicInt.continuous_toZModPow n))
/-- Reduction between consecutive continuous residue coefficient sheaves. -/
noncomputable def tateResidueTransition (X : Scheme.{u}) (ℓ n : ℕ) [Fact ℓ.Prime] :
    continuousAbRing X (ZMod (ℓ ^ (n + 1))) ⟶ continuousAbRing X (ZMod (ℓ ^ n)) :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (continuousMapRingSheafMap X
      (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n 1)) (ZMod (ℓ ^ n)))
      continuous_of_discreteTopology)
private noncomputable def residueSystem (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] :=
  Functor.ofOpSequence (X := fun n ↦ continuousAbRing X (ZMod (ℓ ^ n)))
    (fun n ↦ tateResidueTransition X ℓ n)
private noncomputable def residueCone (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] :
    Cone (residueSystem X ℓ) where
  pt := continuousAbRing X ℤ_[ℓ]
  π := NatTrans.ofOpSequence (fun n ↦ tateResidueMap X ℓ n) (fun n ↦ by
    simp only [Functor.const_obj_map, Functor.const_obj_obj, residueSystem,
      Functor.ofOpSequence_map_homOfLE_succ, Category.id_comp]
    change tateResidueMap X ℓ n = tateResidueMap X ℓ (n + 1) ≫ tateResidueTransition X ℓ n
    ext U a
    apply ULift.ext
    ext x
    exact (PadicInt.castHom_toZModPow_succ n (a.down x)).symm)
private noncomputable def residueConeIsLimit (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] :
    IsLimit (residueCone X ℓ) := by
  apply isLimitOfReflects (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  apply evaluationJointlyReflectsLimits
  intro U
  apply isLimitOfReflects (forget Ab.{u + 1})
  apply Classical.choice
  apply (Types.isLimit_iff _).mpr
  intro s hs
  have ha (n : ℕ) (x : U.unop.left) :
      ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n 1)) (ZMod (ℓ ^ n))
        ((s (op (n + 1))).down x) = (s (op n)).down x := by
    have hh := hs ((homOfLE (Nat.le_add_right n 1)).op)
    simp only [Functor.comp_map, residueSystem,
      Functor.ofOpSequence_map_homOfLE_succ] at hh
    exact congrArg (fun z : ULift.{u + 1} C(U.unop.left, ZMod (ℓ ^ n)) ↦ z.down x) hh
  obtain ⟨f, hf, huniq⟩ := PadicInt.exists_unique_continuous_lift U.unop.left
    (fun n ↦ (s (op n)).down) ha
  refine ⟨ULift.up f, ?_, ?_⟩
  · intro n
    apply ULift.ext
    ext x
    exact hf n.unop x
  · intro g hg
    apply ULift.ext
    apply huniq
    intro n x
    exact congrArg (fun z : ULift.{u + 1} C(U.unop.left, ZMod (ℓ ^ n)) ↦ z.down x)
      (hg (op n))
end AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.ProEtale
open CondensedRing
instance tateResidueMap_isMonHom (X : Scheme.{u}) (ℓ n : ℕ) [Fact ℓ.Prime] :
    IsMonHom (tateResidueMap X ℓ n) := by
  dsimp only [tateResidueMap]
  infer_instance
instance tateResidueTransition_isMonHom (X : Scheme.{u}) (ℓ n : ℕ) [Fact ℓ.Prime] :
    IsMonHom (tateResidueTransition X ℓ n) := by
  dsimp only [tateResidueTransition]
  infer_instance
/-- The actual reduction from the condensed integral coefficient object. -/
noncomputable def tateResidueCoefficientMap (X : Scheme.{u}) (ℓ n : ℕ) [Fact ℓ.Prime] :=
  chartComparison X ℤ_[ℓ] ≫ tateResidueMap X ℓ n
instance tateResidueCoefficientMap_isMonHom (X : Scheme.{u}) (ℓ n : ℕ) [Fact ℓ.Prime] :
    IsMonHom (tateResidueCoefficientMap X ℓ n) := by
  dsimp only [tateResidueCoefficientMap]
  infer_instance
/-- Consecutive actual coefficient reductions are compatible. -/
theorem tateResidueCoefficientMap_compat (X : Scheme.{u}) (ℓ n : ℕ) [Fact ℓ.Prime] :
    tateResidueCoefficientMap X ℓ (n + 1) ≫ tateResidueTransition X ℓ n =
      tateResidueCoefficientMap X ℓ n := by
  dsimp only [tateResidueCoefficientMap]
  rw [Category.assoc]
  congr 1
  ext U a
  apply ULift.ext
  ext x
  exact PadicInt.castHom_toZModPow_succ n (a.down x)
/-- The finite residue ring, regarded as a module over the integral coefficient object. -/
noncomputable def tateResidueModuleLevel (X : Scheme.{u}) (ℓ n : ℕ) [Fact ℓ.Prime] :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) :=
  (Mod.comap (tateResidueCoefficientMap X ℓ n)).obj
    (Mod.regular (continuousAbRing X (ZMod (ℓ ^ n))))
/-- The linear transition between consecutive finite residue modules. -/
noncomputable def tateResidueModuleTransition (X : Scheme.{u}) (ℓ n : ℕ) [Fact ℓ.Prime] :
    tateResidueModuleLevel X ℓ (n + 1) ⟶ tateResidueModuleLevel X ℓ n :=
  Mod.Hom.mk' (tateResidueTransition X ℓ n) (by
    change (tateResidueCoefficientMap X ℓ (n + 1) ▷ _ ≫ μ[_]) ≫ tateResidueTransition X ℓ n =
      _ ◁ tateResidueTransition X ℓ n ≫ tateResidueCoefficientMap X ℓ n ▷ _ ≫ μ[_]
    rw [Category.assoc, IsMonHom.mul_hom, tensorHom_def', Category.assoc,
      ← whisker_exchange_assoc, ← comp_whiskerRight_assoc,
      tateResidueCoefficientMap_compat])
/-- The inverse system of finite residue modules, including the zero level. -/
noncomputable def tateResidueModuleSystem (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] :=
  Functor.ofOpSequence (X := fun n ↦ tateResidueModuleLevel X ℓ n)
    (fun n ↦ tateResidueModuleTransition X ℓ n)
/-- The canonical linear projection from the regular integral module to a residue level. -/
noncomputable def tateResidueModuleProjection (X : Scheme.{u}) (ℓ n : ℕ) [Fact ℓ.Prime] :
    Mod.regular (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) ⟶
      tateResidueModuleLevel X ℓ n :=
  Mod.Hom.mk' (tateResidueCoefficientMap X ℓ n) (by
    change μ[_] ≫ tateResidueCoefficientMap X ℓ n =
      _ ◁ tateResidueCoefficientMap X ℓ n ≫ tateResidueCoefficientMap X ℓ n ▷ _ ≫ μ[_]
    rw [IsMonHom.mul_hom, tensorHom_def', Category.assoc])
/-- The cone of actual residue projections with vertex the regular integral module. -/
noncomputable def tateResidueModuleCone (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] :
    Cone (tateResidueModuleSystem X ℓ) where
  pt := Mod.regular (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X)
  π := NatTrans.ofOpSequence (fun n ↦ tateResidueModuleProjection X ℓ n) (fun n ↦ by
    simp only [Functor.const_obj_map, Functor.const_obj_obj, tateResidueModuleSystem,
      Functor.ofOpSequence_map_homOfLE_succ, Category.id_comp]
    apply Mod.hom_ext
    exact (tateResidueCoefficientMap_compat X ℓ n).symm)
private noncomputable def residueModuleForgetIso (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] :
    tateResidueModuleSystem X ℓ ⋙ Mod.forget
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) ≅ residueSystem X ℓ := by
  let t : tateResidueModuleSystem X ℓ ⋙ Mod.forget
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) ⟶ residueSystem X ℓ :=
    NatTrans.ofOpSequence (fun n ↦ 𝟙 _) (fun n ↦ by
      simp only [Functor.comp_map, tateResidueModuleSystem, residueSystem,
        Functor.ofOpSequence_map_homOfLE_succ, Category.comp_id, Category.id_comp]
      rfl)
  have : ∀ n, IsIso (t.app n) := fun n ↦ inferInstanceAs (IsIso (𝟙 _))
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t
/-- The regular condensed integral coefficient module is the inverse limit of its residues. -/
theorem tateResidueModuleCone_isLimit (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] :
    Nonempty (IsLimit (tateResidueModuleCone X ℓ)) := by
  refine ⟨?_⟩
  apply isLimitOfReflects (Mod.forget
    (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X))
  apply (IsLimit.postcomposeHomEquiv (residueModuleForgetIso X ℓ) _).toFun
  refine IsLimit.ofIsoLimit (residueConeIsLimit X ℓ) ?_
  exact (Cone.ext (asIso (chartComparison X ℤ_[ℓ])) (fun n ↦ by
    simp only [Cone.postcompose_obj_π, NatTrans.comp_app]
    change tateResidueCoefficientMap X ℓ n.unop ≫ 𝟙 _ =
      chartComparison X ℤ_[ℓ] ≫ tateResidueMap X ℓ n.unop
    exact Category.comp_id _)).symm
end AlgebraicGeometry.ProEtale
