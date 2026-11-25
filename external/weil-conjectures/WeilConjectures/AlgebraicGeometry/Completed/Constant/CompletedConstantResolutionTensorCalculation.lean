/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantRealizationDataSupplement
import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.AlgebraicGeometry.CompletedConstantProjection.CompletedConstantResidueData
import all WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantRankOneComparison
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
import WeilConjectures.Algebra.Homology.BifunctorSingleComparison
import WeilConjectures.Algebra.Homology.FlatScalarRealizationFlat
import WeilConjectures.Algebra.Homology.FlatScalarRealization
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.CategoryTheory.ConstantModuleFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
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
import Mathlib.RingTheory.Flat.EquationalCriterion
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceDataSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.CategoryTheory.Monoidal.BraidedLocalizationSquare
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare

/-! # Tensor calculation on finite-free completion resolutions

Source: Stacks Tags 06YN, 06YT, 06YU and 093M.
(blueprint: lem-weil-pbc-completed-constant-resolution-tensor-calculation).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme

private def extensionCompIso (X : Scheme.{u})
    {R S V : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) :
    completedConstantExtension X a ⋙ completedConstantExtension X b ≅
      completedConstantExtension X (a ≫ b) := by
  let aa := (completedAdjunction X a).choose
  let ab := (completedAdjunction X b).choose
  let ac := (completedAdjunction X (a ≫ b)).choose
  exact ((aa.comp ab).ofNatIsoRight (completedRestrictCompIso X a b).symm).leftAdjointUniq ac

-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private def constantScalarChangeIso (X : Scheme.{u})
    {B D : Type (u + 1)} [CommRing B] [CommRing D] (q : B →+* D) :
    adicLisseConstantModules X B ⋙ completedConstantExtension X
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom q)) ≅
      ModuleCat.extendScalars.{u + 1, u + 1, u + 1} q ⋙ adicLisseConstantModules X D := by
  let J := ProEt.topology X
  let a := (constantSheaf J CommRingCat.{u + 1}).map (CommRingCat.ofHom q)
  let ac := (completedAdjunction X a).choose
  let ad := ConstantScalarRealization.adjunction J q
  let z := ac.leftAdjointUniq ad
  haveI (M : ModuleCat.{u + 1} B) :
      IsIso (ConstantScalarRealization.moduleComparison J q M) :=
    (ConstantScalarRealization.moduleComparison_tensor J q M).1
  let e : commutativeSiteConstantModuleFunctor J B ⋙
      ConstantScalarRealization.extension J q ≅
        ModuleCat.extendScalars.{u + 1, u + 1, u + 1} q ⋙
          commutativeSiteConstantModuleFunctor J D :=
    NatIso.ofComponents (fun M ↦
      asIso (ConstantScalarRealization.moduleComparison J q M))
      (fun f ↦ ConstantScalarRealization.moduleComparison_naturality J q f)
  exact Functor.isoWhiskerLeft (adicLisseConstantModules X B) z ≪≫ e

private def restrictedTensorIso {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (U : C ⥤ D) [U.Monoidal] (N : C) :
    U ⋙ MonoidalCategory.tensorRight (U.obj N) ≅ MonoidalCategory.tensorRight N ⋙ U := by
  refine NatIso.ofComponents (fun M ↦ Functor.Monoidal.μIso U M N) ?_
  intro M M' f
  exact Functor.LaxMonoidal.μ_natural_left U f N

private theorem reduction_eval_step
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) (n : ℕ) :
    (Ideal.Quotient.factorPowSucc I (n + 1)).comp
        (AdicCompletion.evalₐ I (n + 2)).toRingHom =
      (AdicCompletion.evalₐ I (n + 1)).toRingHom := by
  ext x
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I A x
  change Ideal.Quotient.factorPowSucc I (n + 1)
    (AdicCompletion.evalₐ I (n + 2) (AdicCompletion.mk I A s)) =
      AdicCompletion.evalₐ I (n + 1) (AdicCompletion.mk I A s)
  simp only [AdicCompletion.evalₐ_mk]
  change Ideal.Quotient.mk _ (s.val (n + 2)) = Ideal.Quotient.mk _ (s.val (n + 1))
  apply Ideal.Quotient.eq.mpr
  have hs := (Submodule.Quotient.eq _).mp
    (AdicCompletion.AdicCauchySequence.mk_eq_mk (Nat.le_succ (n + 1)) s)
  simpa [smul_eq_mul, Ideal.mul_top] using hs

private def scalarReductionMap
    {B D E : Type (u + 1)} [CommRing B] [CommRing D] [CommRing E]
    (f : B →+* D) (g : B →+* E) (q : D →+* E) (hq : q.comp f = g)
    (M : ModuleCat.{u + 1} B) :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f).obj M →ₛₗ[q]
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} g).obj M := by
  let N := (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} g).obj M
  letI : Module B D := Module.compHom D f
  letI : Module B E := Module.compHom E g
  letI : Module B N := Module.compHom N g
  letI : SMulCommClass B D D := ModuleCat.sMulCommClass_mk f D
  letI : SMulCommClass B E E := ModuleCat.sMulCommClass_mk g E
  let k : D →ₗ[B] M →ₗ[B] N :=
    { toFun := fun d ↦
        { toFun := fun x ↦ q d ⊗ₜ[B, g] x
          map_add' := fun _ _ ↦ TensorProduct.tmul_add _ _ _
          map_smul' := fun b x ↦ by
            change q d ⊗ₜ[B, g] (b • x) = g b • (q d ⊗ₜ[B, g] x)
            change q d ⊗ₜ[B, g] (b • x) = (g b * q d) ⊗ₜ[B, g] x
            exact (TensorProduct.smul_tmul (R := B) b (q d) x).symm }
      map_add' := by
        intro d d'
        ext x
        exact (congrArg (fun z ↦ z ⊗ₜ[B, g] x) (map_add q d d')).trans
          (TensorProduct.add_tmul _ _ _)
      map_smul' := by
        intro b d
        ext x
        change q (f b * d) ⊗ₜ[B, g] x = g b • (q d ⊗ₜ[B, g] x)
        rw [map_mul, show q (f b) = g b from RingHom.congr_fun hq b]
        rfl }
  let t := TensorProduct.lift k
  refine
    { toFun := t
      map_add' := t.map_add
      map_smul' := ?_ }
  change ∀ (d : D) (z : TensorProduct B D M), t (d • z) = q d • t z
  intro d z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul d' x =>
    change q (d * d') ⊗ₜ[B, g] x = (q d * q d') ⊗ₜ[B, g] x
    rw [map_mul]

private theorem scalarReductionMap_naturality
    {B D E : Type (u + 1)} [CommRing B] [CommRing D] [CommRing E]
    (f : B →+* D) (g : B →+* E) (q : D →+* E) (hq : q.comp f = g)
    {M N : ModuleCat.{u + 1} B} (l : M ⟶ N) :
    ∀ z : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f).obj M,
      scalarReductionMap f g q hq N
          (((ModuleCat.extendScalars f).map l).hom z) =
        ((ModuleCat.extendScalars g).map l).hom (scalarReductionMap f g q hq M z) := by
  let : Module B D := Module.compHom D f
  change ∀ z : TensorProduct B D M, _
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul p x => rfl

-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private def constantSemilinear (X : Scheme.{u})
    {B D : Type (u + 1)} [CommRing B] [CommRing D] (q : B →+* D)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : R ⟶ adicLisseConstantRing X B) (b : R ⟶ adicLisseConstantRing X D)
    (hab : a ≫ (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom q) = b)
    (M : ModuleCat.{u + 1} B) (N : ModuleCat.{u + 1} D) (f : M →ₛₗ[q] N) :
    (SheafOfModules.restrictScalars ((adicLisseForget X).map a)).obj
      ((adicLisseConstantModules X B).obj M) ⟶
    (SheafOfModules.restrictScalars ((adicLisseForget X).map b)).obj
      ((adicLisseConstantModules X D).obj N) := by
  let k := CompletedConstantProjection.constantMap X q (𝟙 _)
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom q))
    (Category.id_comp _) M N f
  refine ⟨{
    app := fun U ↦ ModuleCat.ofHom
      (X := ((SheafOfModules.restrictScalars ((adicLisseForget X).map a)).obj
        ((adicLisseConstantModules X B).obj M)).val.obj U)
      (Y := ((SheafOfModules.restrictScalars ((adicLisseForget X).map b)).obj
        ((adicLisseConstantModules X D).obj N)).val.obj U)
      { toFun := k.val.app U
        map_add' := map_add _
        map_smul' := ?_ }
    naturality := ?_ }⟩
  · intro r x
    let x' : ((adicLisseConstantModules X B).obj M).val.obj _ := x
    let y' : ((adicLisseConstantModules X D).obj N).val.obj _ := k.val.app _ x'
    change k.val.app _ (a.hom.app _ r • x') = b.hom.app _ r • y'
    have hk := (k.val.app _).hom.map_smul (a.hom.app _ r) x'
    change k.val.app _ (a.hom.app _ r • x') =
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom q)).hom.app _ (a.hom.app _ r) • y' at hk
    rw [hk]
    congr 1
    exact congrArg (fun z ↦ z.hom.app _ r) hab
  · intro U V g
    ext x
    exact PresheafOfModules.naturality_apply k.val g x

private theorem constantSemilinear_generator (X : Scheme.{u})
    {B D : Type (u + 1)} [CommRing B] [CommRing D] (q : B →+* D)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : R ⟶ adicLisseConstantRing X B) (b : R ⟶ adicLisseConstantRing X D)
    (hab : a ≫ (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom q) = b)
    (M : ModuleCat.{u + 1} B) (N : ModuleCat.{u + 1} D) (f : M →ₛₗ[q] N)
    (U : X.ProEtᵒᵖ) (x : M) :
    (constantSemilinear X q R a b hab M N f).val.app U
      (completedConstantGenerator X B M U x) = completedConstantGenerator X D N U (f x) := by
  exact CompletedConstantProjection.constantMap_generator X q (𝟙 _)
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom q))
    (Category.id_comp _) M N f U x

-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private theorem constant_generator_hom_ext (X : Scheme.{u})
    {B : Type (u + 1)} [CommRing B]
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : R ⟶ adicLisseConstantRing X B) (M : ModuleCat.{u + 1} B)
    (N : completedConstantModules X R)
    (f g : (SheafOfModules.restrictScalars ((adicLisseForget X).map a)).obj
      ((adicLisseConstantModules X B).obj M) ⟶ N)
    (h : ∀ (U : X.ProEtᵒᵖ) (x : M),
      f.val.app U (completedConstantGenerator X B M U x) =
        g.val.app U (completedConstantGenerator X B M U x)) : f = g := by
  apply (SheafOfModules.toSheaf _).map_injective
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology X) _ _ N.isSheaf
  ext U x
  exact h U x

private theorem constantSemilinear_naturality (X : Scheme.{u})
    {B D : Type (u + 1)} [CommRing B] [CommRing D] (q : B →+* D)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : R ⟶ adicLisseConstantRing X B) (b : R ⟶ adicLisseConstantRing X D)
    (hab : a ≫ (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom q) = b)
    (M M' : ModuleCat.{u + 1} B) (N N' : ModuleCat.{u + 1} D)
    (f : M →ₛₗ[q] N) (f' : M' →ₛₗ[q] N') (g : M ⟶ M') (k : N ⟶ N')
    (h : ∀ x : M, f' (g.hom x) = k.hom (f x)) :
    (SheafOfModules.restrictScalars ((adicLisseForget X).map a)).map
        ((adicLisseConstantModules X B).map g) ≫
        constantSemilinear X q R a b hab M' N' f' =
      constantSemilinear X q R a b hab M N f ≫
        (SheafOfModules.restrictScalars ((adicLisseForget X).map b)).map
          ((adicLisseConstantModules X D).map k) := by
  apply constant_generator_hom_ext X R a M _
  intro U x
  change (constantSemilinear X q R a b hab M' N' f').val.app U
    (((adicLisseConstantModules X B).map g).val.app U
      (completedConstantGenerator X B M U x)) =
    ((adicLisseConstantModules X D).map k).val.app U
      ((constantSemilinear X q R a b hab M N f).val.app U
        (completedConstantGenerator X B M U x))
  rw [CompletedConstantProjection.constant_map_generator,
    constantSemilinear_generator, constantSemilinear_generator,
    CompletedConstantProjection.constant_map_generator]
  exact congrArg (completedConstantGenerator X D N' U) (h x)

-- Work with the unbundled tensor carrier, so scalar restriction is unfolded once.
-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private abbrev reductionModuleLevel (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) (n : ℕ) :=
  ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
    (AdicCompletion.evalₐ I (n + 1)).toRingHom ⋙
      adicLisseConstantModules X (A ⧸ I ^ (n + 1)) ⋙
        SheafOfModules.restrictScalars ((adicLisseForget X).map
          (β ≫ limit.π (adicLisseRingSystem X I) (op n)))

-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private def reductionModuleIso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (d : CompletedConstantModuleRealization X I)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) [IsIso β]
    (c : ModuleCat.{u + 1} (AdicCompletion I A) ⥤ completedConstantModules X R)
    (e : c ≅ completedConstantRealization X I d.scalar ⋙
      SheafOfModules.restrictScalars ((adicLisseForget X).map β))
    (P : CompletedConstantQuotientTower X I R β) (n : ℕ) :
    letI := SheafOfModules.cochainModulesMonoidal R
    c ⋙ MonoidalCategory.tensorRight (P.diagram.obj (op n)) ≅
      reductionModuleLevel X I R β n := by
  let := SheafOfModules.cochainModulesMonoidal R
  let := SheafOfModules.cochainModulesMonoidal (adicLisseCompletedRing X I)
  let := HasDerivedCategory.standard (completedConstantModules X R)
  let := HasDerivedCategory.standard
    (completedConstantModules X (adicLisseCompletedRing X I))
  let tr := (SheafOfModules.ringIso_tensor_transport (asIso β)).some
  let U := SheafOfModules.restrictScalars ((adicLisseForget X).map β)
  letI : U.Braided := tr.monoidal
  let π := limit.π (adicLisseRingSystem X I) (op n)
  let V := completedRestriction X π
  let N := SheafOfModules.unit ((adicLisseForget X).obj
    ((adicLisseRingSystem X I).obj (op n)))
  let ep : U.obj (V.obj N) ≅ P.diagram.obj (op n) :=
    ((completedRestrictCompIso X β π).app N).symm ≪≫ (eqToIso (P.level (op n))).symm
  let C := adicLisseConstantModules X (AdicCompletion I A)
  let E := completedConstantExtension X d.scalar
  let a := Functor.isoWhiskerLeft c
    ((MonoidalCategory.curriedTensor (completedConstantModules X R)).flip.mapIso ep.symm)
  let b := Functor.isoWhiskerRight e (MonoidalCategory.tensorRight (U.obj (V.obj N)))
  let k := Functor.isoWhiskerLeft E (restrictedTensorIso U (V.obj N))
  let t := (completedOrdinaryRestrictionComparison X π).some
  let l := Functor.isoWhiskerRight (Functor.isoWhiskerLeft E t.symm) U
  let m := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft C (extensionCompIso X d.scalar π)) (V ⋙ U)
  let z := eqToIso (congrArg (completedConstantExtension X) (d.scalar_projection n))
  let o := Functor.isoWhiskerRight (Functor.isoWhiskerLeft C z) (V ⋙ U)
  let q := (AdicCompletion.evalₐ I (n + 1)).toRingHom
  let p := Functor.isoWhiskerRight (constantScalarChangeIso X q) (V ⋙ U)
  let r := Functor.isoWhiskerLeft
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} q ⋙ adicLisseConstantModules X (A ⧸ I ^ (n + 1)))
    (completedRestrictCompIso X β π).symm
  exact a ≪≫ b ≪≫ Functor.isoWhiskerLeft C k ≪≫
    Functor.isoWhiskerLeft C l ≪≫ m ≪≫ o ≪≫ p ≪≫ r

-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
-- Comparing the several bundled scalar-restriction presentations is expensive.
-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private def realizationUnitIso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (d : CompletedConstantModuleRealization X I)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) [IsIso β]
    (c : ModuleCat.{u + 1} (AdicCompletion I A) ⥤ completedConstantModules X R)
    (e : c ≅ completedConstantRealization X I d.scalar ⋙
      SheafOfModules.restrictScalars ((adicLisseForget X).map β)) :
    letI := SheafOfModules.cochainModulesMonoidal R
    c.obj (ModuleCat.of (AdicCompletion I A) (AdicCompletion I A)) ≅
      𝟙_ (completedConstantModules X R) := by
  let := SheafOfModules.cochainModulesMonoidal R
  let := SheafOfModules.cochainModulesMonoidal (adicLisseCompletedRing X I)
  let := HasDerivedCategory.standard (completedConstantModules X R)
  let := HasDerivedCategory.standard
    (completedConstantModules X (adicLisseCompletedRing X I))
  let tr := (SheafOfModules.ringIso_tensor_transport (asIso β)).some
  let U := SheafOfModules.restrictScalars ((adicLisseForget X).map β)
  letI : U.Braided := tr.monoidal
  exact e.app _ ≪≫ U.mapIso (CompletedConstantReduction.constantChange_unit X d.scalar) ≪≫
    (Functor.Monoidal.εIso U).symm

private theorem reduction_projection_step (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) (n : ℕ) :
    (β ≫ limit.π (adicLisseRingSystem X I) (op (n + 1))) ≫
        (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1))) =
      β ≫ limit.π (adicLisseRingSystem X I) (op n) := by
  rw [Category.assoc]
  have hw := limit.w (adicLisseRingSystem X I) (homOfLE (Nat.le_succ n)).op
  dsimp only [adicLisseRingSystem] at hw
  rw [Functor.ofOpSequence_map_homOfLE_succ] at hw
  exact congrArg (β ≫ ·) hw

-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private def reductionModuleStep (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) (n : ℕ) :
    reductionModuleLevel X I R β (n + 1) ⟶ reductionModuleLevel X I R β n where
  app M := constantSemilinear X (Ideal.Quotient.factorPowSucc I (n + 1)) R
    (β ≫ limit.π (adicLisseRingSystem X I) (op (n + 1)))
    (β ≫ limit.π (adicLisseRingSystem X I) (op n))
    (reduction_projection_step X I R β n)
    _ _ (scalarReductionMap _ _ _ (reduction_eval_step I n) M)
  naturality := by
    intro M N f
    exact constantSemilinear_naturality X (Ideal.Quotient.factorPowSucc I (n + 1)) R
      (β ≫ limit.π (adicLisseRingSystem X I) (op (n + 1)))
      (β ≫ limit.π (adicLisseRingSystem X I) (op n))
      (reduction_projection_step X I R β n) _ _ _ _
      (scalarReductionMap _ _ _ (reduction_eval_step I n) M)
      (scalarReductionMap _ _ _ (reduction_eval_step I n) N)
      ((ModuleCat.extendScalars (AdicCompletion.evalₐ I (n + 2)).toRingHom).map f)
      ((ModuleCat.extendScalars (AdicCompletion.evalₐ I (n + 1)).toRingHom).map f)
      (scalarReductionMap_naturality _ _ _ (reduction_eval_step I n) f)

private theorem reductionModuleStep_generator (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) (n : ℕ)
    (M : ModuleCat.{u + 1} (AdicCompletion I A)) (U : X.ProEtᵒᵖ)
    (p : A ⧸ I ^ (n + 2)) (x : M) :
    ((reductionModuleStep X I R β n).app M).val.app U
      (completedConstantGenerator X _ _ U
        (p ⊗ₜ[AdicCompletion I A, (AdicCompletion.evalₐ I (n + 2)).toRingHom] x)) =
      completedConstantGenerator X _ _ U
        (Ideal.Quotient.factorPowSucc I (n + 1) p ⊗ₜ[AdicCompletion I A,
          (AdicCompletion.evalₐ I (n + 1)).toRingHom] x) := by
  exact constantSemilinear_generator X (Ideal.Quotient.factorPowSucc I (n + 1)) R
    (β ≫ limit.π (adicLisseRingSystem X I) (op (n + 1)))
    (β ≫ limit.π (adicLisseRingSystem X I) (op n))
    (reduction_projection_step X I R β n) _ _
    (scalarReductionMap _ _ _ (reduction_eval_step I n) M) U _

-- The comparison uses the regular scalar-extension isomorphism on its source.
-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
-- Cache the complex diagram once for the tower and its comparison.
private def reductionComplexDiagram (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I)
    (h : ∀ n : ℕ, (adicLisseConstantModules X (A ⧸ I ^ (n + 1))).Additive) :
    ℕᵒᵖ ⥤ (CochainComplex (ModuleCat.{u + 1} (AdicCompletion I A)) ℤ ⥤
      CochainComplex (completedConstantModules X R) ℤ) := by
  have hL (n : ℕ) : (reductionModuleLevel X I R β n).Additive := by
    let := h n
    let := (ModuleCat.extendRestrictScalarsAdj.{0, u + 1, u + 1}
      (AdicCompletion.evalₐ I (n + 1)).toRingHom).isLeftAdjoint
    infer_instance
  letI (n : ℕ) : (reductionModuleLevel X I R β n).Additive := hL n
  exact Functor.ofOpSequence
    (X := fun n ↦ (reductionModuleLevel X I R β n).mapHomologicalComplex (.up ℤ))
    (fun n ↦ NatTrans.mapHomologicalComplex (reductionModuleStep X I R β n) (.up ℤ))

-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private def reductionTower (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I)
    (h : ∀ n : ℕ, (adicLisseConstantModules X (A ⧸ I ^ (n + 1))).Additive) :
    CompletedConstantReductionTower X I R β h := by
  let F := reductionComplexDiagram X I R β h
  refine
    { functor := F.flip
      level := fun _ _ ↦ rfl
      map_level := fun _ _ _ _ ↦ ?_
      transition := ?_ }
  · dsimp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · intro M n i U p x
    dsimp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change (((F.map (homOfLE (Nat.le_succ n)).op).app M).f i).val.app U
      (completedConstantGenerator X _ _ U (p ⊗ₜ[AdicCompletion I A,
        (AdicCompletion.evalₐ I (n + 2)).toRingHom] x)) = _
    dsimp only [F, reductionComplexDiagram]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact reductionModuleStep_generator X I R β n (M.X i) U p x

attribute [local irreducible] reductionTower

-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
-- Bundled sheaf and scalar-restriction conversions require extra elaboration.

private def isoOfOpSequence {D : Type*} [Category* D] {F G : ℕᵒᵖ ⥤ D}
    (e : ∀ n : ℕ, F.obj (op n) ≅ G.obj (op n))
    (h : ∀ n : ℕ, F.map (homOfLE (Nat.le_succ n)).op ≫ (e n).hom =
      (e (n + 1)).hom ≫ G.map (homOfLE (Nat.le_succ n)).op) : F ≅ G :=
  NatIso.ofComponents (fun n ↦ e n.unop)
    (fun f ↦ (NatTrans.ofOpSequence (fun n ↦ (e n).hom) h).naturality f)

-- Name the normalized module comparison before lifting it to complexes.
-- Check module transition compatibility independently of the cochain construction.
-- Keep the level isomorphism as a named term for kernel checking.
-- Check the complex successor square before assembling a sequence isomorphism.
-- Assemble the already checked components through a generic sequence constructor.
-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
private theorem flatOnSite_of_iso (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {M N : completedConstantModules X R} (e : M ≅ N)
    (hM : SheafOfModules.IsFlatOnSite (J := ProEt.topology X) (R := R) M) :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology X) (R := R) N := by
  let := SheafOfModules.cochainModulesMonoidal R
  let k := SheafOfModules.siteSheafTensorRightIso R M ≪≫
    (MonoidalCategory.curriedTensor _).flip.mapIso e ≪≫
      (SheafOfModules.siteSheafTensorRightIso R N).symm
  exact (exactFunctor _ _).prop_of_iso k hM

-- Bundled sheaf and scalar-restriction conversions require extra elaboration.
end AlgebraicGeometry.Scheme
