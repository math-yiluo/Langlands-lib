/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicLisseModuleSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantPresentation
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import WeilConjectures.AlgebraicGeometry.CompletedConstantProjection.CompletedConstantResidueData
import WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CoverLifting
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
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Completed scalar extension of constant residue modules

Source: Stacks Project, Tags 093J and 093M.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective
attribute [local irreducible] completedAdicChangeData completedAdicRing

private theorem isIso_of_regular
    {R : Type t} [CommRing R] {D : Type*} [Category D]
    {F G : ModuleCat.{t} R ⥤ D}
    [PreservesColimitsOfSize.{t, t} F] [PreservesColimitsOfSize.{t, t} G]
    [PreservesFiniteColimits F] [PreservesFiniteColimits G]
    (a : F ⟶ G) [IsIso (a.app (ModuleCat.of R R))]
    (M : ModuleCat.{t} R) : IsIso (a.app M) := by
  have hfree (I : Type t) : IsIso (a.app (ModuleCat.of R (I →₀ R))) := by
    let K := Discrete.functor (fun _ : I ↦ ModuleCat.of R R)
    have (i : Discrete I) : IsIso ((Functor.whiskerLeft K a).app i) :=
      inferInstanceAs (IsIso (a.app (ModuleCat.of R R)))
    have : IsIso (Functor.whiskerLeft K a) := NatIso.isIso_of_isIso_app _
    exact isIso_app_coconePt_of_preservesColimit K a
      (ModuleCat.finsuppCocone R R I) (ModuleCat.finsuppCoconeIsColimit R R I)
  let p := Finsupp.linearCombination R (id : M → M)
  let q := Finsupp.linearCombination R (id : LinearMap.ker p → LinearMap.ker p)
  let f := (LinearMap.ker p).subtype.comp q
  have hf : p.comp f = 0 := by ext; simp [f]
  let S := ModuleCat.shortComplexOfCompEqZero f p hf
  have hS : S.Exact := by
    apply ModuleCat.shortComplex_exact
    intro x
    change p x = 0 ↔ ∃ y, f y = x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := Finsupp.linearCombination_id_surjective R
        (LinearMap.ker p) ⟨x, hx⟩
      exact ⟨y, congrArg Subtype.val hy⟩
    · rintro ⟨y, rfl⟩
      exact congrArg (fun k : (LinearMap.ker p →₀ R) →ₗ[R] M ↦ k y) hf
  have : Epi S.g := (ModuleCat.epi_iff_surjective _).mpr
    (Finsupp.linearCombination_id_surjective R M)
  let K := parallelPair S.f 0
  have (j : WalkingParallelPair) : IsIso ((Functor.whiskerLeft K a).app j) := by
    cases j
    · exact hfree (LinearMap.ker p)
    · exact hfree M
  have : IsIso (Functor.whiskerLeft K a) := NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit K a
    (CokernelCofork.ofπ S.g S.zero) hS.gIsCokernel

section ResidueComparison

private def constantResidueMap
    (X : Scheme.{t}) {B D : Type (t + 1)} [CommRing B] [CommRing D]
  (q : B →+* D) {S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
  (c : adicLisseConstantRing X B ⟶ S) (p : S ⟶ adicLisseConstantRing X D)
  (hp : c ≫ p = (constantSheaf (ProEt.topology X) CommRingCat.{t + 1}).map
    (CommRingCat.ofHom q)) :
    ModuleCat.restrictScalars.{t + 1} q ⋙ adicLisseConstantModules X B ⟶
      adicLisseConstantModules X D ⋙
        SheafOfModules.restrictScalars ((adicLisseForget X).map p) ⋙
        SheafOfModules.restrictScalars ((adicLisseForget X).map c) where
  app N := CompletedConstantProjection.constantMap X q c p hp
    ((ModuleCat.restrictScalars.{t + 1} q).obj N) N
      { toFun := id, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  naturality M N f := by
    apply (SheafOfModules.toSheaf _).map_injective
    simp only [Functor.map_comp, CompletedConstantProjection.constantMap_underlying]
    change (constantSheaf (ProEt.topology X) AddCommGrpCat.{t + 1}).map
        ((forget₂ (ModuleCat.{t + 1} D) AddCommGrpCat.{t + 1}).map f) ≫
          (constantSheaf (ProEt.topology X) AddCommGrpCat.{t + 1}).map (𝟙 _) =
      (constantSheaf (ProEt.topology X) AddCommGrpCat.{t + 1}).map (𝟙 _) ≫
        (constantSheaf (ProEt.topology X) AddCommGrpCat.{t + 1}).map
          ((forget₂ (ModuleCat.{t + 1} D) AddCommGrpCat.{t + 1}).map f)
    erw [(constantSheaf (ProEt.topology X) AddCommGrpCat.{t + 1}).map_id,
      (constantSheaf (ProEt.topology X) AddCommGrpCat.{t + 1}).map_id]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

attribute [local irreducible] constantResidueMap

private def scalarResidueMap
    (X : Scheme.{t}) {B D : Type (t + 1)} [CommRing B] [CommRing D]
  (q : B →+* D) {S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
  (c : adicLisseConstantRing X B ⟶ S) (p : S ⟶ adicLisseConstantRing X D)
  (hp : c ≫ p = (constantSheaf (ProEt.topology X) CommRingCat.{t + 1}).map
    (CommRingCat.ofHom q)) :
    ModuleCat.restrictScalars.{t + 1} q ⋙ adicLisseConstantModules X B ⋙ completedAdicChange X c ⟶
      adicLisseConstantModules X D ⋙
        SheafOfModules.restrictScalars ((adicLisseForget X).map p) := by
  let a := (completedAdjunction X c).choose
  let g := constantResidueMap X q c p hp
  exact Functor.whiskerRight g (completedAdicChange X c) ≫
    Functor.whiskerLeft
      (adicLisseConstantModules X D ⋙
        SheafOfModules.restrictScalars ((adicLisseForget X).map p)) a.counit

attribute [local irreducible] scalarResidueMap

private lemma scalarResidueMap_tensor
    (X : Scheme.{t}) {B D : Type (t + 1)} [CommRing B] [CommRing D]
  (q : B →+* D) {S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
  (c : adicLisseConstantRing X B ⟶ S) (p : S ⟶ adicLisseConstantRing X D)
  (hp : c ≫ p = (constantSheaf (ProEt.topology X) CommRingCat.{t + 1}).map
    (CommRingCat.ofHom q)) (N : ModuleCat.{t + 1} D)
    (U : X.ProEtᵒᵖ) (s : S.obj.obj U) (x : N) :
    ((scalarResidueMap X q c p hp).app N).val.app U
      (completedAdicChangeTensor X c
        ((adicLisseConstantModules X B).obj ((ModuleCat.restrictScalars.{t + 1} q).obj N)) U s
        (completedConstantGenerator X B ((ModuleCat.restrictScalars.{t + 1} q).obj N) U x)) =
      p.hom.app U s • (show ((adicLisseConstantModules X D).obj N).val.obj U from
        completedConstantGenerator X D N U x) := by
  let a := (completedAdjunction X c).choose
  let g := constantResidueMap X q c p hp
  let M := (adicLisseConstantModules X B).obj ((ModuleCat.restrictScalars.{t + 1} q).obj N)
  let H := (SheafOfModules.restrictScalars ((adicLisseForget X).map p)).obj
    ((adicLisseConstantModules X D).obj N)
  let r : (completedAdicChange X c).obj M ⟶ H := (scalarResidueMap X q c p hp).app N
  let y := completedConstantGenerator X B ((ModuleCat.restrictScalars.{t + 1} q).obj N) U x
  have he : a.homEquiv M H r = g.app N := by
    simp only [r, scalarResidueMap, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    change a.homEquiv M H ((completedAdicChange X c).map (g.app N) ≫
      a.counit.app H) = g.app N
    rw [← a.homEquiv_counit]
    exact (a.homEquiv M H).apply_symm_apply _
  have ht : r.val.app U (completedAdicChangeTensor X c M U 1 y) =
      (g.app N).val.app U y := by
    rw [← (completedAdjunction X c).choose_spec M H r U y]
    rw [he]
    rfl
  have hs : completedAdicChangeTensor X c M U s y =
      s • completedAdicChangeTensor X c M U 1 y := by
    simpa only [mul_one] using completedTensor_smul X c M U s 1 y
  change r.val.app U (completedAdicChangeTensor X c M U s y) = _
  rw [hs, (r.val.app U).hom.map_smul, ht]
  change p.hom.app U s •
      (show ((adicLisseConstantModules X D).obj N).val.obj U from (g.app N).val.app U y) = _
  apply congrArg (fun z : ((adicLisseConstantModules X D).obj N).val.obj U ↦
    p.hom.app U s • z)
  simp only [g, constantResidueMap, y]
  exact CompletedConstantProjection.constantMap_generator X q c p hp
    ((ModuleCat.restrictScalars.{t + 1} q).obj N) N
    { toFun := id, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl } U x

end ResidueComparison

private theorem scalarResidueMap_regular_isIso
    (X : Scheme.{t}) {B : Type (t + 1)} [CommRing B] [IsNoetherianRing B]
    (I : Ideal B) {S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (e : adicLisseCompletedRing X I ≅ S) (c : adicLisseConstantRing X B ⟶ S)
    (hc : ∀ n, c ≫ e.inv ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{t + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) (n : ℕ) :
    IsIso ((scalarResidueMap X (Ideal.Quotient.mk (I ^ (n + 1))) c
      (e.inv ≫ limit.π (adicLisseRingSystem X I) (op n)) (hc n)).app
        (ModuleCat.of (B ⧸ I ^ (n + 1)) (B ⧸ I ^ (n + 1)))) := by
  let Q := B ⧸ I ^ (n + 1)
  let p : S ⟶ adicLisseConstantRing X (B ⧸ I ^ (n + 1)) :=
    e.inv ≫ limit.π (adicLisseRingSystem X I) (op n)
  let r := (scalarResidueMap X (Ideal.Quotient.mk (I ^ (n + 1))) c p (hc n)).app
    (ModuleCat.of Q Q)
  let u : (adicLisseConstantModules X Q).obj (ModuleCat.of Q Q) ≅
      SheafOfModules.unit (adicLisseRing X Q) :=
    directUnitIso (adicLisseConstantUnit X Q)
  let w := (SheafOfModules.restrictScalars ((adicLisseForget X).map p)).map u.hom
  have hu (U : X.ProEtᵒᵖ) (x : Q) :
      u.hom.val.app U (completedConstantGenerator X Q (ModuleCat.of Q Q) U x) =
        (adicLisseConstantUnit X Q).app U x := by
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (directUnitMap_unit (adicLisseConstantUnit X Q)) U) x
  have : IsIso (r ≫ w) :=
    (completed_constant_algebra_flat_quotients X I S e c hc).2.2 n
      (adicLisseConstantRing X Q) (Iso.refl _) p (by dsimp only [p]; erw [Category.comp_id])
      (r ≫ w) (by
        intro U s x
        change u.hom.val.app U (r.val.app U
          (completedAdicChangeTensor X c
            ((adicLisseConstantModules X B).obj (ModuleCat.of B Q)) U s
            (completedConstantGenerator X B (ModuleCat.of B Q) U x))) = _
        erw [scalarResidueMap_tensor X (Ideal.Quotient.mk (I ^ (n + 1))) c p
          (hc n) (ModuleCat.of Q Q) U s x, (u.hom.val.app U).hom.map_smul, hu]
        rfl)
  exact IsIso.of_isIso_comp_right r w

private theorem scalarResidueMap_isIso
    (X : Scheme.{t}) {B : Type (t + 1)} [CommRing B] [IsNoetherianRing B]
    (I : Ideal B) {S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (e : adicLisseCompletedRing X I ≅ S) (c : adicLisseConstantRing X B ⟶ S)
    (hc : ∀ n, c ≫ e.inv ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{t + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
    (n : ℕ) (N : ModuleCat.{t + 1} (B ⧸ I ^ (n + 1))) :
    IsIso ((scalarResidueMap X (Ideal.Quotient.mk (I ^ (n + 1))) c
      (e.inv ≫ limit.π (adicLisseRingSystem X I) (op n)) (hc n)).app N) := by
  have : PreservesColimitsOfSize.{t + 1, t + 1} (adicLisseConstantModules X B) := by
    change PreservesColimitsOfSize.{t + 1, t + 1}
      (directConstant (R := adicLisseRing X B) (adicLisseConstantUnit X B))
    infer_instance
  let Q := B ⧸ I ^ (n + 1)
  have : PreservesColimitsOfSize.{t + 1, t + 1} (adicLisseConstantModules X Q) := by
    change PreservesColimitsOfSize.{t + 1, t + 1}
      (directConstant (R := adicLisseRing X Q) (adicLisseConstantUnit X Q))
    infer_instance
  have := (completedAdjunction X c).choose.isLeftAdjoint
  have := (ModuleCat.restrictCoextendScalarsAdj.{t + 1, t + 1, t + 1}
    (Ideal.Quotient.mk (I ^ (n + 1)))).isLeftAdjoint
  let p : S ⟶ adicLisseConstantRing X (B ⧸ I ^ (n + 1)) :=
    e.inv ≫ limit.π (adicLisseRingSystem X I) (op n)
  let P := SheafOfModules.restrictScalars.{t + 1} ((adicLisseForget X).map p)
  let T := SheafOfModules.toSheaf.{t + 1} ((adicLisseForget X).obj S)
  have : PreservesColimitsOfSize.{t + 1, t + 1}
      (SheafOfModules.toSheaf.{t + 1} (adicLisseRing X Q)) := by
    constructor
    intro K _
    exact ((moduleSheaves_colimits_forgetful.{_, _, _, t + 1} (adicLisseRing X Q)).2.2.2.2.2 K).2.1
  have : PreservesColimitsOfSize.{t + 1, t + 1} T := by
    constructor
    intro K _
    exact ((moduleSheaves_colimits_forgetful.{_, _, _, t + 1}
      ((adicLisseForget X).obj S)).2.2.2.2.2 K).2.1
  have : ReflectsColimitsOfSize.{t + 1, t + 1} T :=
    reflectsColimits_of_reflectsIsomorphisms
  have : PreservesColimitsOfSize.{t + 1, t + 1} (P ⋙ T) :=
    inferInstanceAs (PreservesColimitsOfSize.{t + 1, t + 1}
      (SheafOfModules.toSheaf (adicLisseRing X Q)))
  have : PreservesColimitsOfSize.{t + 1, t + 1} P :=
    preservesColimits_of_reflects_of_preserves P T
  have : IsIso ((scalarResidueMap X (Ideal.Quotient.mk (I ^ (n + 1))) c p
      (hc n)).app (ModuleCat.of Q Q)) := scalarResidueMap_regular_isIso X I e c hc n
  exact isIso_of_regular
    (F := ModuleCat.restrictScalars.{t + 1} (Ideal.Quotient.mk (I ^ (n + 1))) ⋙
      adicLisseConstantModules X B ⋙ completedAdicChange X c)
    (G := adicLisseConstantModules X Q ⋙ P)
    (scalarResidueMap X (Ideal.Quotient.mk (I ^ (n + 1))) c p (hc n)) N

end AlgebraicGeometry.Scheme
