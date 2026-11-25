/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalDerivedReductionExists
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Triangulated.Functor
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset
import all WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
import WeilConjectures.AlgebraicGeometry.Integral.Strict.IntegralStrictCompletionReflector
import Mathlib.Algebra.Module.ZMod
import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Completion of simultaneous reduction on the pro-etale site
Source: diagonal tower proof step 4; Stacks Tags 099M, 091S and 091Z. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a b v w r va vb
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

open CategoryTheory.RingedStrictTowerProof

private theorem derivedLimitRestriction
    {A : Type a} [Category.{v} A] [Abelian A]
    {B : Type b} [Category.{w} B] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{r} A] [HasDerivedCategory.{r} B]
    [HasDerivedCategory.{r} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{r} (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape ℕᵒᵖ F]
    [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F)]
    [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F)]
    [((Functor.whiskeringRight ℕᵒᵖ A B).obj F).PreservesKInjectiveComplexes]
    (LA : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory A)
    (LB : DerivedCategory (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory B)
    (ηA : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LA)
    (ηB : (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LB)
    (hA : ∀ P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      P.IsKInjective → IsIso (ηA.app P))
    (hB : ∀ P : CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
      P.IsKInjective → IsIso (ηB.app P)) :
    Nonempty (LA ⋙ F.mapDerivedCategory ≅
      ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategory ⋙ LB) := by
  let FT := (Functor.whiskeringRight ℕᵒᵖ A B).obj F
  have : PreservesFiniteLimits FT := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits FT := ⟨fun _ _ _ ↦ inferInstance⟩
  have : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive :=
    Functor.additive_of_preserves_binary_products _
  obtain ⟨e, _⟩ := towerComparison_existsLimitIso F F.mapDerivedCategory
    FT.mapDerivedCategory LA LB F.mapDerivedCategoryFactors.inv
    FT.mapDerivedCategoryFactors.inv ηA ηB (fun _ _ ↦ inferInstance)
    (fun _ _ ↦ inferInstance) hA (fun P hP ↦ by
      have := hP
      exact hB _ inferInstance) (preservesLimitNatIso F)
  exact ⟨e⟩

private instance diagonalForgetTowerFiniteLimits (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ (DiagonalMod ℓ W)
      (DiagonalAb W)).obj (diagonalForget ℓ W)) := ⟨fun _ _ _ ↦ inferInstance⟩
private instance diagonalForgetTowerFiniteColimits (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ (DiagonalMod ℓ W)
      (DiagonalAb W)).obj (diagonalForget ℓ W)) := ⟨fun _ _ _ ↦ inferInstance⟩
private theorem derivedLimits_exists (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb W)] :
    ∃ (RF : DerivedCategory (DiagonalSystems ℓ W) ⥤ DerivedCategory (DiagonalMod ℓ W))
      (η : (lim : DiagonalSystems ℓ W ⥤ DiagonalMod ℓ W).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
      (RZ : DerivedCategory (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DerivedCategory (DiagonalAb W))
      (ηZ : (lim : (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DiagonalAb W).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RZ),
      RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso (DiagonalSystems ℓ W) (.up ℤ)) ∧
      RZ.IsRightDerivedFunctor ηZ
        (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ DiagonalAb W) (.up ℤ)) ∧
      Nonempty (RF ⋙ (diagonalForget ℓ W).mapDerivedCategory ≅
        ((Functor.whiskeringRight ℕᵒᵖ (DiagonalMod ℓ W) (DiagonalAb W)).obj
          (diagonalForget ℓ W)).mapDerivedCategory ⋙ RZ) := by
  have : IsGrothendieckAbelian.{u + 1} (DiagonalSystems ℓ W) :=
    tower_grothendieck (DiagonalMod ℓ W)
  have : IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb W) :=
    tower_grothendieck (DiagonalAb W)
  have : (lim : DiagonalSystems ℓ W ⥤ DiagonalMod ℓ W).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (lim : (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DiagonalAb W).Additive :=
    Functor.additive_of_preserves_binary_products _
  obtain ⟨RF, η, hu, hc, _⟩ := totalDerivedData
    (lim : DiagonalSystems ℓ W ⥤ DiagonalMod ℓ W)
  obtain ⟨RZ, ηZ, hzu, hzc, _⟩ := totalDerivedData
    (lim : (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DiagonalAb W)
  have : PreservesFiniteLimits (diagonalScalarExtension ℓ W) := scalarExtension_exact ℓ W
  have : PreservesFiniteColimits (diagonalScalarExtension ℓ W) := by
    have := (diagonalScalarAdjunction ℓ W).leftAdjoint_preservesColimits
    infer_instance
  have : (diagonalScalarExtension ℓ W).Additive := scalarExtension_additive ℓ W
  let E := (Functor.whiskeringRight ℕᵒᵖ (DiagonalAb W) (DiagonalMod ℓ W)).obj
    (diagonalScalarExtension ℓ W)
  have : E.Additive := inferInstance
  have : PreservesFiniteLimits E := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits E := ⟨fun _ _ _ ↦ inferInstance⟩
  have : E.PreservesHomology := {}
  let FT := (Functor.whiskeringRight ℕᵒᵖ (DiagonalMod ℓ W) (DiagonalAb W)).obj
    (diagonalForget ℓ W)
  have : PreservesFiniteLimits FT := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits FT := ⟨fun _ _ _ ↦ inferInstance⟩
  have adj := Adjunction.whiskerRight ℕᵒᵖ (diagonalScalarAdjunction ℓ W)
  have : ((Functor.whiskeringRight ℕᵒᵖ (DiagonalMod ℓ W) (DiagonalAb W)).obj
      (diagonalForget ℓ W)).PreservesKInjectiveComplexes := adj.preservesKInjectiveComplexes
  have : PreservesLimitsOfShape ℕᵒᵖ (diagonalForget ℓ W) := by
    have := (diagonalScalarAdjunction ℓ W).rightAdjoint_preservesLimits
    infer_instance
  exact ⟨RF, η, RZ, ηZ, hu, hzu, derivedLimitRestriction (diagonalForget ℓ W)
    RF RZ η ηZ hc hzc⟩

private theorem padic_map_smul {ℓ : ℕ} [Fact ℓ.Prime]
    {M : Type u} [AddCommGroup M] [Module (ULift.{v} ℤ_[ℓ]) M]
    {N : Type u} [AddCommGroup N] [Module (ULift.{v} ℤ_[ℓ]) N]
    (n : ℕ) (hM : ∀ x : M, (ℓ ^ n) • x = 0) (f : M →+ N)
    (r : ULift.{v} ℤ_[ℓ]) (x : M) : f (r • x) = r • f x := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (r.down.appr_spec n)
  have hr : r - (r.down.appr n : ULift.{v} ℤ_[ℓ]) =
      (ULift.up a) * (ℓ : ULift.{v} ℤ_[ℓ]) ^ n := by
    apply ULift.ext
    exact ha.symm
  have hN : (ℓ ^ n) • f x = 0 := by rw [← map_nsmul, hM, map_zero]
  have hsplit (y : M) : r • y = r.down.appr n • y := by
    conv_lhs => rw [← sub_add_cancel r (r.down.appr n : ULift.{v} ℤ_[ℓ]), hr]
    rw [add_smul, mul_smul]
    simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hM, smul_zero, zero_add]
  rw [hsplit, map_nsmul]
  conv_rhs => rw [← sub_add_cancel r (r.down.appr n : ULift.{v} ℤ_[ℓ]), hr]
  rw [add_smul, mul_smul]
  simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hN, smul_zero, zero_add]
private def padicLift (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) (n : ℕ)
    (Q N : DiagonalMod ℓ W) (hQ : (ℓ ^ n) • 𝟙 Q = 0)
    (f : (diagonalForget ℓ W).obj Q ⟶ (diagonalForget ℓ W).obj N) : Q ⟶ N :=
  ObjectProperty.homMk
    { app U := by
        let g : (Q.obj.obj U) →+ (N.obj.obj U) := (f.hom.app U).hom
        exact ModuleCat.ofHom
          { toFun := g
            map_add' := g.map_add
            map_smul' r x := padic_map_smul n (fun y ↦ by
              have h := congrArg (fun k : Q ⟶ Q ↦ k.hom.app U y) hQ
              exact h) g r x }
      naturality U V i := by
        apply (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ]))
          AddCommGrpCat.{u + 1}).map_injective
        exact f.hom.naturality i }

private theorem padicLift_forget (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) (n : ℕ)
    (Q N : DiagonalMod ℓ W) (hQ : (ℓ ^ n) • 𝟙 Q = 0)
    (f : (diagonalForget ℓ W).obj Q ⟶ (diagonalForget ℓ W).obj N) :
    (diagonalForget ℓ W).map (padicLift ℓ W n Q N hQ f) = f := rfl

private theorem quotientAdjunction
    {A : Type a} [Category.{va} A] [Abelian A]
    {B : Type b} [Category.{vb} B] [Abelian B]
    (L : A ⥤ B) (F : B ⥤ A) [L.Additive] [F.Additive] [F.Faithful]
    (adj : L ⊣ F) (n : ℕ) (S : A) (Q : B)
    (q : S ⟶ F.obj Q) (w : (n • 𝟙 S) ≫ q = 0)
    (hq : IsColimit (CokernelCofork.ofπ q w))
    (lift : ∀ N : B, (F.obj Q ⟶ F.obj N) → (Q ⟶ N))
    (hlift : ∀ (N : B) (f : F.obj Q ⟶ F.obj N), F.map (lift N f) = f) :
    ∃ w' : (n • 𝟙 (L.obj S)) ≫ (adj.homEquiv S Q).symm q = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ ((adj.homEquiv S Q).symm q) w')) := by
  let π := (adj.homEquiv S Q).symm q
  have hw : (n • 𝟙 (L.obj S)) ≫ π = 0 := by
    apply (adj.homEquiv S Q).injective
    rw [← L.map_id S, ← L.map_nsmul, adj.homEquiv_naturality_left,
      Equiv.apply_symm_apply, w, adj.homAddEquiv_zero]
  let c (N : B) (k : L.obj S ⟶ N) (hk : (n • 𝟙 (L.obj S)) ≫ k = 0) :
      CokernelCofork (n • 𝟙 S) :=
    CokernelCofork.ofπ (adj.homEquiv S N k) (by
      rw [← adj.homEquiv_naturality_left, L.map_nsmul, L.map_id, hk,
        adj.homAddEquiv_zero])
  refine ⟨hw, ⟨CokernelCofork.IsColimit.ofπ π hw
    (fun {N} k hk ↦ lift N (hq.desc (c N k hk)))
    (fun {N} k hk ↦ ?_) (fun {N} k hk m hm ↦ ?_)⟩⟩
  · apply (adj.homEquiv S N).injective
    rw [adj.homEquiv_naturality_right]
    dsimp only [π]
    rw [Equiv.apply_symm_apply, hlift]
    exact hq.fac (c N k hk) WalkingParallelPair.one
  · apply F.map_injective
    apply Cofork.IsColimit.hom_ext hq
    change q ≫ F.map m = q ≫ F.map (lift N (hq.desc (c N k hk)))
    rw [hlift]
    calc
      q ≫ F.map m = (adj.homEquiv S N) k := by
        have h := congrArg (adj.homEquiv S N) hm
        simpa only [adj.homEquiv_naturality_right, π, Equiv.apply_symm_apply] using h
      _ = q ≫ hq.desc (c N k hk) := (hq.fac (c N k hk) WalkingParallelPair.one).symm

private def padicOfKilled (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) (n : ℕ)
    (M : DiagonalAb W) (hm : (ℓ ^ n) • 𝟙 M = 0) : DiagonalMod ℓ W := by
  let modu (U : W.ProEtᵒᵖ) : Module (ZMod (ℓ ^ n)) (M.obj.obj U) :=
    AddCommGroup.zmodModule (fun x ↦ by
      have h := congrArg (fun k : M ⟶ M ↦ k.hom.app U x) hm
      exact h)
  let F : W.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ZMod (ℓ ^ n)) :=
    { obj := fun U ↦ by
        let := modu U
        exact ModuleCat.of _ (M.obj.obj U)
      map := fun {U V} f ↦ by
        let := modu U
        let := modu V
        exact ModuleCat.ofHom ((M.obj.map f).hom.toZModLinearMap (ℓ ^ n))
      map_id := by intro U; ext x; exact congrArg (fun k ↦ k x) (M.obj.map_id U)
      map_comp := by intro U V T f g; ext x
                     exact congrArg (fun k ↦ k x) (M.obj.map_comp f g) }
  let P := F ⋙ ModuleCat.restrictScalars
    ((PadicInt.toZModPow n).comp ULift.ringEquiv.toRingHom)
  exact ⟨P, Presheaf.isSheaf_of_isSheaf_comp _ _
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) AddCommGrpCat.{u + 1})
    M.property⟩

private theorem presentation_killed
    {A : Type a} [Category.{va} A] [Abelian A]
    {B : Type b} [Category.{vb} B] [Abelian B]
    (ℓ : ℕ) (L : A ⥤ B) (O : DiagonalReductionPresentation ℓ L) (n : ℕ) (M : A) :
    (ℓ ^ (n + 1)) • 𝟙 ((O.E.obj M).obj (op n)) = 0 := by
  have : Epi ((O.π n).app M) := Cofork.IsColimit.epi (O.quotient n M)
  apply (cancel_epi ((O.π n).app M)).mp
  change (O.π n).app M ≫ (ℓ ^ (n + 1) • 𝟙 _) = (O.π n).app M ≫ 0
  calc
    (O.π n).app M ≫ (ℓ ^ (n + 1) • 𝟙 _) =
        (ℓ ^ (n + 1) • 𝟙 _) ≫ (O.π n).app M := by
      simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp]
      congr 1
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    _ = 0 := O.zero n M
    _ = (O.π n).app M ≫ 0 := comp_zero.symm

private theorem ordinary_level_comparison (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (O : DiagonalReductionPresentation ℓ (diagonalScalarExtension ℓ W))
    (I : DiagonalReductionPresentation ℓ (𝟭 (DiagonalAb W)))
    (n : ℕ) (M : DiagonalAb W) :
    ∃ e : (diagonalForget ℓ W).obj ((O.E.obj M).obj (op n)) ≅
      (I.E.obj M).obj (op n),
      (diagonalScalarAdjunction ℓ W).unit.app M ≫
        (diagonalForget ℓ W).map ((O.π n).app M) ≫ e.hom = (I.π n).app M := by
  let F := diagonalForget ℓ W
  have : F.Faithful := by
    dsimp only [F, diagonalForget]
    infer_instance
  have : (diagonalForget ℓ W).Additive := diagonalForget_additive ℓ W
  have : (diagonalScalarExtension ℓ W).Additive :=
    (diagonalScalarAdjunction ℓ W).left_adjoint_additive
  let Q := padicOfKilled ℓ W (n + 1) ((I.E.obj M).obj (op n))
    (presentation_killed ℓ (𝟭 _) I n M)
  let q : M ⟶ F.obj Q := (I.π n).app M
  obtain ⟨w, ⟨hc⟩⟩ := quotientAdjunction (diagonalScalarExtension ℓ W) F
    (diagonalScalarAdjunction ℓ W) (ℓ ^ (n + 1)) M Q q (I.zero n M) (I.quotient n M)
    (fun N f ↦ padicLift ℓ W (n + 1) Q N (by
      apply F.map_injective
      rw [F.map_nsmul, F.map_id, F.map_zero]
      exact presentation_killed ℓ (𝟭 _) I n M) f)
    (fun N f ↦ padicLift_forget ℓ W (n + 1) Q N _ f)
  let e := F.mapIso ((O.quotient n M).coconePointUniqueUpToIso hc)
  refine ⟨e, ?_⟩
  change (diagonalScalarAdjunction ℓ W).unit.app M ≫ F.map ((O.π n).app M) ≫
    F.map ((O.quotient n M).coconePointUniqueUpToIso hc).hom = _
  have he : (O.π n).app M ≫
      ((O.quotient n M).coconePointUniqueUpToIso hc).hom =
        ((diagonalScalarAdjunction ℓ W).homEquiv M Q).symm q :=
    (O.quotient n M).comp_coconePointUniqueUpToIso_hom hc WalkingParallelPair.one
  rw [← F.map_comp, he]
  exact ((diagonalScalarAdjunction ℓ W).homEquiv M Q).apply_symm_apply q

private def ordinaryComparison (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (O : DiagonalReductionPresentation ℓ (diagonalScalarExtension ℓ W))
    (I : DiagonalReductionPresentation ℓ (𝟭 (DiagonalAb W))) :
    O.E ⋙ (Functor.whiskeringRight ℕᵒᵖ (DiagonalMod ℓ W) (DiagonalAb W)).obj
      (diagonalForget ℓ W) ≅ I.E := by
  classical
  let e (M : DiagonalAb W) (n : ℕ) := (ordinary_level_comparison ℓ W O I n M).choose
  have he (M : DiagonalAb W) (n : ℕ) :
      (diagonalScalarAdjunction ℓ W).unit.app M ≫
        (diagonalForget ℓ W).map ((O.π n).app M) ≫ (e M n).hom = (I.π n).app M :=
    (ordinary_level_comparison ℓ W O I n M).choose_spec
  have he' (M : DiagonalAb W) (n : ℕ) :
      ((diagonalScalarAdjunction ℓ W).unit.app M ≫
        (diagonalForget ℓ W).map ((O.π n).app M)) ≫ (e M n).hom = (I.π n).app M := by
    simpa only [Category.assoc] using he M n
  have epi (M : DiagonalAb W) (n : ℕ) :
      Epi ((diagonalScalarAdjunction ℓ W).unit.app M ≫
        (diagonalForget ℓ W).map ((O.π n).app M)) := by
    have : Epi ((I.π n).app M) := Cofork.IsColimit.epi (I.quotient n M)
    have : Epi (((diagonalScalarAdjunction ℓ W).unit.app M ≫
        (diagonalForget ℓ W).map ((O.π n).app M)) ≫ (e M n).hom) := by
      simpa only [Category.assoc, he] using this
    exact (epi_comp_iff_of_isIso ((diagonalScalarAdjunction ℓ W).unit.app M ≫
      (diagonalForget ℓ W).map ((O.π n).app M)) (e M n).hom).mp inferInstance
  let en (M : DiagonalAb W) :
      (O.E.obj M) ⋙ diagonalForget ℓ W ≅ I.E.obj M :=
    NatIso.ofComponents (fun n ↦ e M n.unop) (by
      intro n m f
      apply (cancel_epi ((diagonalScalarAdjunction ℓ W).unit.app M ≫
        (diagonalForget ℓ W).map ((O.π n.unop).app M))).mp
      change _ ≫ (diagonalForget ℓ W).map ((O.E.obj M).map f) ≫ (e M m.unop).hom = _
      have trans (R : DiagonalReductionPresentation ℓ (𝟭 (DiagonalAb W))) :
          (R.π n.unop).app M ≫ (R.E.obj M).map f = (R.π m.unop).app M := by
        let tr := NatTrans.ofOpSequence (F := (Functor.const ℕᵒᵖ).obj M)
          (G := R.E.obj M) (fun i ↦ (R.π i).app M) (fun i ↦ by
            simpa using (R.transition i M).symm)
        exact (tr.naturality f).symm.trans (Category.id_comp _)
      have transO : (O.π n.unop).app M ≫ (O.E.obj M).map f = (O.π m.unop).app M := by
        let tr := NatTrans.ofOpSequence
          (F := (Functor.const ℕᵒᵖ).obj ((diagonalScalarExtension ℓ W).obj M))
          (G := O.E.obj M) (fun i ↦ (O.π i).app M) (fun i ↦ by
            simpa using (O.transition i M).symm)
        exact (tr.naturality f).symm.trans (Category.id_comp _)
      simp only [Category.assoc]
      rw [← Category.assoc ((diagonalForget ℓ W).map _), ← Functor.map_comp,
        transO, ← Category.assoc]
      rw [Category.assoc, he]
      calc
        (I.π m.unop).app M =
            (I.π n.unop).app M ≫ (I.E.obj M).map f := (trans I).symm
        _ = _ := by
          rw [← he' M n.unop]
          simp only [Category.assoc]
      )
  exact NatIso.ofComponents en (by
    intro M N f
    apply NatTrans.ext
    funext n
    apply (cancel_epi ((diagonalScalarAdjunction ℓ W).unit.app M ≫
      (diagonalForget ℓ W).map ((O.π n.unop).app M))).mp
    change ((diagonalScalarAdjunction ℓ W).unit.app M ≫
      (diagonalForget ℓ W).map ((O.π n.unop).app M)) ≫
        (diagonalForget ℓ W).map ((O.E.map f).app n) ≫ (e N n.unop).hom =
      ((diagonalScalarAdjunction ℓ W).unit.app M ≫
        (diagonalForget ℓ W).map ((O.π n.unop).app M)) ≫
          (e M n.unop).hom ≫ (I.E.map f).app n
    rw [Category.assoc, ← Category.assoc ((diagonalForget ℓ W).map _),
      ← Functor.map_comp]
    have hO : (diagonalScalarExtension ℓ W).map f ≫ (O.π n.unop).app N =
        (O.π n.unop).app M ≫ (O.E.map f).app n := (O.π n.unop).naturality f
    rw [← hO, Functor.map_comp]
    have hu : (diagonalScalarAdjunction ℓ W).unit.app M ≫
        (diagonalForget ℓ W).map ((diagonalScalarExtension ℓ W).map f) =
      f ≫ (diagonalScalarAdjunction ℓ W).unit.app N :=
        ((diagonalScalarAdjunction ℓ W).unit.naturality f).symm
    simp only [← Category.assoc] at hu ⊢
    rw [hu]
    simp only [Category.assoc]
    rw [he]
    calc
      f ≫ (I.π n.unop).app N =
          (I.π n.unop).app M ≫ (I.E.map f).app n := (I.π n.unop).naturality f
      _ = _ := by
        rw [← he' M n.unop]
        simp only [Category.assoc])

attribute [local irreducible] ordinaryComparison padicOfKilled padicLift
  diagonalScalarExtension diagonalForget diagonalScalarAdjunction

private theorem exactDerived_rightAdjoint
    {A : Type a} [Category.{va} A] [Abelian A] [HasDerivedCategory.{r} A]
    {B : Type b} [Category.{vb} B] [Abelian B] [HasDerivedCategory.{r} B]
    (L : A ⥤ B) (F : B ⥤ A) [L.Additive] [F.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : L ⊣ F) :
    F.mapDerivedCategory.IsRightAdjoint := adj.onDerivedCategory.isRightAdjoint

private theorem derivedReductionComparison
    {A : Type a} [Category.{va} A] [Abelian A] [HasDerivedCategory.{r} A]
    {B : Type b} [Category.{vb} B] [Abelian B] [HasDerivedCategory.{r} B]
    {C : Type v} [Category.{w} C] [Abelian C] [HasDerivedCategory.{r} C]
    (E : A ⥤ B) [E.Additive] (I : A ⥤ C) [I.Additive]
    (T : DerivedCategory A ⥤ DerivedCategory B)
    (U : DerivedCategory A ⥤ DerivedCategory C)
    (ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ε' : DerivedCategory.Q ⋙ U ⟶ I.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [T.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ))]
    [U.IsLeftDerivedFunctor ε' (HomologicalComplex.quasiIso A (.up ℤ))]
    [(E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).HasPointwiseLeftDerivedFunctor
      (HomologicalComplex.quasiIso A (.up ℤ))]
    (F : B ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.mapDerivedCategory.IsRightAdjoint] (e : E ⋙ F ≅ I) :
    Nonempty (T ⋙ F.mapDerivedCategory ≅ U) := by
  let G := E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  let α : DerivedCategory.Q ⋙ (T ⋙ F.mapDerivedCategory) ⟶ G ⋙ F.mapDerivedCategory :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε F.mapDerivedCategory
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension T ε
    (HomologicalComplex.quasiIso A (.up ℤ))
  have := G.hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor
    DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  have : (T ⋙ F.mapDerivedCategory).IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso A (.up ℤ)) :=
    ⟨Functor.PreservesRightKanExtension.preserves (G := F.mapDerivedCategory) T ε⟩
  let τ : G ⋙ F.mapDerivedCategory ≅ I.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (E.mapHomologicalComplex (.up ℤ)) F.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ F)) (.up ℤ)).symm ≪≫
          NatIso.mapHomologicalComplex e (.up ℤ)) DerivedCategory.Q
  exact ⟨Functor.leftDerivedNatIso _ _ α ε'
    (HomologicalComplex.quasiIso A (.up ℤ)) τ⟩

private theorem ordinaryDerivedComparison (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W))
    (I : DiagonalDerivedReduction ℓ (𝟭 (DiagonalAb W)))
    [PreservesFiniteLimits (diagonalScalarExtension ℓ W)] :
    Nonempty (D.T ⋙ ((Functor.whiskeringRight ℕᵒᵖ (DiagonalMod ℓ W)
      (DiagonalAb W)).obj (diagonalForget ℓ W)).mapDerivedCategory ≅ I.T) := by
  let FT := (Functor.whiskeringRight ℕᵒᵖ (DiagonalMod ℓ W) (DiagonalAb W)).obj
    (diagonalForget ℓ W)
  let ET := (Functor.whiskeringRight ℕᵒᵖ (DiagonalAb W) (DiagonalMod ℓ W)).obj
    (diagonalScalarExtension ℓ W)
  have : (diagonalScalarExtension ℓ W).Additive :=
    (diagonalScalarAdjunction ℓ W).left_adjoint_additive
  have : PreservesFiniteColimits (diagonalScalarExtension ℓ W) := by
    have := (diagonalScalarAdjunction ℓ W).leftAdjoint_preservesColimits
    infer_instance
  have : PreservesFiniteLimits ET := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits ET := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteLimits FT := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits FT := ⟨fun _ _ _ ↦ inferInstance⟩
  have : FT.mapDerivedCategory.IsRightAdjoint :=
    exactDerived_rightAdjoint ET FT
      (Adjunction.whiskerRight ℕᵒᵖ (diagonalScalarAdjunction ℓ W))
  have := D.universal
  have := D.pointwise
  have := I.universal
  exact derivedReductionComparison D.ordinary.E I.ordinary.E D.T I.T D.ε I.ε FT
    (ordinaryComparison ℓ W D.ordinary I.ordinary)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Simultaneous reduction followed by total derived limit is the integral
ell-completion reflector, with its constant Z_l action retained.

Source: blueprint diagonal tower proof step 4; Stacks Tags 099M, 091S, 091Z
(blueprint: lem-sfb-diagonal-reduction-completion).

Proof: use the exact extension/restriction adjunction for Z to Z_l, since Z_l is
Z-flat. Its levelwise adjunction on strict towers has exact left adjoint, so
restriction preserves K-injective complexes. Grothendieckness of both tower
categories supplies K-injective resolutions and the total right derived limits.
Restriction commutes with their ordinary limits by the projection universal
property, hence also with their total derived limits. The quotient cokernel
properties give the normalized ordinary comparison with the integral reduction
tower, since Z_l/ell^(n+1) is Z/ell^(n+1); its transition squares commute by the
quotient generators. The exact derived restriction is a right adjoint, hence preserves the pointwise
right Kan extension defining the left derived reduction. Uniqueness descends
this comparison by the two left-derived universal properties. This gives the
natural comparison of the two completed functors required in the conclusion.
For the integral tower apply the principal-ideal completion theorem to the
constant integer ring on the small pro-etale site, using the equivalence with
fixed-scalar module sheaves and then with abelian sheaves. Its unit comes from
all quotient maps and is natural in the input complex. The principal-ideal
criterion identifies its complete objects with right orthogonality to complexes
on which ell is invertible. The completion theorem gives complete outputs and
the universal Hom bijection. Transport the unit and these two properties along
the preceding natural comparison. This works for unbounded complexes and uses
K-injective towers, without assuming exactness of sheaf products. -/
theorem diagonal_reduction_completion (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W)) :
    DiagonalCompletionSpec ℓ W D := by
  classical
  have : PreservesFiniteLimits (diagonalScalarExtension ℓ W) := scalarExtension_exact ℓ W
  obtain ⟨_D, I, _hD, _hI⟩ := exists_diagonalDerivedReduction ℓ W
  obtain ⟨RF, η, RZ, ηZ, hRF, hRZ, ⟨eLim⟩⟩ := derivedLimits_exists ℓ W
  obtain ⟨eOrd⟩ := ordinaryDerivedComparison ℓ W D I
  let e : D.T ⋙ RF ⋙ (diagonalForget ℓ W).mapDerivedCategory ≅ I.T ⋙ RZ :=
    Functor.isoWhiskerLeft D.T eLim ≪≫
      (Functor.associator D.T _ RZ).symm ≪≫ Functor.isoWhiskerRight eOrd RZ
  obtain ⟨unit, hcomplete, hbij⟩ := integral_strict_completion_reflector ℓ W I RZ ηZ hRZ
  refine ⟨I, RF, η, RZ, ηZ, hRF, hRZ, ⟨e⟩, unit ≫ e.inv, ?_, ?_⟩
  · intro K P hP
    have := hcomplete K P hP
    exact (Iso.homCongr (Iso.refl P) (e.app K)).injective.subsingleton
  · intro K N hN
    convert (hbij K N hN).comp (Iso.homCongr (e.app K) (Iso.refl N)).bijective using 1
    ext f
    simp only [NatTrans.comp_app, Iso.homCongr, Equiv.coe_fn_mk,
      Iso.refl_hom, Category.comp_id, Function.comp_apply, Category.assoc]
    rfl

end AlgebraicGeometry.ProEtale
