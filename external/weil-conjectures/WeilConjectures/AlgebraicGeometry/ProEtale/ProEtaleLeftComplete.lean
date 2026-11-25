/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleMilnorSequence
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.AlgebraicGeometry.MilnorTower
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
public import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.AlgebraicGeometry.RoosCohomologySequence
public import WeilConjectures.AlgebraicGeometry.RoosCohomologyMaps
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.AlgebraicGeometry.RoosCohomologyNaturality
public import Mathlib.Algebra.Homology.SingleHomology
public import WeilConjectures.CategoryTheory.SmoothPurity.TruncationsAndHomotopyColimits
public import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleProductsDerived
import WeilConjectures.AlgebraicGeometry.ProEtaleMilnorEpimorphic
import WeilConjectures.AlgebraicGeometry.ProEtaleMilnorSequence
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.AlgebraicGeometry.MilnorTower
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.AlgebraicGeometry.RoosCohomologySequence
import WeilConjectures.AlgebraicGeometry.RoosCohomologyMaps
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.AlgebraicGeometry.RoosCohomologyNaturality
import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSurjectiveTowerDerivedLimitSupplement
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Postnikov convergence on the small pro-etale site

We use the good truncations and quotient maps of Mathlib and the strict shifted-cone
construction used by `milnor_sequence`. The comparison has the quotient maps in its
first coordinate and zero in its second coordinate; no arbitrary cone lift is chosen.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

section Construction

variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

/-- The canonical quotient from the lower truncation at -(n+1) to that at -n.
Truncating the quotient map at the lower cutoff and identifying the already-supported
result with its source constructs the unique map compatible with the quotient from K. -/
def postnikovStep (K : CochainComplex A ℤ) (n : ℕ) :
    K.truncGE (-((n + 1 : ℕ) : ℤ)) ⟶ K.truncGE (-(n : ℤ)) :=
  letI := (K.truncGE (-(n : ℤ))).isStrictlyGE_of_ge
    (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))
    (Int.neg_le_neg (Int.ofNat_le.mpr (Nat.le_succ n)))
  CochainComplex.truncGEMap (K.πTruncGE (-(n : ℤ))) (-((n + 1 : ℕ) : ℤ)) ≫
    inv ((K.truncGE (-(n : ℤ))).πTruncGE (-((n + 1 : ℕ) : ℤ)))

/-- The strict inverse sequence of good truncations, indexed by n >= 0. -/
def postnikovTower (K : CochainComplex A ℤ) : ℕᵒᵖ ⥤ CochainComplex A ℤ :=
  Functor.ofOpSequence (X := fun n : ℕ ↦ K.truncGE (-(n : ℤ))) (postnikovStep K)

omit [HasCountableProducts A] in
private lemma postnikovStep_quotient (K : CochainComplex A ℤ) (n : ℕ) :
    K.πTruncGE (-((n + 1 : ℕ) : ℤ)) ≫ postnikovStep K n =
      K.πTruncGE (-(n : ℤ)) := by
  dsimp [postnikovStep]
  rw [← Category.assoc, CochainComplex.πTruncGE_naturality, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

/-- The quotient family and zero second coordinate satisfy the shifted-cone chain-map
condition. This is the map-of-complexes assertion in the first paragraph of the source. -/
theorem postnikovComparison_condition (K : CochainComplex A ℤ) :
    CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain K
          (∏ᶜ (fun n : ℕ ↦ (postnikovTower K).obj (op n))) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (Pi.lift (fun n : ℕ ↦ K.πTruncGE (-(n : ℤ))) ≫
          towerTransitionEndomorphism
            (K := fun n : ℕ ↦ (postnikovTower K).obj (op n))
            (WeilConjectures.integralOperationsTowerStep (postnikovTower K))) = 0 := by
  have hzero : Pi.lift (fun n : ℕ ↦ K.πTruncGE (-(n : ℤ))) ≫
      towerTransitionEndomorphism
        (K := fun n : ℕ ↦ (postnikovTower K).obj (op n))
        (WeilConjectures.integralOperationsTowerStep (postnikovTower K)) = 0 := by
    have htower : WeilConjectures.integralOperationsTowerStep (postnikovTower K) =
        postnikovStep K := by
      funext n
      simp [WeilConjectures.integralOperationsTowerStep, postnikovTower]
    rw [htower]
    change Pi.lift (fun n : ℕ ↦ K.πTruncGE (-(n : ℤ))) ≫
      towerTransitionEndomorphism (postnikovStep K) = 0
    apply Pi.hom_ext
    intro n
    simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.comp_sub,
      Preadditive.sub_comp, Category.comp_id, Category.assoc,
      Pi.lift_comp_π, Pi.lift_comp_π_assoc, zero_comp]
    rw [postnikovStep_quotient, sub_self]
  simp [hzero]

/-- The canonical comparison with the sequential derived limit: its first coordinate
is the family K -> tau_(>=-n) K and its second coordinate is zero. -/
def postnikovComparison (K : CochainComplex A ℤ) :
    K ⟶ WeilConjectures.integralOperationsRoos (postnikovTower K) :=
  CochainComplex.mappingCocone.lift
    (towerTransitionEndomorphism
      (K := fun n : ℕ ↦ (postnikovTower K).obj (op n))
      (WeilConjectures.integralOperationsTowerStep (postnikovTower K)))
    (Pi.lift (fun n : ℕ ↦ K.πTruncGE (-(n : ℤ)))) 0
    (postnikovComparison_condition K)

private lemma eventually_constant_kernel {M : ℕ → A}
    (t : ∀ n, M (n + 1) ⟶ M n) {S : A} (u : ∀ n, S ⟶ M n) (N : ℕ)
    (hz : ∀ n, n < N → IsZero (M n))
    (hu : ∀ n, N ≤ n → IsIso (u n))
    (hc : ∀ n, u (n + 1) ≫ t n = u n) :
    ∃ h : Pi.lift u ≫ towerTransitionEndomorphism t = 0,
      Nonempty (IsLimit (KernelFork.ofι (Pi.lift u) h)) := by
  have hzero : Pi.lift u ≫ towerTransitionEndomorphism t = 0 := by
    apply Pi.hom_ext
    intro n
    simp [towerTransitionEndomorphism, towerProductShift, Category.assoc, hc]
  have ht (n : ℕ) (hn : N ≤ n) : IsIso (t n) := by
    have := hu n hn
    have := hu (n + 1) (by omega)
    have : IsIso (u (n + 1) ≫ t n) := by rw [hc]; infer_instance
    exact IsIso.of_isIso_comp_left (u (n + 1)) (t n)
  have := hu N (by omega)
  refine ⟨hzero, ⟨KernelFork.IsLimit.ofι _ _
    (fun g _ ↦ g ≫ Pi.π M N ≫ inv (u N)) ?_ ?_⟩⟩
  · intro W g hg
    have hg' (n : ℕ) : (g ≫ Pi.π M (n + 1)) ≫ t n = g ≫ Pi.π M n := by
      have h := congrArg (fun f ↦ f ≫ Pi.π M n) hg
      have h' : g ≫ Pi.π M n - (g ≫ Pi.π M (n + 1)) ≫ t n = 0 := by
        simpa [towerTransitionEndomorphism, towerProductShift, Category.assoc] using h
      exact (sub_eq_zero.mp h').symm
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, Pi.lift_comp_π]
    by_cases hn : N ≤ n
    · induction n, hn using Nat.le_induction with
      | base => simp
      | succ n hn ih =>
        have := ht n hn
        apply (cancel_mono (t n)).mp
        simpa only [Category.assoc, hc, hg'] using ih
    · exact (hz n (by omega)).eq_of_tgt _ _
  · intro W g hg m hm
    have h := congrArg (fun f ↦ f ≫ Pi.π M N) hm
    simpa [Category.assoc] using congrArg (fun f ↦ f ≫ inv (u N)) h

end Construction

/-- Every complex of modules over any ring sheaf on the small pro-etale site is
quasi-isomorphic to the strict sequential derived limit of its good lower truncations,
via the canonical quotient-family comparison. -/
theorem left_complete_quasiIso (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{max u (t + 1)})
    (K : CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ) :
    QuasiIso (postnikovComparison K) := by
  let A := ringedSiteModules.{max u (t + 1)} R
  let := HasDerivedCategory.standard A
  have hp (q : ℤ) : IsIso (piComparison
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q)
      (fun n : ℕ ↦ (postnikovTower K).obj (op n))) := by
    let H := HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q
    have (L : ULift.{u} ℕ → CochainComplex A ℤ) :
        IsIso (piComparison H L) := (products_derived X R _ L).2.1 q
    have (L : ULift.{u} ℕ → CochainComplex A ℤ) :
        PreservesLimit (Discrete.functor L) H := PreservesProduct.of_iso_comparison _ _
    have : PreservesLimitsOfShape (Discrete (ULift.{u} ℕ)) H :=
      preservesLimitsOfShape_of_discrete H
    have : PreservesLimitsOfShape (Discrete ℕ) H :=
      preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) H
    infer_instance
  let C := fun n : ℕ ↦ (postnikovTower K).obj (op n)
  let d := WeilConjectures.integralOperationsTowerStep (postnikovTower K)
  have hd (n : ℕ) : d n = postnikovStep K n := by
    simp [d, WeilConjectures.integralOperationsTowerStep, postnikovTower]
  let P := ∏ᶜ C
  let φ : P ⟶ P := towerTransitionEndomorphism d
  let H := fun q : ℤ ↦ HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q
  let u (q : ℤ) (n : ℕ) : (H q).obj K ⟶ (H q).obj (C n) :=
    (H q).map (K.πTruncGE (-(n : ℤ)))
  let t (q : ℤ) (n : ℕ) : (H q).obj (C (n + 1)) ⟶ (H q).obj (C n) :=
    (H q).map (d n)
  have hc (q : ℤ) (n : ℕ) : u q (n + 1) ≫ t q n = u q n := by
    change (H q).map (K.πTruncGE (-((n + 1 : ℕ) : ℤ))) ≫ (H q).map (d n) = _
    rw [← Functor.map_comp, hd, postnikovStep_quotient]
  have hu (q : ℤ) (n : ℕ) (hn : -q ≤ (n : ℤ)) : IsIso (u q n) := by
    have := CochainComplex.quasiIsoAt_πTruncGE K (-(n : ℤ)) q (by omega)
    exact (quasiIsoAt_iff_isIso_homologyMap _ _).mp this
  have hz (q : ℤ) (n : ℕ) (hn : (n : ℤ) < -q) : IsZero ((H q).obj (C n)) := by
    exact (K.truncGE (-(n : ℤ))).isZero_of_isGE (-(n : ℤ)) q (by omega)
  have ht (q : ℤ) (n : ℕ) : Epi (t q n) := by
    by_cases hn : -q ≤ (n : ℤ)
    · have := hu q n hn
      have := hu q (n + 1) (by omega)
      have : IsIso (u q (n + 1) ≫ t q n) := by rw [hc]; infer_instance
      have := IsIso.of_isIso_comp_left (u q (n + 1)) (t q n)
      infer_instance
    · exact (hz q n (by omega)).epi _
  have hepi (q : ℤ) : Epi (towerTransitionEndomorphism (K := fun n ↦ (H q).obj (C n)) (t q)) := by
    exact (AlgebraicGeometry.ProEtale.milnor_epimorphic.{u, t} X R
      (milnorCohomologyTower (postnikovTower K) q) (ht q)).1
  have hφ (q : ℤ) : (H q).map φ ≫ piComparison (H q) C =
      piComparison (H q) C ≫ towerTransitionEndomorphism (K := fun n ↦ (H q).obj (C n)) (t q) := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, piComparison_comp_π]
    simp only [towerTransitionEndomorphism, towerProductShift, Functor.map_sub,
      Preadditive.sub_comp, ← Functor.map_comp, limit.lift_π, Fan.mk_pt, Fan.mk_π_app,
      Category.id_comp, Preadditive.comp_sub, piComparison_comp_π,
      piComparison_comp_π_assoc, sub_left_inj, φ, t]
    exact congrArg (H q).map (Category.id_comp _)
  have hep (q : ℤ) : Epi ((H q).map φ) := by
    have := hp q
    have := hepi q
    have : Epi ((H q).map φ ≫ piComparison (H q) C) := by rw [hφ]; infer_instance
    have : Epi (((H q).map φ ≫ piComparison (H q) C) ≫
        inv (piComparison (H q) C)) := inferInstance
    simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using this
  let T := CochainComplex.mappingCocone.triangle φ
  have hT := DerivedCategory.mappingCocone_triangle_distinguished φ
  have hm (q : ℤ) : Mono ((H q).map (CochainComplex.mappingCocone.fst φ)) := by
    have := hep (q - 1)
    have hδ : CochainComplex.homologyδOfTriangle T (q - 1) q (by omega) = 0 := by
      exact (CochainComplex.homologyMap_exact₃_of_distTriang T hT
        (q - 1) q (by omega)).epi_f_iff.mp (hep (q - 1))
    exact (CochainComplex.homologyMap_exact₁_of_distTriang T hT
      (q - 1) q (by omega)).mono_g_iff.mpr hδ
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have := hp q
  have := hm q
  obtain ⟨hw, ⟨hk⟩⟩ := eventually_constant_kernel (t q) (u q) (-q).toNat
    (fun n hn ↦ hz q n (by omega)) (fun n hn ↦ hu q n (by omega)) (hc q)
  let e := (asIso (piComparison (H q) C)).symm
  have he (W : A) (g : W ⟶ ∏ᶜ (fun n ↦ (H q).obj (C n))) :
      g ≫ towerTransitionEndomorphism (t q) = 0 ↔
        g ≫ e.hom ≫ (H q).map φ = 0 := by
    have heq : e.hom ≫ (H q).map φ =
        towerTransitionEndomorphism (t q) ≫ e.hom := by
      apply (cancel_mono (piComparison (H q) C)).mp
      simp only [Category.assoc, hφ, e, Iso.symm_hom, asIso_inv,
        IsIso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [heq]
    exact ⟨fun h ↦ by rw [← Category.assoc, h, zero_comp], fun h ↦ by
      apply (cancel_mono e.hom).mp
      simpa only [Category.assoc, zero_comp] using h⟩
  have hk' := KernelFork.isLimitOfIsLimitOfIff hk ((H q).map φ) e (fun {_} g ↦ he _ g)
  let α : K ⟶ P := Pi.lift (fun n : ℕ ↦ K.πTruncGE (-(n : ℤ)))
  have hα : Pi.lift (u q) ≫ e.hom = (H q).map α := by
    apply (cancel_mono (piComparison (H q) C)).mp
    simp [e, Category.assoc, α, u, map_lift_piComparison]
  simp only [KernelFork.ι_ofι] at hk'
  have hk'' := IsLimit.ofIsoLimit hk' (ofιCongr hα)
  have : Mono (HomologicalComplex.homologyMap T.mor₁ q) := hm q
  have hkF := (CochainComplex.homologyMap_exact₂_of_distTriang T hT q).fIsKernel
  have hcomp : HomologicalComplex.homologyMap (postnikovComparison K) q =
      (hk''.conePointUniqueUpToIso hkF).hom := by
    change (H q).map (postnikovComparison K) = _
    apply (cancel_mono ((H q).map (CochainComplex.mappingCocone.fst φ))).mp
    have hfac := IsLimit.conePointUniqueUpToIso_hom_comp hk'' hkF WalkingParallelPair.zero
    change (hk''.conePointUniqueUpToIso hkF).hom ≫
      (H q).map (CochainComplex.mappingCocone.fst φ) = (H q).map α at hfac
    rw [hfac]
    change (H q).map (postnikovComparison K) ≫
      (H q).map (CochainComplex.mappingCocone.fst φ) = (H q).map α
    rw [← Functor.map_comp]
    congr 1
    exact CochainComplex.mappingCocone.lift_fst _ _ _ _
  rw [hcomp]
  infer_instance

end AlgebraicGeometry.Scheme.ProEt
