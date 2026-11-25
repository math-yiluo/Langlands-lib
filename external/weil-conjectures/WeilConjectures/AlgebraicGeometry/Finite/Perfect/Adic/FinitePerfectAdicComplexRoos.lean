/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicTowerExtraction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSurjectiveTowerDerivedLimitSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # Termwise epimorphic completed-module complex towers

Source: Stacks Project, Cohomology on Sites, Tags 0940 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Exact products for the completed coefficient modules.
Source: Stacks Tags 07KC and 0941.
(blueprint: lem-weil-pbc-finite-perfect-adic-complex-roos). -/
theorem finitePerfectAdicModules_exactProducts
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) :
    CountableAB4Star (CompletedAdicModules X d) := by
  have : HasFiniteBiproducts (CompletedAdicModules X d) := Abelian.hasFiniteBiproducts
  have : (lim (J := Discrete ℕ) (C := CompletedAdicModules X d)).PreservesEpimorphisms :=
    { preserves := by
        intro F G f hf
        have h := (ProEt.countableProducts_exact.{t, 0, 0} X
          (completedAdicCommRing X d)).2.2 ℕ
          (fun n ↦ F.obj ⟨n⟩) (fun n ↦ G.obj ⟨n⟩)
          (fun n ↦ f.app ⟨n⟩) (fun n ↦ inferInstance)
        have he : lim.map f = (Pi.isoLimit _).inv ≫
            Limits.Pi.map (fun n ↦ f.app ⟨n⟩) ≫ (Pi.isoLimit _).hom := by
          apply limit.hom_ext
          intro ⟨n⟩
          simp
        rw [he]
        infer_instance }
  have := hasExactLimitsOfShape_of_preservesEpi (CompletedAdicModules X d) (Discrete ℕ)
  exact CountableAB4Star.of_hasExactLimitsOfShape_nat _

/-- Termwise epimorphic complex towers have their ordinary limit as their Roos limit.

Source: Stacks Project, Cohomology on Sites, Tags 0940 and 0941.
(blueprint: lem-weil-pbc-finite-perfect-adic-complex-roos).

Proof: form the termwise product and its one-minus-shift operator. In every degree,
the pro-etale epimorphic-tower theorem makes this operator an epimorphism. The
ordinary limit cone is its kernel, by the universal property of compatible families.
Thus these two maps are a short exact sequence of complexes. Exact countable
products identify the localized product cone with a derived product. Transport the
short-exact-sequence triangle through that product isomorphism, checking the first
two arrows on every projection. No boundedness of the complexes is needed. -/
theorem finitePerfectAdicComplex_roos
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (T : ℕᵒᵖ ⥤ CochainComplex (CompletedAdicModules X d) ℤ)
    (ht : ∀ (n : ℕ) (i : ℤ), Epi ((T.map (homOfLE n.le_succ).op).f i))
    (c : Cone T) (hc : IsLimit c) :
    HasProduct (fun n : ℕ ↦ DerivedCategory.Q.obj (T.obj (op n))) ∧
    ∀ [HasProduct (fun n : ℕ ↦ DerivedCategory.Q.obj (T.obj (op n)))],
      IsDerivedLimit (K := fun n : ℕ ↦ DerivedCategory.Q.obj (T.obj (op n)))
        (fun n : ℕ ↦ DerivedCategory.Q.map (T.map (homOfLE n.le_succ).op))
        (DerivedCategory.Q.obj c.pt) := by
  classical
  let K := fun n : ℕ ↦ T.obj (op n)
  let B : Fan K := Fan.mk (∏ᶜ K) (Pi.π K)
  let hB : IsLimit B := productIsProduct K
  let shift : B.pt ⟶ B.pt := towerProductShift
    (fun n ↦ T.map (homOfLE n.le_succ).op)
  have hshift (n : ℕ) : shift ≫ B.proj n =
      B.proj (n + 1) ≫ T.map (homOfLE n.le_succ).op := Pi.lift_comp_π _ _
  let S := ShortComplex.mk _ _
    (Fan.IsLimit.lift_π_comp_one_sub_eq_zero hB shift hshift c)
  have hk := Fan.IsLimit.isLimitKernelForkOneSub hB shift hshift hc
  have hepi (i : ℤ) : Epi ((𝟙 B.pt - shift).f i) := by
    let F := fun n : ℕ ↦ (T.obj (op n)).X i
    let f := fun n : ℕ ↦ (T.map (homOfLE n.le_succ).op).f i
    obtain ⟨_, _, hEpi, _⟩ :=
      AlgebraicGeometry.ProEtale.proEtale_surjectiveTower_derivedLimit.{t, 0} X
        (completedAdicCommRing X d) F f (fun n ↦ ht n i)
    let hBi := isLimitFanMkObjOfIsLimit (HomologicalComplex.eval _ _ i) K _ hB
    let e : B.pt.X i ≅ ∏ᶜ F := hBi.conePointUniqueUpToIso (productIsProduct F)
    have he (n : ℕ) : e.hom ≫ Pi.π F n = (B.proj n).f i :=
      hBi.conePointUniqueUpToIso_hom_comp (productIsProduct F) ⟨n⟩
    have hconj : (𝟙 B.pt - shift).f i =
        e.hom ≫ towerTransitionEndomorphism f ≫ e.inv := by
      apply (cancel_mono e.hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      apply Pi.hom_ext
      intro n
      simp only [Category.assoc, he, towerTransitionEndomorphism, towerProductShift,
        Preadditive.comp_sub, Preadditive.sub_comp, Category.id_comp, Pi.lift_comp_π,
        HomologicalComplex.sub_f_apply, HomologicalComplex.id_f]
      have hn := congrArg (fun q ↦ q.f i) (hshift n)
      simpa only [HomologicalComplex.comp_f, Category.assoc, reassoc_of% he, f] using
        congrArg (fun q ↦ (B.proj n).f i - q) hn
    rw [hconj]
    infer_instance
  have hS : S.ShortExact := by
    have : Mono S.f := mono_of_isLimit_fork hk
    have : Epi S.g := HomologicalComplex.epi_of_epi_f _ hepi
    exact { exact := ShortComplex.exact_of_f_is_kernel _ hk }
  have := finitePerfectAdicModules_exactProducts X d
  obtain ⟨hD, hQ, _⟩ := derivedCategory_countableProducts_core.{0}
    (CompletedAdicModules X d)
  have hQB : IsLimit (DerivedCategory.Q.mapCone B) := (hQ ℕ K).some
  let hQFan := (Fan.isLimitMapConeEquiv DerivedCategory.Q K B) hQB
  refine ⟨inferInstance, ?_⟩
  intro hprod
  let K₀ := fun n : ℕ ↦ DerivedCategory.Q.obj (K n)
  let f₀ := fun n : ℕ ↦ DerivedCategory.Q.map (T.map (homOfLE n.le_succ).op)
  let p : DerivedCategory.Q.obj c.pt ⟶ ∏ᶜ K₀ :=
    Pi.lift (fun n : ℕ ↦ DerivedCategory.Q.map (c.π.app (op n)))
  let E : DerivedCategory.Q.obj B.pt ≅ ∏ᶜ K₀ :=
    hQFan.conePointUniqueUpToIso (productIsProduct K₀)
  have hE (n : ℕ) : E.hom ≫ Pi.π K₀ n = DerivedCategory.Q.map (B.proj n) :=
    hQFan.conePointUniqueUpToIso_hom_comp (productIsProduct K₀) ⟨n⟩
  have hπ (n : ℕ) : p ≫ Pi.π K₀ n =
      DerivedCategory.Q.map (c.π.app (op n)) := Pi.lift_comp_π _ _
  have hi : DerivedCategory.Q.map S.f ≫ E.hom = p := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hE, ← Functor.map_comp, hπ]
    exact congrArg DerivedCategory.Q.map (hB.fac _ ⟨n⟩)
  have hu (n : ℕ) : S.g ≫ B.proj n = B.proj n -
      B.proj (n + 1) ≫ T.map (homOfLE n.le_succ).op := by
    change (𝟙 B.pt - shift) ≫ B.proj n = _
    rw [Preadditive.sub_comp, Category.id_comp, hshift]
  have htrans : DerivedCategory.Q.map S.g ≫ E.hom =
      E.hom ≫ towerTransitionEndomorphism f₀ := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hE, ← Functor.map_comp, hu, Functor.map_sub]
    simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
      Category.id_comp, Preadditive.comp_sub, Pi.lift_comp_π, hE, f₀]
    rw [Functor.map_comp, ← Category.assoc, hE]
  let δ := DerivedCategory.triangleOfSESδ hS
  refine ⟨p, E.inv ≫ δ, ?_⟩
  exact (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk
      (Pretriangulated.Triangle.mk (DerivedCategory.Q.map S.f) (DerivedCategory.Q.map S.g) δ)
      (Pretriangulated.Triangle.mk p (towerTransitionEndomorphism f₀) (E.inv ≫ δ))
      (Iso.refl _) E E (by simpa using hi) htrans (by simp))).mp
    (DerivedCategory.triangleOfSES_distinguished hS)

end AlgebraicGeometry.Scheme
