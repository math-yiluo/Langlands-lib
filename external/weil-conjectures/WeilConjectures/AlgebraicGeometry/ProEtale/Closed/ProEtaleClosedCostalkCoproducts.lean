/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedClosedKernelAdjoint
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.CategoryTheory.ProperBaseChange.SupportedRightAdjointCoproducts
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIntegralDirectImageCoproducts
import all WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedTensorProjection
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Closed costalks and uniformly bounded-below coproducts

## References

* Stacks Project, Tag 09BM
* Bhatt--Scholze, Lemma 6.3.14(4)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

-- The unbounded derived comparisons require elaborating several functor structures.
set_option synthInstance.maxSize 4096 in
/-- Every right adjoint to exact closed direct image preserves uniformly
bounded-below coproducts for arbitrary ring-sheaf coefficients. -/
theorem proEtaleClosedCostalk_preservesCoproduct
    {T Z : Scheme.{u}} [TopologicalSpace.NoetherianSpace T]
    (i : Z ⟶ T) [IsClosedImmersion i]
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    [(proEtaleRingedDirectImage i R).Additive]
    [PreservesFiniteLimits (proEtaleRingedDirectImage i R)]
    [PreservesFiniteColimits (proEtaleRingedDirectImage i R)]
    (G : DerivedCategory (proEtaleRingModules T R) ⥤
      DerivedCategory (proEtaleRingModules Z
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)))
    (ag : (proEtaleRingedDirectImage i R).mapDerivedCategory ⊣ G)
    (I : Type (u + 1)) (M : I → DerivedCategory (proEtaleRingModules T R))
    (b : ℤ) (hM : ∀ s, (M s).IsGE b) :
    PreservesColimit (Discrete.functor M) G := by
  classical
  let W : T.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let V := ProEt.mk W.ι
  have : IsOpenImmersion V.hom := inferInstanceAs (IsOpenImmersion W.ι)
  let : TopologicalSpace.NoetherianSpace V.left :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (W : Set T))
  have : QuasiCompact V.hom :=
    ⟨fun B _ _ ↦ @TopologicalSpace.NoetherianSpace.isCompact V.left _
      (inferInstance : TopologicalSpace.NoetherianSpace V.left) (V.hom ⁻¹' B)⟩
  have hv : Set.range V.hom = (Set.range i)ᶜ := W.range_ι
  -- Split the dependent existential one witness at a time to avoid a large elimination term.
  obtain ⟨ai, h⟩ := proEtale_ringed_closed_kernel_adjoint i V hv R
  obtain ⟨aj, h⟩ := h
  obtain ⟨hai, h⟩ := h
  obtain ⟨haj, h⟩ := h
  obtain ⟨hqi, h⟩ := h
  obtain ⟨hqj, h⟩ := h
  obtain ⟨hli, h⟩ := h
  obtain ⟨hci, h⟩ := h
  obtain ⟨hlj, h⟩ := h
  obtain ⟨hcj, h⟩ := h
  obtain ⟨hlqi, h⟩ := h
  obtain ⟨hcqi, h⟩ := h
  obtain ⟨hH, h⟩ := h
  obtain ⟨a0, h⟩ := h
  obtain ⟨eH, h⟩ := h
  have h := h.2.2.2.2
  obtain ⟨q, h⟩ := h
  obtain ⟨eq, h⟩ := h
  obtain ⟨haext, h⟩ := h
  obtain ⟨hlext, h⟩ := h
  obtain ⟨hcext, h⟩ := h
  obtain ⟨ab, h⟩ := h
  obtain ⟨d0, h⟩ := h
  obtain ⟨di, h⟩ := h
  obtain ⟨dj, h⟩ := h
  have hiD := h.2.1
  have hjD := h.2.2.1
  have hzero := h.2.2.2.1
  let := hai
  let := haj
  let := hqi
  let := hqj
  let := hli
  let := hci
  let := hlj
  let := hcj
  let := hlqi
  let := hcqi
  let pi := proEtaleModuleInverseImage i R
  let qi := proEtaleRingedDirectImage i R
  let pj := proEtaleModuleInverseImage V.hom R
  let qj := proEtaleRingedDirectImage V.hom R
  have : IsIso di.counit := (NatTrans.isIso_iff_isIso_app _).mpr hiD
  have : IsIso dj.counit := (NatTrans.isIso_iff_isIso_app _).mpr hjD
  obtain ⟨_, _, _, _, hd⟩ := openClosedModuleData i V.hom hv R
  let RZ := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R
  let RU := (proEtaleSheafInverseImage V.hom CommRingCat.{u + 1}).obj R
  let pia := proEtaleRingModulePullback i R RZ (Iso.refl _)
  let pja := proEtaleRingModulePullback V.hom R RU (Iso.refl _)
  let ei := Functor.mapDerivedCategoryNatIso (inverseIso i R)
  let ej := Functor.mapDerivedCategoryNatIso (inverseIso V.hom R)
  have hdD := Functor.jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory pia pja hd
  have hdet {K L : DerivedCategory (proEtaleRingModules T R)} (f : K ⟶ L)
      (hi : IsIso (pi.mapDerivedCategory.map f))
      (hj : IsIso (pj.mapDerivedCategory.map f)) : IsIso f := by
    exact hdD.isIso_of_pairFunctor f ((NatIso.isIso_map_iff ei f).mpr hi)
      ((NatIso.isIso_map_iff ej f).mpr hj)
  let N (s : I) := pj.mapDerivedCategory.obj (M s)
  have hN (s : I) : (N s).IsGE b := by
    have := hM s
    exact pj.isGE_mapDerivedCategory_obj (M s) b
  have : PreservesColimit (Discrete.functor N) qj.rightDerivedFunctor := by
    have hp := proEtaleIntegralDirectImage_preservesCoproduct V.hom R RU
      (Iso.refl _) I N b hN
    change PreservesColimit (Discrete.functor N)
      (proEtaleRingModuleDirectImage V.hom R RU (Iso.refl _)).rightDerivedFunctor at hp
    dsimp only [RU] at hp
    have := hp
    let α := Functor.rightDerivedFunctorNatIso (eqToIso (push_eq V.hom R))
    exact preservesColimit_of_natIso (Discrete.functor N) α
  let eN : Discrete.functor N ≅ Discrete.functor M ⋙ pj.mapDerivedCategory :=
    (Discrete.compNatIsoDiscrete M pj.mapDerivedCategory).symm
  have : PreservesColimit (Discrete.functor M ⋙ pj.mapDerivedCategory)
      qj.rightDerivedFunctor :=
    preservesColimit_of_iso_diagram qj.rightDerivedFunctor eN
  have : PreservesColimitsOfSize.{u + 1, u + 1} pj.mapDerivedCategory :=
    dj.leftAdjoint_preservesColimits
  have : HasCoproducts.{u + 1} (DerivedCategory (proEtaleRingModules T R)) :=
    derived_hasCoproducts
  exact supportedRightAdjoint_preservesCoproduct qi.mapDerivedCategory pi.mapDerivedCategory
    pj.mapDerivedCategory qj.rightDerivedFunctor G di dj ag hzero hdet I M

end AlgebraicGeometry.Scheme
