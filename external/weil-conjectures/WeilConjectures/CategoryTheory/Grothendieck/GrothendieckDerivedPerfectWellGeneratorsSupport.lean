/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckDerivedCompactLocalizationModel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.CompactlyGenerated
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.CategoryTheory.GrothendieckDerivedGabrielPopescuPresentation
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Equivalence
public import WeilConjectures.CategoryTheory.GabrielPopescuAbelianCore
public import WeilConjectures.CategoryTheory.GabrielPopescuLargeHomRightAdjoint
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import WeilConjectures.CategoryTheory.DerivedLargeCoproductsTransfer
public import WeilConjectures.CategoryTheory.DerivedHomologyInjective
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.CategoryTheory.DerivedHomologyInjectiveSurjective
public import Mathlib.Algebra.Homology.SingleHomology
public import WeilConjectures.CategoryTheory.DerivedHomologyInjectiveInjective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.LargeHomSolutionSet
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.CategoryTheory.CompactDerivedSourceCore
public import WeilConjectures.CategoryTheory.DerivedModuleCompactGeneration
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.DerivedModuleRankOneProperties
public import Mathlib.Algebra.Module.ULift
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
public import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompact
public import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactInjective
public import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactSurjective
public import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Products
public import WeilConjectures.CategoryTheory.DerivedModuleRankOneGenerator
public import WeilConjectures.CategoryTheory.DerivedModuleRankOneNonzeroMap
public import WeilConjectures.CategoryTheory.DerivedModuleNonzeroClassMap
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.TriangulatedEquivalenceTransfer
public import WeilConjectures.CategoryTheory.CompactGenerationEquivalence
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.GrothendieckDerivedExactLocalization
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.CategoryTheory.SixFunctors.AlphaCompactObject
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.ObjectProperty.Shift

import all WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import WeilConjectures.CategoryTheory.GrothendieckAbelian.GeneratingMonoQuasiIsos
import WeilConjectures.CategoryTheory.GrothendieckAbelian.AcyclicSwallowing
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Connected
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
import Mathlib.CategoryTheory.Preadditive.LiftToFinset
import Mathlib.CategoryTheory.Presentable.Type
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-!
# A small factorization class in a Grothendieck derived category

Fix a separator and a sufficiently large regular cardinal. Complexes generated in each degree
by fewer than that many copies of the separator form an essentially small, shift-stable class.
The cover and acyclic swallowing lemmas give bounded representatives for derived roofs. This
transfers component-image factorization and a uniform coproduct-support bound from complexes
to the derived category.
-/

set_option linter.style.haveILetI false

@[expose] public section

universe v u u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

attribute [local instance] derived_hasCoproducts

/-- Every bounded complex is a quotient of the fixed disk copower, hence is represented
by the cokernel of one of its subobjects. -/
private theorem bounded_complexes_essentiallySmall
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    (G : A) (κ : Cardinal.{v}) :
    ObjectProperty.EssentiallySmall.{v}
      (CochainComplex.degreewiseCardinalGenerated G κ) := by
  let D := CochainComplex.diskCopower G κ
  let F : Subobject D → CochainComplex A ℤ := fun K ↦ cokernel K.arrow
  let P : ObjectProperty (CochainComplex A ℤ) := ObjectProperty.ofObj F
  have : ObjectProperty.Small.{v} P := inferInstance
  refine ⟨P, inferInstance, ?_⟩
  intro X hX
  obtain ⟨p, hp⟩ := CochainComplex.exists_epi_diskCopower hX
  letI := hp
  let K := kernelSubobject p
  have hk : K.arrow ≫ p = 0 := kernelSubobject_arrow_comp p
  have hlim : IsLimit (KernelFork.ofι K.arrow hk) :=
    IsLimit.ofIsoLimit (kernelIsKernel p) (Fork.ext (kernelSubobjectIso p).symm (by simp [K]))
  let e : cokernel K.arrow ≅ X :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
      (Abelian.epiIsCokernelOfKernel _ hlim)
  exact ⟨F K, ⟨K⟩, ⟨e.symm⟩⟩

/-- The size bound is unchanged by reindexing the degrees. -/
private theorem bounded_complexes_shift
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    (G : A) (κ : Cardinal.{v}) (X : CochainComplex A ℤ)
    (hX : CochainComplex.degreewiseCardinalGenerated G κ X) (n : ℤ) :
    CochainComplex.degreewiseCardinalGenerated G κ (X⟦n⟧) := by
  intro i
  exact (isCardinalGenerated G κ).prop_of_iso
    (X.shiftFunctorObjXIso n i (i + n) rfl).symm (hX (i + n))

/-- Add the contractible mapping cocone of the identity to make a roof denominator epic.
The inclusion of the old source has the displayed retraction. -/
private theorem epi_quasiIso_replacement
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    {W X : CochainComplex A ℤ} (s : W ⟶ X) [QuasiIso s] :
    ∃ (V : CochainComplex A ℤ) (t : W ⟶ V) (p : V ⟶ X) (r : V ⟶ W),
      QuasiIso t ∧ QuasiIso p ∧ Epi p ∧ t ≫ p = s ∧ t ≫ r = 𝟙 W := by
  let D := CochainComplex.mappingCocone (𝟙 X)
  have hD : D.Acyclic := by
    have h : Homotopy (𝟙 D) 0 := by
      simpa [D, CochainComplex.mappingCocone] using
        (CochainComplex.mappingCone.homotopyIdZeroOfId (K := X)).shift (-1)
    intro n
    rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero,
      ← HomologicalComplex.homologyMap_id, h.homologyMap_eq,
      HomologicalComplex.homologyMap_zero]
  have hfst : Epi (CochainComplex.mappingCocone.fst (𝟙 X)) := by
    apply HomologicalComplex.epi_of_epi_f
    intro n
    exact epi_of_epi_fac (CochainComplex.mappingCocone.inl_v_fst_f (𝟙 X) n)
  let p : W ⊞ D ⟶ X := biprod.desc s (CochainComplex.mappingCocone.fst (𝟙 X))
  have hp : Epi p := epi_of_epi_fac (biprod.inr_desc s
    (CochainComplex.mappingCocone.fst (𝟙 X)))
  have ht : QuasiIso (biprod.inl : W ⟶ W ⊞ D) :=
    (Abelian.quasiIso_f_iff_of_shortExact
      (S := ShortComplex.mk biprod.inl biprod.snd (by simp))
      (ShortComplex.Splitting.ofHasBinaryBiproduct W D).shortExact).2 hD
  have hpqi : QuasiIso p := by
    have : QuasiIso ((biprod.inl : W ⟶ W ⊞ D) ≫ p) := by simpa [p]
    exact quasiIso_of_comp_left biprod.inl p
  exact ⟨W ⊞ D, biprod.inl, p, biprod.fst, ht, hpqi, hp,
    by simp [p], by simp⟩

/-- For a short exact sequence of complexes, the quotient map is a quasi-isomorphism
exactly when its kernel is acyclic. -/
private theorem quasiIso_g_iff_acyclic
    {A : Type u} [Category.{v} A] [Abelian A]
    {S : ShortComplex (CochainComplex A ℤ)} (hS : S.ShortExact) :
    QuasiIso S.g ↔ S.X₁.Acyclic := by
  constructor
  · intro hg n
    letI := hg
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    refine (hS.homology_exact₁ (n - 1) n (by simp)).isZero_X₂ ?_ ?_
    · rw [← cancel_epi (HomologicalComplex.homologyMap S.g (n - 1)), comp_zero]
      exact hS.comp_δ (n - 1) n (by simp)
    · rw [← cancel_mono (HomologicalComplex.homologyMap S.g n), zero_comp,
        ← HomologicalComplex.homologyMap_comp, S.zero,
        HomologicalComplex.homologyMap_zero]
  · intro h
    constructor
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have : Mono (HomologicalComplex.homologyMap S.g n) :=
      (hS.homology_exact₂ n).mono_g (by
        apply IsZero.eq_of_src
        simpa [← HomologicalComplex.exactAt_iff_isZero_homology] using h n)
    have : Epi (HomologicalComplex.homologyMap S.g n) :=
      (hS.homology_exact₃ n (n + 1) (by simp)).epi_f (by
        apply IsZero.eq_of_tgt
        simpa [← HomologicalComplex.exactAt_iff_isZero_homology] using h (n + 1))
    exact Balanced.isIso_of_mono_of_epi _

/-- Lift generators degreewise along an epimorphism and close them under differentials. -/
private theorem bounded_subcomplex_epi
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    (G : A) (κ : Cardinal.{v}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (hG : IsSeparator G)
    (hsub : ∀ n : ℕ, HasCardinalLT (Subobject (∐ fun _ : Fin n ↦ G)) κ)
    {W X : CochainComplex A ℤ} (p : W ⟶ X) [Epi p]
    (hX : CochainComplex.degreewiseCardinalGenerated G κ X) :
    ∃ T : Subobject W, CochainComplex.degreewiseCardinalGenerated G κ
      (T : CochainComplex A ℤ) ∧ Epi (T.arrow ≫ p) := by
  have htop (n : ℤ) : isCardinalGenerated G κ ((⊤ : Subobject (X.X n)) : A) :=
    (isCardinalGenerated G κ).prop_of_iso (asIso (⊤ : Subobject (X.X n)).arrow).symm
      (hX n)
  choose V hV hVp using fun n : ℤ ↦
    exists_isCardinalGenerated_subobject_of_epi G κ hκ hG hsub
      (p.f n) ⊤ (htop n)
  let T := HomologicalComplex.subcomplexClosure W V
  refine ⟨T, CochainComplex.degreewiseCardinalGenerated_subcomplexClosure G κ V hV, ?_⟩
  have he (n : ℤ) : Epi ((V n).arrow ≫ p.f n) := by
    obtain ⟨e, he, heq⟩ := Subobject.exists_fac (p.f n) (V n)
    haveI := he
    haveI : IsIso ((Subobject.«exists» (p.f n)).obj (V n)).arrow := by
      rw [hVp n]
      infer_instance
    rw [← heq]
    infer_instance
  apply HomologicalComplex.epi_of_epi_f
  intro n
  have hle := HomologicalComplex.le_subcomplexClosure W V n
  have hfac : Subobject.ofLE (V n) (HomologicalComplex.subobjectEval W n T) hle ≫
      (HomologicalComplex.subobjectEvalUnderlyingIso (n := n) T).hom ≫
        (T.arrow ≫ p).f n = (V n).arrow ≫ p.f n := by
    simp only [HomologicalComplex.comp_f,
      HomologicalComplex.subobjectEvalUnderlyingIso_hom_comp_arrow_assoc,
      Subobject.ofLE_arrow_assoc]
  letI := he n
  exact epi_of_epi_fac ((Category.assoc _ _ _).trans hfac)

/-- The union of two generating families generates a binary biproduct. -/
private theorem generated_biprod
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    (G : A) (κ : Cardinal.{v}) [Fact κ.IsRegular] {X Y : A}
    (hX : isCardinalGenerated G κ X) (hY : isCardinalGenerated G κ Y) :
    isCardinalGenerated G κ (X ⊞ Y) := by
  obtain ⟨I, hI, p, hp⟩ := hX
  obtain ⟨J, hJ, q, hq⟩ := hY
  letI := hp
  letI := hq
  let a : ∀ k : I ⊕ J, G ⟶ X ⊞ Y :=
    Sum.elim (fun i ↦ Sigma.ι (fun _ : I ↦ G) i ≫ p ≫ biprod.inl)
      (fun j ↦ Sigma.ι (fun _ : J ↦ G) j ≫ q ≫ biprod.inr)
  refine ⟨I ⊕ J, (hasCardinalLT_sum_iff I J κ
    (Cardinal.IsRegular.aleph0_le Fact.out)).2 ⟨hI, hJ⟩, Sigma.desc a, ?_⟩
  constructor
  intro Z f g h
  apply biprod.hom_ext'
  · apply (cancel_epi p).1
    apply Sigma.hom_ext
    intro i
    simpa [a, Category.assoc] using Sigma.ι (fun _ : I ⊕ J ↦ G) (Sum.inl i) ≫= h
  · apply (cancel_epi q).1
    apply Sigma.hom_ext
    intro j
    simpa [a, Category.assoc] using Sigma.ι (fun _ : I ⊕ J ↦ G) (Sum.inr j) ≫= h

/-- Choose a bounded subcomplex mapping onto the denominator target. Its kernel embeds
in the acyclic kernel of the original denominator. Swallow its image in a bounded acyclic
subcomplex, then push out. The resulting bounded extension is quasi-isomorphic to the target. -/
private theorem bounded_epi_quasiIso_roof
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    (G : A) (κ : Cardinal.{v}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (hG : IsSeparator G)
    (hsub : ∀ n : ℕ, HasCardinalLT (Subobject (∐ fun _ : Fin n ↦ G)) κ)
    {W X : CochainComplex A ℤ} (p : W ⟶ X) [Epi p] [QuasiIso p]
    (hX : CochainComplex.degreewiseCardinalGenerated G κ X) :
    ∃ (T : CochainComplex A ℤ) (a : T ⟶ W),
      CochainComplex.degreewiseCardinalGenerated G κ T ∧ QuasiIso (a ≫ p) := by
  obtain ⟨T, hT, ht⟩ := bounded_subcomplex_epi G κ hκ hG hsub p hX
  let t := T.arrow ≫ p
  letI : Epi t := ht
  let K := kernel p
  have hK : K.Acyclic := (quasiIso_g_iff_acyclic
    (S := ShortComplex.mk (kernel.ι p) p (kernel.condition p))
    { exact := ShortComplex.exact_kernel p }).mp inferInstance
  let i : kernel t ⟶ K := kernel.lift p (kernel.ι t ≫ T.arrow) (by simp [t])
  have hi : i ≫ kernel.ι p = kernel.ι t ≫ T.arrow := by simp [i]
  haveI : Mono i := mono_of_mono_fac hi
  have hker : CochainComplex.degreewiseCardinalGenerated G κ (kernel t) :=
    CochainComplex.degreewiseCardinalGenerated_of_mono G κ hκ hG hsub (kernel.ι t) hT
  have hS : CochainComplex.degreewiseCardinalGenerated G κ
      ((imageSubobject i : Subobject K) : CochainComplex A ℤ) :=
    CochainComplex.degreewiseCardinalGenerated_of_epi G κ (factorThruImageSubobject i) hker
  obtain ⟨V, hSV, hV, hVac⟩ :=
    CochainComplex.exists_acyclic_degreewiseCardinalGenerated_le G κ hκ hG hsub hK
      (imageSubobject i) hS
  let k : kernel t ⟶ (V : CochainComplex A ℤ) :=
    V.factorThru i ((Subobject.imageSubobject_le_iff i V).1 hSV)
  have hk : k ≫ V.arrow = i := Subobject.factorThru_arrow _ _ _
  let P := pushout (kernel.ι t) k
  let a : P ⟶ W := pushout.desc T.arrow (V.arrow ≫ kernel.ι p) (by
    rw [← Category.assoc, hk, hi])
  let q : P ⟶ X := pushout.desc t 0 (by simp)
  have haq : a ≫ p = q := by
    apply pushout.hom_ext <;> simp [a, q, t, Category.assoc]
  have hzero : pushout.inr (kernel.ι t) k ≫ q = 0 := by simp [q]
  haveI : Epi q := epi_of_epi_fac (pushout.inl_desc t 0 (by simp))
  have hc : IsColimit (CokernelCofork.ofπ q hzero) := by
    apply CokernelCofork.IsColimit.ofπ' _ _
    intro Z b hb
    have hkb : kernel.ι t ≫ (pushout.inl (kernel.ι t) k ≫ b) = 0 := by
      rw [← Category.assoc, pushout.condition, Category.assoc, hb, comp_zero]
    let d : X ⟶ Z := (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel t)).desc
      (CokernelCofork.ofπ _ hkb)
    have hd : t ≫ d = pushout.inl (kernel.ι t) k ≫ b :=
      Cofork.IsColimit.π_desc (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel t))
    refine ⟨d, ?_⟩
    apply pushout.hom_ext
    · simpa [q] using hd
    · simp [q, hb]
  haveI : Epi q := epi_of_isColimit_cofork hc
  have hse : (ShortComplex.mk (pushout.inr (kernel.ι t) k) q hzero).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ hc
      epi_g := epi_of_isColimit_cofork hc }
  have hq : QuasiIso q := (quasiIso_g_iff_acyclic hse).mpr hVac
  let e : (T : CochainComplex A ℤ) ⊞ (V : CochainComplex A ℤ) ⟶ P :=
    biprod.desc (pushout.inl _ _) (pushout.inr _ _)
  haveI : Epi e := ⟨fun {Z} b c h ↦ pushout.hom_ext
    (by simpa [e] using biprod.inl ≫= h) (by simpa [e] using biprod.inr ≫= h)⟩
  have hsum : CochainComplex.degreewiseCardinalGenerated G κ
      ((T : CochainComplex A ℤ) ⊞ (V : CochainComplex A ℤ)) := by
    intro n
    exact (isCardinalGenerated G κ).prop_of_iso
      ((HomologicalComplex.eval A (ComplexShape.up ℤ) n).mapBiprod _ _).symm
      (generated_biprod G κ (hT n) (hV n))
  refine ⟨P, a, CochainComplex.degreewiseCardinalGenerated_of_epi G κ e hsum, ?_⟩
  rwa [haq]

/-- Coproduct projections commute with a map of families. -/
private theorem sigma_map_projection
    {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{v} C]
    {I : Type v} [DecidableEq I] {X Y : I → C} (a : ∀ i, X i ⟶ Y i) (i : I) :
    Limits.Sigma.map a ≫ Sigma.π Y i = Sigma.π X i ≫ a i := by
  classical
  apply Sigma.hom_ext
  intro j
  by_cases h : j = i
  · subst j
    simp
  · simp [Sigma.ι_π_of_ne _ h, Sigma.ι_π_of_ne_assoc _ h]

attribute [local instance] IsFiltered.isConnected in
set_option backward.isDefEq.respectTransparency false in
/-- In an AB5 category, coproduct projections jointly detect vanishing. Pull back along
the finite partial coproducts; on each pullback the finite sum of coordinate projections
reconstructs the map. -/
private theorem coproduct_projection_zero
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    {I : Type v} [DecidableEq I] (Y : I → C) {X : C} (f : X ⟶ ∐ Y)
    (h : ∀ i, f ≫ Sigma.π Y i = 0) : f = 0 := by
  classical
  open CoproductsFromFiniteFiltered in
  have hz : f ≫ 𝟙 _ = 0 :=
    (isColimitFiniteSubproductsCocone Y).pullback_zero_ext (fun S ↦ by
      let leg := (finiteSubcoproductsCocone Y).ι.app S
      have hj (j : S) : leg ≫ Sigma.π Y j.1.as =
          Sigma.π (fun x : S ↦ Y x.1.as) j := by
        apply Sigma.hom_ext
        intro k
        by_cases hk : k = j
        · subst k
          simp [leg, finiteSubcoproductsCocone_ι_app]
        · have hk' : k.1.as ≠ j.1.as := by
            intro he
            apply hk
            apply Subtype.ext
            exact Discrete.ext he
          simp [leg, finiteSubcoproductsCocone_ι_app,
            Sigma.ι_π_of_ne _ hk, Sigma.ι_π_of_ne _ hk']
      have hp (j : S) : pullback.fst leg f ≫ Sigma.π (fun x : S ↦ Y x.1.as) j = 0 := by
        rw [← hj, ← Category.assoc, pullback.condition, Category.assoc, h, comp_zero]
      change pullback.snd leg f ≫ f ≫ 𝟙 _ = 0
      rw [Category.comp_id, ← pullback.condition]
      calc
        pullback.fst leg f ≫ leg = pullback.fst leg f ≫
            ∑ j ∈ S.attach, Sigma.π _ j ≫ Sigma.ι Y j.1.as := by
          exact congrArg (fun b ↦ pullback.fst leg f ≫ b)
            (finiteSubcoproductsCocone_ι_app_eq_sum Y S)
        _ = 0 := by
          rw [Preadditive.comp_sum]
          apply Finset.sum_eq_zero
          intro j hj'
          rw [← Category.assoc]
          simpa only [Discrete.functor_obj_eq_as, zero_comp] using
            (hp j) =≫ Sigma.ι Y j.1.as)
  simpa using hz

/-- Exactness of coproducts identifies the coproduct of component images as the kernel
of the coproduct of their quotient maps. Joint detection by projections gives the lift. -/
private theorem coproduct_component_images
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    {I : Type v} [DecidableEq I] (Y : I → C) {X : C} (f : X ⟶ ∐ Y) :
    ∃ g : X ⟶ ∐ (fun i ↦ image (f ≫ Sigma.π Y i)),
      g ≫ Limits.Sigma.map (fun i ↦ image.ι (f ≫ Sigma.π Y i)) = f := by
  classical
  let a (i : I) := image.ι (f ≫ Sigma.π Y i)
  let q (i : I) := cokernel.π (a i)
  let S : ShortComplex (Discrete I ⥤ C) :=
    { X₁ := Discrete.functor (fun i ↦ image (f ≫ Sigma.π Y i))
      X₂ := Discrete.functor Y
      X₃ := Discrete.functor (fun i ↦ cokernel (a i))
      f := Discrete.natTrans (fun i ↦ a i.as)
      g := Discrete.natTrans (fun i ↦ q i.as)
      zero := by ext i; exact cokernel.condition (a i.as) }
  have hS : S.Exact := by
    apply ShortComplex.exact_of_f_is_kernel
    refine evaluationJointlyReflectsLimits _ fun i ↦ (KernelFork.isLimitMapConeEquiv _ _).2 ?_
    change IsLimit (KernelFork.ofι (a i.as) (cokernel.condition (a i.as)))
    exact Abelian.monoIsKernelOfCokernel
      (CokernelCofork.ofπ _ (cokernel.condition (a i.as))) (cokernelIsCokernel (a i.as))
  have hz : Limits.Sigma.map a ≫ Limits.Sigma.map q = 0 := by
    apply Sigma.hom_ext
    intro i
    simp [a, q]
  have hex : (ShortComplex.mk (Limits.Sigma.map a) (Limits.Sigma.map q) hz).Exact :=
    colim.exact_mapShortComplex hS (coproductIsCoproduct _) (coproductIsCoproduct _)
      (coproductIsCoproduct _) _ _ (fun ⟨i⟩ ↦ by simp [S]) (fun ⟨i⟩ ↦ by simp [S])
  haveI : Mono (Limits.Sigma.map a) := by
    constructor
    intro Z b c hbc
    apply sub_eq_zero.mp
    apply coproduct_projection_zero
    intro i
    haveI : Mono (a i) := inferInstance
    apply (cancel_mono (a i)).1
    simp only [zero_comp, Preadditive.sub_comp]
    have hi := hbc =≫ Sigma.π Y i
    simpa only [Category.assoc, sigma_map_projection] using sub_eq_zero.mpr hi
  have hf : f ≫ Limits.Sigma.map q = 0 := by
    apply coproduct_projection_zero
    intro i
    rw [Category.assoc, sigma_map_projection, ← Category.assoc]
    calc
      (f ≫ Sigma.π Y i) ≫ q i =
          (factorThruImage (f ≫ Sigma.π Y i) ≫ a i) ≫ q i :=
        congrArg (fun b ↦ b ≫ q i) (image.fac _).symm
      _ = 0 := by rw [Category.assoc, cokernel.condition (a i), comp_zero]
  obtain ⟨g, hg⟩ := KernelFork.IsLimit.lift' hex.fIsKernel f hf
  exact ⟨g, hg⟩

/-- The partial coproducts supported on fewer than α indices form an α-filtered diagram
of split monomorphisms with colimit the full coproduct. The subobject bound on the source
lets any map into that colimit factor through one stage. -/
private theorem alphaSmall_of_subobject_bound
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    (α : Cardinal.{v}) [Fact α.IsRegular] (X : C)
    (hX : HasCardinalLT (Subobject X) α) : IsAlphaSmall X α := by
  classical
  intro I Y f
  let S := HasCardinalLT.Set I α
  let F : S ⥤ C :=
    { obj := fun T ↦ ∐ fun i : T.1 ↦ Y i
      map := fun {T U} h ↦ Sigma.desc fun i ↦ Sigma.ι (fun j : U.1 ↦ Y j)
        ⟨i.1, leOfHom h i.2⟩
      map_id := by intro T; ext i; simp
      map_comp := by intro T U V a b; ext i; simp }
  let c : Cocone F :=
    { pt := ∐ Y
      ι := { app := fun T ↦ Sigma.desc fun i : T.1 ↦ Sigma.ι Y i
             naturality := by intro T U h; ext i; simp [F] } }
  let s (i : I) : S := ⟨{i}, hasCardinalLT_of_finite _ _
    (Cardinal.IsRegular.aleph0_le Fact.out)⟩
  let single (i : I) : (s i).1 := ⟨i, Set.mem_singleton i⟩
  let d (t : Cocone F) : ∐ Y ⟶ t.pt := Sigma.desc fun i ↦
    Sigma.ι (fun j : (s i).1 ↦ Y j) (single i) ≫ t.ι.app (s i)
  have hc : IsColimit c := by
    refine { desc := d, fac := ?_, uniq := ?_ }
    · intro t T
      apply Sigma.hom_ext
      intro i
      let h : s i.1 ⟶ T := homOfLE (by
        intro j hj
        have : j = i.1 := hj
        simp [this, i.2])
      have he := Sigma.ι (fun j : (s i.1).1 ↦ Y j) (single i.1) ≫= t.w h
      simpa [c, d, F, single] using he.symm
    · intro t m hm
      apply Sigma.hom_ext
      intro i
      have he := Sigma.ι (fun j : (s i).1 ↦ Y j) (single i) ≫= hm (s i)
      simpa [c, d, single] using he
  have hm (T : S) : IsSplitMono (c.ι.app T) :=
    ⟨⟨Sigma.desc (fun i ↦ if h : i ∈ T.1 then
      Sigma.ι (fun j : T.1 ↦ Y j) ⟨i, h⟩ else 0), by ext i; simp [c, F, i.2]⟩⟩
  haveI (T U : S) (φ : T ⟶ U) : Mono (F.map φ) := by
    haveI := hm T
    exact mono_of_mono_fac (c.w φ)
  obtain ⟨T, g, hg⟩ := IsGrothendieckAbelian.IsPresentable.surjectivity hc hX f
  exact ⟨T.1, T.2, g, hg.symm⟩

/-- Every derived morphism with bounded source has a roof with bounded middle complex. -/
private theorem bounded_derived_roof
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasDerivedCategory.{v} A]
    (G : A) (κ : Cardinal.{v}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (hG : IsSeparator G)
    (hsub : ∀ n : ℕ, HasCardinalLT (Subobject (∐ fun _ : Fin n ↦ G)) κ)
    {X Y : CochainComplex A ℤ} (hX : CochainComplex.degreewiseCardinalGenerated G κ X)
    (f : DerivedCategory.Q.obj X ⟶ DerivedCategory.Q.obj Y) :
    ∃ (T : CochainComplex A ℤ) (q : T ⟶ X) (b : T ⟶ Y),
      CochainComplex.degreewiseCardinalGenerated G κ T ∧ QuasiIso q ∧
      DerivedCategory.Q.map q ≫ f = DerivedCategory.Q.map b := by
  let Q := DerivedCategory.Q (C := A)
  obtain ⟨W, s, hs, g, hf⟩ := DerivedCategory.right_fac f
  haveI : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso A s).1 hs
  obtain ⟨V, t, p, r, ht, hp, he, htp, htr⟩ := epi_quasiIso_replacement s
  letI := ht
  letI := hp
  letI := he
  have hpf : Q.map p ≫ f = Q.map (r ≫ g) := by
    apply (cancel_epi (Q.map t)).1
    rw [← Functor.map_comp_assoc, htp, hf, IsIso.hom_inv_id_assoc,
      ← Functor.map_comp, ← Category.assoc, htr, Category.id_comp]
  obtain ⟨T, a, hT, hq⟩ := bounded_epi_quasiIso_roof G κ hκ hG hsub p hX
  letI := hq
  refine ⟨T, a ≫ p, a ≫ r ≫ g, hT, hq, ?_⟩
  rw [Functor.map_comp, Category.assoc, hpf]
  simp only [Functor.map_comp, Q]

/-- Reuse the coproduct cofan established by the derived coproduct construction. -/
private theorem derived_Q_preserves_coproduct
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasDerivedCategory.{v} A] {I : Type v} (X : I → CochainComplex A ℤ) :
    PreservesColimit (Discrete.functor X) DerivedCategory.Q := by
  apply preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct X)
  refine (isColimitMapCoconeCofanMkEquiv _ _ _).symm ?_
  simpa using (derivedCoproductCofan I (fun i ↦ DerivedCategory.Q.obj (X i))
    X (fun i ↦ Iso.refl _)).some

/-- Bound the subobject lattices of an essentially small set of representatives. -/
private theorem uniform_subobject_bound
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    (P : ObjectProperty C) [ObjectProperty.EssentiallySmall.{v} P] :
    ∃ (α : Cardinal.{v}), α.IsRegular ∧
      ∀ X, P X → HasCardinalLT (Subobject X) α := by
  obtain ⟨P₀, hP₀, hP₀P, hPP₀⟩ := ObjectProperty.EssentiallySmall.exists_small_le P
  letI := hP₀
  obtain ⟨α, hα, hb⟩ := HasCardinalLT.exists_regular_cardinal_forall
    (fun X : Subtype P₀ ↦ Subobject X.1)
  refine ⟨α, hα, fun X hX ↦ ?_⟩
  obtain ⟨Y, hY, ⟨e⟩⟩ := hPP₀ X hX
  exact Subobject.hasCardinalLT_of_mono (hb ⟨Y, hY⟩) e.hom

attribute [local instance] derived_Q_preserves_coproduct

/-- The coproduct comparison sends the image of each coprojection to its coprojection. -/
@[reassoc (attr := simp)]
private theorem derived_coproduct_inclusion
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasDerivedCategory.{v} A] {I : Type v} (X : I → CochainComplex A ℤ) (i : I) :
    DerivedCategory.Q.map (Sigma.ι X i) ≫
      (PreservesCoproduct.iso DerivedCategory.Q X).hom =
        Sigma.ι (fun i ↦ DerivedCategory.Q.obj (X i)) i := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (isColimitOfHasCoproductOfPreservesColimit DerivedCategory.Q X)
    (colimit.isColimit _) ⟨i⟩

/-- The coproduct comparison is natural in the family. -/
@[reassoc]
private theorem derived_coproduct_naturality
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasDerivedCategory.{v} A] {I : Type v} {X Y : I → CochainComplex A ℤ}
    (a : ∀ i, X i ⟶ Y i) :
    (PreservesCoproduct.iso DerivedCategory.Q X).hom ≫
        Limits.Sigma.map (fun i ↦ DerivedCategory.Q.map (a i)) =
      DerivedCategory.Q.map (Limits.Sigma.map a) ≫
        (PreservesCoproduct.iso DerivedCategory.Q Y).hom := by
  apply (isColimitOfHasCoproductOfPreservesColimit DerivedCategory.Q X).hom_ext
  rintro ⟨i⟩
  dsimp only [Cofan.mk_ι_app]
  rw [derived_coproduct_inclusion_assoc, Sigma.ι_map,
    ← Functor.map_comp_assoc, Sigma.ι_map, Functor.map_comp,
    Category.assoc, derived_coproduct_inclusion]

/-- Use a bounded roof, factor its chain map through its component images, and apply Q. -/
private theorem bounded_class_factorization
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasDerivedCategory.{v} A]
    (G : A) (κ : Cardinal.{v}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (hG : IsSeparator G)
    (hsub : ∀ n : ℕ, HasCardinalLT (Subobject (∐ fun _ : Fin n ↦ G)) κ) :
    ((CochainComplex.degreewiseCardinalGenerated G κ).map
      DerivedCategory.Q).IsCoproductFactorizationClass := by
  classical
  intro U hU I Y f
  obtain ⟨X, hX, ⟨e⟩⟩ := hU
  let Q := DerivedCategory.Q (C := A)
  let K (i : I) := Q.objPreimage (Y i)
  let eY (i : I) : Q.obj (K i) ≅ Y i := Q.objObjPreimageIso (Y i)
  let eSum : Q.obj (∐ K) ≅ ∐ Y :=
    PreservesCoproduct.iso Q K ≪≫ Limits.Sigma.mapIso eY
  let f₀ := e.hom ≫ f ≫ eSum.inv
  obtain ⟨T, q, b, hT, hq, he⟩ := bounded_derived_roof G κ hκ hG hsub hX f₀
  letI := hq
  let Z (i : I) := image (b ≫ Sigma.π K i)
  let a (i : I) : Z i ⟶ K i := image.ι (b ≫ Sigma.π K i)
  obtain ⟨g, hg⟩ := coproduct_component_images K b
  refine ⟨fun i ↦ Q.obj (Z i), ?_, fun i ↦ Q.map (a i) ≫ (eY i).hom,
    e.inv ≫ inv (Q.map q) ≫ Q.map g ≫ (PreservesCoproduct.iso Q Z).hom, ?_⟩
  · intro i
    refine ⟨Z i, ?_, ⟨Iso.refl _⟩⟩
    exact CochainComplex.degreewiseCardinalGenerated_of_epi G κ
      (factorThruImage (b ≫ Sigma.π K i)) hT
  · have ha : Limits.Sigma.map (fun i ↦ Q.map (a i) ≫ (eY i).hom) =
        Limits.Sigma.map (fun i ↦ Q.map (a i)) ≫ (Limits.Sigma.mapIso eY).hom := by
      apply Sigma.hom_ext
      intro i
      simp
    rw [ha]
    simp only [Category.assoc]
    rw [derived_coproduct_naturality_assoc, ← Functor.map_comp_assoc, hg]
    change e.inv ≫ inv (Q.map q) ≫ Q.map b ≫ eSum.hom = f
    rw [← he]
    simp [f₀]

/-- The support bound for a bounded roof passes to the corresponding derived morphism. -/
private theorem bounded_class_alphaSmall
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasDerivedCategory.{v} A]
    (G : A) (κ α : Cardinal.{v}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (hG : IsSeparator G)
    (hsub : ∀ n : ℕ, HasCardinalLT (Subobject (∐ fun _ : Fin n ↦ G)) κ)
    (hs : ∀ X, CochainComplex.degreewiseCardinalGenerated G κ X → IsAlphaSmall X α) :
    ∀ U, (CochainComplex.degreewiseCardinalGenerated G κ).map DerivedCategory.Q U →
      IsAlphaSmall U α := by
  classical
  intro U hU I Y f
  obtain ⟨X, hX, ⟨e⟩⟩ := hU
  let Q := DerivedCategory.Q (C := A)
  let K (i : I) := Q.objPreimage (Y i)
  let eY (i : I) : Q.obj (K i) ≅ Y i := Q.objObjPreimageIso (Y i)
  let eSum : Q.obj (∐ K) ≅ ∐ Y :=
    PreservesCoproduct.iso Q K ≪≫ Limits.Sigma.mapIso eY
  let f₀ := e.hom ≫ f ≫ eSum.inv
  obtain ⟨T, q, b, hT, hq, he⟩ := bounded_derived_roof G κ hκ hG hsub hX f₀
  letI := hq
  obtain ⟨J, hJ, g, hg⟩ := hs T hT I K b
  let eJ : Q.obj (∐ fun j : J ↦ K j) ≅ ∐ fun j : J ↦ Y j :=
    PreservesCoproduct.iso Q (fun j : J ↦ K j) ≪≫
      Limits.Sigma.mapIso (fun j : J ↦ eY j)
  have hi : eJ.hom ≫ Sigma.desc (fun j : J ↦ Sigma.ι Y j) =
      Q.map (Sigma.desc (fun j : J ↦ Sigma.ι K j)) ≫ eSum.hom := by
    apply (isColimitOfHasCoproductOfPreservesColimit Q (fun j : J ↦ K j)).hom_ext
    rintro ⟨j⟩
    dsimp only [Cofan.mk_ι_app, eJ, eSum, Iso.trans_hom]
    dsimp only [Q]
    simp only [Category.assoc, derived_coproduct_inclusion_assoc,
      Sigma.ι_mapIso_hom_assoc, Sigma.ι_comp_desc, ← Functor.map_comp_assoc,
      Sigma.ι_mapIso_hom]
  refine ⟨J, hJ, e.inv ≫ inv (Q.map q) ≫ Q.map g ≫ eJ.hom, ?_⟩
  simp only [Category.assoc]
  rw [hi, ← Functor.map_comp_assoc, hg]
  change e.inv ≫ inv (Q.map q) ≫ Q.map b ≫ eSum.hom = f
  rw [← he]
  simp [f₀]

/-- One regular cardinal bounds the finite copowers and every component of a small family. -/
private theorem bounded_family_cardinal
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    {J : Type v} (X : J → CochainComplex A ℤ) :
    ∃ (κ : Cardinal.{v}), κ.IsRegular ∧ Cardinal.aleph0 < κ ∧
      (∀ n : ℕ, HasCardinalLT (Subobject (∐ fun _ : Fin n ↦ separator A)) κ) ∧
      ∀ j, CochainComplex.degreewiseCardinalGenerated (separator A) κ (X j) := by
  let F : Option (ULift.{v} ℕ ⊕ (J × ULift.{v} ℤ)) → Type (max u v) :=
    fun i ↦ match i with
    | none => ULift.{max u v} ℕ
    | some (.inl n) => Subobject (∐ fun _ : Fin n.down ↦ separator A)
    | some (.inr j) => Subobject ((X j.1).X j.2.down)
  have hsmall : ∀ i, Small.{v} (F i) := by
    intro i
    rcases i with _ | (n | j) <;> dsimp [F] <;> infer_instance
  letI := hsmall
  obtain ⟨κ, hκ, hb⟩ := HasCardinalLT.exists_regular_cardinal_forall F
  refine ⟨κ, hκ, ?_, fun n ↦ hb (some (.inl ⟨n⟩)), fun j n ↦ ?_⟩
  · have h : HasCardinalLT (ULift.{max u v} ℕ) κ := hb none
    have h' : HasCardinalLT (ULift.{v} ℕ) κ := by simpa using h
    rw [hasCardinalLT_iff_cardinal_mk_lt] at h'
    simpa using h'
  · exact isCardinalGenerated_of_hasCardinalLT_subobject (separator A) κ
      (isSeparator_separator A) (hb (some (.inr (j, ⟨n⟩))))

/-- Supporting small-class construction for the exact compact localization.
Source: Neeman, Theorem 0.2 and Krause, Sections 6.2--6.3.
(blueprint: new-sfb-derived-perfect-well-generators-support-b4)

Proof in words: choose the exact compact localization model and a complex representative
of each image generator. Choose a regular cardinal dominating the subobject lattices of
all their components, the finite copowers of a separator, and the natural numbers. Let P
be the class of complexes generated degreewise by fewer than this many separator copies,
and take its essential image under Q. Quotients of a fixed disk copower give essential
smallness; reindexing degrees gives shift stability.

Every map from such an object has a roof with middle complex in P: replace the denominator
by an epimorphic quasi-isomorphism, cover its target by a bounded subcomplex, and enlarge
the resulting kernel inside the acyclic denominator kernel before pushing out. A chain map
from that middle complex to a coproduct factors through the coproduct of its component
images, which are again in P. Applying Q gives the factorization condition. Finally bound
the subobject lattices of representatives of P by a common regular cardinal. Maps from
these representatives into coproducts factor through partial coproducts of that size, and
the bounded-roof argument transfers this support bound to the derived category. The chosen
image generators belong by the initial cardinal bound. The importing theorem separately
uses the compact-generator telescope to prove localizing generation. -/
theorem exists_small_factorization_class_of_compact_localization
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] [HasDerivedCategory.{v} A] :
    ∃ (B : Type (max u (v + 1))) (cB : Category.{v} B),
      letI := cB
      ∃ (zB : HasZeroObject B) (sB : HasShift B ℤ) (pB : Preadditive B),
      letI := zB
      letI := sB
      letI := pB
      ∃ aB : ∀ n : ℤ, (shiftFunctor B n).Additive,
      letI := aB
      ∃ tB : Pretriangulated B,
      letI := tB
      ∃ (iB : IsTriangulated B) (sumsB : HasCoproducts.{v} B),
      letI := iB
      letI := sumsB
      ∃ (J : Type v) (E : J → B),
        (∀ j, IsCompactObject (E j)) ∧ IsTriangulatedGeneratingFamily E ∧
        ∃ (L : B ⥤ DerivedCategory A) (R : DerivedCategory A ⥤ B)
          (adj : L ⊣ R) (sL : L.CommShift ℤ),
          letI := sL
          L.IsTriangulated ∧ IsIso adj.counit ∧
          ∃ (G : ObjectProperty (DerivedCategory A)) (κ : Cardinal.{v})
            (_ : Fact κ.IsRegular),
            ObjectProperty.EssentiallySmall.{v} G ∧ G.IsStableUnderShift ℤ ∧
            (∀ U, G U → IsAlphaSmall U κ) ∧
            G.IsCoproductFactorizationClass ∧
            ∀ j, G (L.obj (E j)) := by
  classical
  obtain ⟨B, cB, zB, sB, pB, aB, tB, iB, sumsB, hB, L, R, adj, sL, hL, hc⟩ :=
    grothendieckDerived_compact_localization_model.{v, u, v, v} (A := A)
  letI := cB
  letI := zB
  letI := sB
  letI := pB
  letI := aB
  letI := tB
  letI := iB
  letI := sumsB
  letI := sL
  obtain ⟨J, E, hE, hgen⟩ := hB
  let X (j : J) := DerivedCategory.Q.objPreimage (L.obj (E j))
  obtain ⟨κ, hκreg, hκ, hsub, hX⟩ := bounded_family_cardinal X
  letI : Fact κ.IsRegular := ⟨hκreg⟩
  let P := CochainComplex.degreewiseCardinalGenerated (separator A) κ
  haveI : ObjectProperty.EssentiallySmall.{v} P :=
    bounded_complexes_essentiallySmall (separator A) κ
  obtain ⟨α, hα, hb⟩ := uniform_subobject_bound P
  letI : Fact α.IsRegular := ⟨hα⟩
  let S := P.map DerivedCategory.Q
  refine ⟨B, cB, zB, sB, pB, aB, tB, iB, sumsB, J, E, hE, hgen,
    L, R, adj, sL, hL, hc, S, α, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun n ↦ ⟨?_⟩⟩
    rintro U ⟨K, hK, ⟨e⟩⟩
    exact ⟨K⟦n⟧, bounded_complexes_shift (separator A) κ K hK n,
      ⟨(DerivedCategory.Q.commShiftIso n).app K ≪≫
        (shiftFunctor (DerivedCategory A) n).mapIso e⟩⟩
  · exact bounded_class_alphaSmall (separator A) κ α hκ (isSeparator_separator A) hsub
      (fun K hK ↦ alphaSmall_of_subobject_bound α K (hb K hK))
  · exact bounded_class_factorization (separator A) κ hκ (isSeparator_separator A) hsub
  · intro j
    exact ⟨X j, hX j, ⟨DerivedCategory.Q.objObjPreimageIso (L.obj (E j))⟩⟩

end CategoryTheory
