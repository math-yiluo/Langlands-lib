/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Perfect.IntegralPerfectStratumPieces
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryIntegralLocalModels
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.ExtensionZeroPerfectModelTransport
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Complete.CompleteCompactSupportProetale
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIdentifiedOpenClosed
import all WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedEssentialImage
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.Open.OpenClosedAdjunctionTransport
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.ConstructibleSheaf.Devissage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-! # Finite devissage of integral stratified perfect complexes

## References

* Bhatt--Scholze, Lemma 6.3.14, final paragraph, as used in Lemma 6.8.12
* Bhatt--Scholze, Lemma 6.3.14, final devissage
* Bhatt--Scholze, Proposition 6.6.11
-/

@[expose] public noncomputable section
set_option autoImplicit false

attribute [-instance] CategoryTheory.flatConstantModulesAbelian

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped ZeroObject
namespace AlgebraicGeometry.Scheme

private theorem reduced_factors_immersion
    {X Y Z : Scheme.{u}} [IsReduced Z] (i : Y ⟶ X) [IsImmersion i]
    (f : Z ⟶ X) (h : Set.range f ⊆ Set.range i) : ∃ g : Z ⟶ Y, g ≫ i = f := by
  let f' := IsOpenImmersion.lift i.coborderRange.ι f
    (h.trans (by
      rw [Scheme.Opens.range_ι]
      change Set.range i ⊆ coborder (Set.range i)
      exact subset_coborder))
  have hf : f' ≫ i.coborderRange.ι = f := IsOpenImmersion.lift_fac _ _ _
  let hr : Set.range f' ⊆ Set.range i.liftCoborder := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨y, hy⟩ := h ⟨z, rfl⟩
    refine ⟨y, i.coborderRange.ι.isEmbedding.injective ?_⟩
    exact (congrArg (fun k : Y ⟶ X ↦ k y) i.liftCoborder_ι).trans
      (hy.trans (congrArg (fun k : Z ⟶ X ↦ k z) hf).symm)
  obtain ⟨g, hg, -⟩ := IsClosedImmersion.existsUnique_fac_of_range_subset_range
    i.liftCoborder f' hr
  exact ⟨g, by rw [← i.liftCoborder_ι, ← Category.assoc, hg, hf]⟩

private theorem geometric_filtration (T : Scheme.{u}) [IsNoetherian T]
    (s : Stratification T) :
    ∃ (n : ℕ) (V : Fin (n + 1) → T.Opens),
      Monotone V ∧ V 0 = ⊥ ∧ V (Fin.last n) = ⊤ ∧
      ∃ (Z : Fin n → Scheme.{u}) (i : ∀ k : Fin n, Z k ⟶ (V k.succ).toScheme),
        (∀ k, IsClosedImmersion (i k) ∧ IsReduced (Z k) ∧
          Set.range (i k) = {x | (V k.succ).ι x ∉ V k.castSucc}) ∧
        ∀ k, ∃ a : Fin s.n, ∃ g : Z k ⟶ s.domain a,
          g ≫ s.immersion a = i k ≫ (V k.succ).ι := by
  classical
  obtain ⟨n, V, hV0, hVn, hstep⟩ := s.toStratification.exists_chain_opens (⊥ : T.Opens)
  change Fin (n + 1) → T.Opens at V
  have hV : Monotone V := Fin.monotone_iff_le_succ.mpr fun k ↦ (hstep k).1
  have hc (k : Fin n) : ∃ (Z : Scheme.{u}) (i : Z ⟶ (V k.succ).toScheme),
      IsClosedImmersion i ∧ IsReduced Z ∧
        Set.range i = {x | (V k.succ).ι x ∉ V k.castSucc} := by
    let U := (V k.succ).ι ⁻¹ᵁ V k.castSucc
    let F : TopologicalSpace.Closeds (V k.succ).toScheme :=
      ⟨(U : Set (V k.succ).toScheme)ᶜ, U.isOpen.isClosed_compl⟩
    have h := Scheme.IdealSheafData.reduced_induced_closed_subscheme _ F
    exact ⟨_, _, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.1⟩
  choose Z i hi hred hr using hc
  refine ⟨n, V, hV, hV0, hVn, Z, i, fun k ↦ ⟨hi k, hred k, hr k⟩, ?_⟩
  intro k
  have := hred k
  obtain ⟨a, ha⟩ := (hstep k).2
  have hs : Set.range (i k ≫ (V k.succ).ι) ⊆ Set.range (s.immersion a) := by
    rw [s.range_immersion]
    rintro _ ⟨z, rfl⟩
    apply ha
    refine ⟨by simp, ?_⟩
    have hz : i k z ∈ Set.range (i k) := Set.mem_range_self z
    rw [hr k] at hz
    exact hz
  obtain ⟨g, hg⟩ := reduced_factors_immersion (s.immersion a) _ hs
  exact ⟨a, g, hg⟩

private theorem locallyPerfect_on_stratum
    {T Z : Scheme.{u}} {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d)))
    (b : ℤ) [K.IsLE b] (s : Stratification T) (a : Fin s.n)
    (f : Z ⟶ T) (g : Z ⟶ s.domain a) (hg : g ≫ s.immersion a = f)
    (hs : ∃ V : Sieve (⊤_ (s.domain a).ProEt),
      V ∈ ProEt.topology (s.domain a) (⊤_ (s.domain a).ProEt) ∧
      ∀ (U : (s.domain a).ProEt) (z : U ⟶ ⊤_ (s.domain a).ProEt), V z →
        ∃ P : completedConstantDerived (ModuleCat.{u + 1} A),
          @DerivedCategory.IsPerfectRingComplex A _
            (HasDerivedCategory.standard (ModuleCat.{u + 1} A)) P ∧
          Nonempty (integralLocalDerived (s.immersion a) (pbcAdicCompletion T d) U K ≅
            integralLocalDerived (s.immersion a) (pbcAdicCompletion T d) U
              ((integralConstantDerived T d).obj P))) :
    IsIntegralLocallyPerfect Z d ((d.pull f).obj K) := by
  classical
  refine ⟨⟨b, ?_⟩, ?_⟩
  · exact Functor.isLE_mapDerivedCategory_obj
      (proEtaleRingModulePullback f (d.completedRing T) (d.completedRing Z)
        (d.integralRingIso f)) K b
  · obtain ⟨V, hV, hm⟩ := hs
    let F := proEtaleBaseChange g
    let hT := (terminalIsTerminal (C := (s.domain a).ProEt)).isTerminalObj F
    let z := hT.from (⊤_ Z.ProEt)
    let W := (V.functorPushforward F).pullback z
    have hW : W ∈ ProEt.topology Z (⊤_ Z.ProEt) :=
      (ProEt.topology _).pullback_stable z
        ((CoverPreserving.of_isContinuous F _ _).cover_preserve hV)
    refine ⟨W, hW, ?_⟩
    intro U z hz
    obtain ⟨B, q, c, hq, _⟩ := hz
    obtain ⟨P, hP, he⟩ := hm B q hq
    refine ⟨P, hP, (localModel_iff d (𝟙 Z) U ((d.pull f).obj K) P).mpr ?_⟩
    obtain ⟨e⟩ := (localModel_iff d (s.immersion a) B K P).mp he
    let v : U.left ⟶ B.left := c.left ≫ pullback.fst B.hom g
    have hc : c.left ≫ pullback.snd B.hom g = U.hom := by
      have hw := c.w
      change c.left ≫ pullback.snd B.hom g = U.hom ≫ 𝟙 _ at hw
      simpa only [Category.comp_id] using hw
    have hv : U.hom ≫ f = v ≫ (B.hom ≫ s.immersion a) := by
      rw [← hg]
      calc
        _ = (c.left ≫ pullback.snd B.hom g) ≫ (g ≫ s.immersion a) := by rw [hc]
        _ = v ≫ (B.hom ≫ s.immersion a) := by
          simpa only [v, Category.assoc] using congrArg
            (fun h ↦ c.left ≫ h ≫ s.immersion a)
            (pullback.condition (f := B.hom) (g := g)).symm
    let t : (d.pull U.hom).obj ((d.pull f).obj K) ≅
        (d.pull v).obj ((d.pull (B.hom ≫ s.immersion a)).obj K) :=
      ((d.pullComp U.hom f).app K).symm ≪≫
        eqToIso (congrArg (fun h ↦ (d.pull h).obj K) hv) ≪≫
        (d.pullComp v (B.hom ≫ s.immersion a)).app K
    have hid : U.hom ≫ 𝟙 Z = U.hom := Category.comp_id U.hom
    exact ⟨eqToIso (congrArg (fun h ↦ (d.pull h).obj ((d.pull f).obj K)) hid) ≪≫
      t ≪≫ (d.pull v).mapIso e ≪≫ (integralConstantDerivedPullIso d v).app P⟩

private theorem module_localization
    {X Z : Scheme.{u}} {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (i : Z ⟶ X) [IsClosedImmersion i] (U : X.ProEt)
    [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ) :
    let P := proEtaleRingModulePullback U.hom (d.completedRing X)
      (d.completedRing U.left) (d.integralRingIso U.hom)
    let Q := proEtaleRingModulePullback i (d.completedRing X)
      (d.completedRing Z) (d.integralRingIso i)
    let D := proEtaleRingModuleDirectImage i (d.completedRing X)
      (d.completedRing Z) (d.integralRingIso i)
    ∃ (ε : P ⋙ cbcOpenShriek d U.hom inferInstance ⟶ 𝟭 _)
      (η : 𝟭 _ ⟶ Q ⋙ D), ∀ M,
      Mono (ε.app M) ∧ Epi (η.app M) ∧
        (ComposableArrows.mk₂ (ε.app M) (η.app M)).Exact := by
  dsimp only
  let R := d.completedRing X
  let S := d.completedRing U.left
  let Si := d.completedRing Z
  let P := proEtaleRingModulePullback U.hom R S (d.integralRingIso U.hom)
  let Q := proEtaleRingModulePullback i R Si (d.integralRingIso i)
  let D := proEtaleRingModuleDirectImage i R Si (d.integralRingIso i)
  obtain ⟨q, ⟨hq⟩, ai, aj, _, _, _, _, hl, hc, _, _, hs, _⟩ :=
    proEtale_ringed_open_closed i U hU R
  let eu := proEtaleScalarEquivalence U.left ((sheafCompose (ProEt.topology U.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (d.integralRingIso U.hom))
  let ei := proEtaleScalarEquivalence Z ((sheafCompose (ProEt.topology Z)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (d.integralRingIso i))
  let au := proEtaleModuleInverseImageAdjunction U.hom R
  let t := (proEtaleRingModuleAdjunction U.hom R S (d.integralRingIso U.hom)).leftAdjointUniq
    ((au.comp eu.symm.toAdjunction).ofNatIsoRight
      (coefficientDirectImageIso U.hom R S (d.integralRingIso U.hom)))
  let ti := (proEtaleRingModuleAdjunction i R Si (d.integralRingIso i)).leftAdjointUniq
    ((ai.comp ei.symm.toAdjunction).ofNatIsoRight
      (coefficientDirectImageIso i R Si (d.integralRingIso i)))
  let p : P ⋙ eu.functor ≅ proEtaleModuleInverseImage U.hom R :=
    Functor.isoWhiskerRight t eu.functor ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ eu.counitIso ≪≫ Functor.rightUnitor _
  let pi : Q ⋙ ei.functor ≅ proEtaleModuleInverseImage i R :=
    Functor.isoWhiskerRight ti ei.functor ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ei.counitIso ≪≫ Functor.rightUnitor _
  let E := eu.trans q
  let hE : P ⋙ E.functor ≅ SheafOfModules.overFunctor (proEtaleModuleCoefficients R) U :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight p q.functor ≪≫ hq
  let a := AlgebraicGeometry.ProEtale.openAdjunctionTransport E P
    (proEtaleRingedExtensionByZero U R) _ aj hE
  let b := (cbcOpenAdjunction d U.hom inferInstance).ofNatIsoRight
    (@asIso _ _ _ _ (cbcPullToRestriction d U.hom)
      (cbcPullToRestriction_isIso d U.hom)).symm
  let c := a.leftAdjointUniq b
  let eo : P ⋙ cbcOpenShriek d U.hom inferInstance ≅
      SheafOfModules.overFunctor (proEtaleModuleCoefficients R) U ⋙
        proEtaleRingedExtensionByZero U R :=
    Functor.isoWhiskerLeft P c.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight hE (proEtaleRingedExtensionByZero U R)
  let ec : Q ⋙ D ≅ proEtaleModuleInverseImage i R ⋙ proEtaleRingedDirectImage i R :=
    Functor.isoWhiskerLeft Q (coefficientDirectImageIso i R Si (d.integralRingIso i)).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight pi (proEtaleRingedDirectImage i R)
  refine ⟨eo.hom ≫ aj.counit, ai.unit ≫ ec.inv, ?_⟩
  intro M
  obtain ⟨hf, hg, hex⟩ := hs M
  have := hf
  have := hg
  exact AlgebraicGeometry.ProEtale.exact_localization_transport
    (aj.counit.app M) (ai.unit.app M) hex (eo.app M) (ec.app M)

private theorem exact_functors_triangle
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F G : C ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (ε : F ⟶ 𝟭 C) (η : 𝟭 C ⟶ G)
    (hs : ∀ M, Mono (ε.app M) ∧ Epi (η.app M) ∧
      (ComposableArrows.mk₂ (ε.app M) (η.app M)).Exact)
    (K : DerivedCategory C) :
    ∃ (f : F.mapDerivedCategory.obj K ⟶ K) (g : K ⟶ G.mapDerivedCategory.obj K)
      (h : G.mapDerivedCategory.obj K ⟶ (F.mapDerivedCategory.obj K)⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang _ := by
  let B := (DerivedCategory.Q (C := C)).objPreimage K
  let e := (DerivedCategory.Q (C := C)).objObjPreimageIso K
  let S : ShortComplex (CochainComplex C ℤ) :=
    ShortComplex.mk ((NatTrans.mapHomologicalComplex ε (.up ℤ)).app B)
      ((NatTrans.mapHomologicalComplex η (.up ℤ)).app B) (by
        ext n
        exact (hs (B.X n)).2.2.toIsComplex.zero 0)
  have hS : S.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact S
    (fun n ↦ { exact :=
      ((ComposableArrows.mk₂ (ε.app (B.X n)) (η.app (B.X n))).exact₂_iff
        (hs (B.X n)).2.2.toIsComplex).1 (hs (B.X n)).2.2
               mono_f := (hs (B.X n)).1
               epi_g := (hs (B.X n)).2.1 })
  let a := F.mapDerivedCategory.mapIso e.symm ≪≫ F.mapDerivedCategoryFactors.app B
  let c := G.mapDerivedCategory.mapIso e.symm ≪≫ G.mapDerivedCategoryFactors.app B
  let f := a.hom ≫ DerivedCategory.Q.map S.f ≫ e.hom
  let g := e.inv ≫ DerivedCategory.Q.map S.g ≫ c.inv
  let h := c.hom ≫ DerivedCategory.triangleOfSESδ hS ≫ a.inv⟦(1 : ℤ)⟧'
  refine ⟨f, g, h, isomorphic_distinguished _
    (DerivedCategory.triangleOfSES_distinguished hS) _
    (Triangle.isoMk _ _ a e.symm c ?_ ?_ ?_)⟩
  · simp [f, Category.assoc]
  · simp [g, Category.assoc]
  · simp [h, Category.assoc, ← Functor.map_comp]

private theorem derived_localization
    {X Z : Scheme.{u}} {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (i : Z ⟶ X) [IsClosedImmersion i] (U : X.ProEt)
    [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) :
    ∃ (f : (cbcDerivedOpenShriek d U.hom inferInstance).obj ((d.pull U.hom).obj K) ⟶ K)
      (g : K ⟶ (d.push i).obj ((d.pull i).obj K))
      (h : (d.push i).obj ((d.pull i).obj K) ⟶
        ((cbcDerivedOpenShriek d U.hom inferInstance).obj
          ((d.pull U.hom).obj K))⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang _ := by
  let P := proEtaleRingModulePullback U.hom (d.completedRing X)
    (d.completedRing U.left) (d.integralRingIso U.hom)
  let Q := proEtaleRingModulePullback i (d.completedRing X)
    (d.completedRing Z) (d.integralRingIso i)
  let D := proEtaleRingModuleDirectImage i (d.completedRing X)
    (d.completedRing Z) (d.integralRingIso i)
  obtain ⟨hl, hc, _⟩ := proEtaleIdentifiedOpenClosed i U hU (d.completedRing X)
    (d.completedRing Z) (d.completedRing U.left)
    (d.integralRingIso i) (d.integralRingIso U.hom)
  have : PreservesFiniteLimits D := hl
  have : PreservesFiniteColimits D := hc
  have : (cbcOpenShriek d U.hom inferInstance).Additive :=
    cbcOpenShriek_additive d U.hom inferInstance
  have : PreservesFiniteLimits (cbcOpenShriek d U.hom inferInstance) :=
    cbcOpenShriek_finiteLimits d U.hom inferInstance
  have : PreservesFiniteColimits (cbcOpenShriek d U.hom inferInstance) :=
    cbcOpenShriek_finiteColimits d U.hom inferInstance
  obtain ⟨ε, η, hs⟩ := module_localization d i U hU
  obtain ⟨f, g, h, hT⟩ := exact_functors_triangle
    (P ⋙ cbcOpenShriek d U.hom inferInstance) (Q ⋙ D) ε η hs K
  let a := (Functor.mapDerivedCategoryCompIso P
    (cbcOpenShriek d U.hom inferInstance)).symm.app K
  let c := (Functor.mapDerivedCategoryCompIso Q D).symm.app K ≪≫
    (D.rightDerivedFunctorIsoMapDerivedCategory.app ((d.pull i).obj K)).symm
  refine ⟨a.inv ≫ f, g ≫ c.hom, c.inv ≫ h ≫ a.hom⟦(1 : ℤ)⟧',
    Pretriangulated.isomorphic_distinguished
      (C := DerivedCategory (pbcModules X (pbcAdicCompletion X d))) _ hT _
      (Triangle.isoMk _ _ a.symm (Iso.refl _) c.symm ?_ ?_ ?_)⟩
  · simp
  · simp [Category.assoc]
  · let S := shiftFunctor (DerivedCategory (pbcModules X (pbcAdicCompletion X d))) (1 : ℤ)
    change (c.inv ≫ h ≫ S.map a.hom) ≫ S.map a.inv = c.inv ≫ h
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
    erw [S.map_id, Category.comp_id]

private theorem locallyPerfect_of_iso
    {X : Scheme.{u}} {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {K L : DerivedCategory (pbcModules X (pbcAdicCompletion X d))}
    (e : K ≅ L) (hK : IsIntegralLocallyPerfect X d K) :
    IsIntegralLocallyPerfect X d L := by
  obtain ⟨⟨b, hb⟩, V, hV, hm⟩ := hK
  have := hb
  refine ⟨⟨b, DerivedCategory.TStructure.t.isLE_of_iso e b⟩, V, hV, ?_⟩
  intro U f hf
  obtain ⟨P, hP, he⟩ := hm U f hf
  obtain ⟨he⟩ := (localModel_iff d (𝟙 X) U K P).mp he
  exact ⟨P, hP, (localModel_iff d (𝟙 X) U L P).mpr
    ⟨((d.pull (U.hom ≫ 𝟙 X)).mapIso e).symm ≪≫ he⟩⟩

private theorem zero_perfect (A : Type (u + 1)) [CommRing A] :
    let := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
    DerivedCategory.IsPerfectRingComplex (0 : DerivedCategory (ModuleCat.{u + 1} A)) := by
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  let P : CochainComplex (ModuleCat.{u + 1} A) ℤ := 0
  refine ⟨P, 0, 0, inferInstance, inferInstance, ?_, ?_⟩
  · intro n
    have hz := (HomologicalComplex.eval _ _ n).map_isZero
      (isZero_zero (CochainComplex (ModuleCat.{u + 1} A) ℤ))
    have : Subsingleton (P.X n) := ModuleCat.subsingleton_of_isZero hz
    exact ⟨inferInstance, inferInstance⟩
  · exact ⟨(isZero_zero _).iso (DerivedCategory.Q.map_isZero (isZero_zero _))⟩

private theorem zero_locallyPerfect
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    IsIntegralLocallyPerfect X d 0 := by
  refine ⟨⟨0, inferInstance⟩, ⊤, GrothendieckTopology.top_mem _ _, ?_⟩
  intro U f hf
  refine ⟨0, zero_perfect A, (localModel_iff d (𝟙 X) U _ _).mpr ?_⟩
  have hleft := (d.pull (U.hom ≫ 𝟙 X)).map_isZero (isZero_zero _)
  have hright : IsZero ((integralConstantDerived U.left d).obj 0) := by
    dsimp only [integralConstantDerived]
    exact Functor.map_isZero _ (isZero_zero _)
  exact ⟨hleft.iso hright⟩

private theorem zero_piece
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d))) (hK : IsZero K) :
    IsIntegralPerfectStratumPiece T d K := by
  refine ⟨T, T, 𝟙 T, inferInstance, 𝟙 T, inferInstance, 0,
    zero_locallyPerfect T d, ?_⟩
  have hpush : IsZero ((d.push (𝟙 T)).obj 0) :=
    (isZero_zero _).of_iso ((d.pushId T).app 0)
  have hz : IsZero ((cbcDerivedOpenShriek d (𝟙 T) inferInstance).obj
      ((d.push (𝟙 T)).obj 0)) := by
    change IsZero ((cbcOpenShriek d (𝟙 T) inferInstance).mapDerivedCategory.obj _)
    exact Functor.map_isZero _ hpush
  exact ⟨hK.iso hz⟩

private theorem empty_derived_zero
    (X : Scheme.{u}) [IsEmpty X] {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) : IsZero K := by
  apply (DerivedCategory.isZero_iff K).2
  intro n
  let M := (DerivedCategory.homologyFunctor _ n).obj K
  apply (IsZero.iff_id_eq_zero M).2
  ext U x
  have : IsEmpty U.unop.left := ⟨fun y ↦ isEmptyElim (show X from U.unop.hom y)⟩
  let ht := ProEt.isTerminalSectionsOfIsEmpty
    ((SheafOfModules.toSheaf _).obj M) U.unop
  have hz : IsZero (((SheafOfModules.toSheaf _).obj M).obj.obj U) :=
    (isZero_zero AddCommGrpCat).of_iso (ht.uniqueUpToIso HasZeroObject.zeroIsTerminal)
  exact (AddCommGrpCat.subsingleton_of_isZero hz).elim _ _

private theorem pull_iso_equivalence
    {X Y : Scheme.{u}} {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (j : X ⟶ Y) [IsIso j] : (d.pull j).IsEquivalence := by
  let a : d.pull j ⋙ d.pull (inv j) ≅ 𝟭 _ :=
    (d.pullComp (inv j) j).symm ≪≫
      eqToIso (congrArg d.pull (IsIso.inv_hom_id j)) ≪≫ d.pullId Y
  let b : d.pull (inv j) ⋙ d.pull j ≅ 𝟭 _ :=
    (d.pullComp j (inv j)).symm ≪≫
      eqToIso (congrArg d.pull (IsIso.hom_inv_id j)) ≪≫ d.pullId X
  exact Functor.IsEquivalence.mk' (d.pull (inv j)) a.symm b

private theorem iter_of_iso
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] (n : ℕ)
    {X Y : C} (e : X ≅ Y) (h : P.extensionProductIter n X) :
    P.extensionProductIter n Y := by
  cases n with
  | zero => exact P.prop_of_iso e h
  | succ n =>
    rw [ObjectProperty.extensionProductIter_succ] at h ⊢
    exact ObjectProperty.prop_of_iso _ e h

/-- A stratified perfect source is a finite extension of locally perfect pieces
supported on locally closed subschemes. This assertion is purely about the source;
it makes no reference to an internal Hom functor, target family, or colimit. -/
theorem integralStratifiedPerfect_mem_stratum_extensions
    (T : Scheme.{u}) [IsNoetherian T]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d)))
    (b : ℤ) [K.IsLE b] (hK : IsIntegralStratifiedPerfect T d K) :
    ∃ n : ℕ,
      ((IsIntegralPerfectStratumPiece T d).shiftClosure ℤ).extensionProductIter n K := by
  classical
  obtain ⟨s, hs⟩ := hK
  obtain ⟨n, V, hV, hV0, hVn, Z, i, hi, hg⟩ := geometric_filtration T s
  let P := (IsIntegralPerfectStratumPiece T d).shiftClosure ℤ
  let J (k : Fin (n + 1)) := cbcDerivedOpenShriek d (V k).ι inferInstance
  let L (k : Fin (n + 1)) := (d.pull (V k).ι).obj K
  have hL (k : Fin (n + 1)) : P.extensionProductIter k.val ((J k).obj (L k)) := by
    induction k using Fin.induction with
    | zero =>
      let hempty : IsEmpty (V 0).toScheme := by
        constructor
        intro x
        have he : (V 0 : Set T) = ∅ :=
          congrArg (fun U : T.Opens ↦ (U : Set T)) hV0
        exact ((Set.ext_iff.mp he) x.val).mp x.property
      have hz := empty_derived_zero (V 0).toScheme d (L 0)
      have hz' : IsZero ((J 0).obj (L 0)) := by
        change IsZero ((cbcOpenShriek d (V 0).ι inferInstance).mapDerivedCategory.obj _)
        exact Functor.map_isZero _ hz
      exact ObjectProperty.le_shiftClosure (A := ℤ) _ _ (zero_piece T d _ hz')
    | succ k ih =>
      let hic : IsClosedImmersion (i k) := (hi k).1
      let hr : IsReduced (Z k) := (hi k).2.1
      let j := T.homOfLE (hV (Fin.castSucc_le_succ k))
      let hj : IsOpenImmersion j := inferInstanceAs
        (IsOpenImmersion (T.homOfLE (hV (Fin.castSucc_le_succ k))))
      let W : (V k.succ).toScheme.ProEt := ProEt.mk j
      let hj' : IsOpenImmersion W.hom := hj
      have : TopologicalSpace.NoetherianSpace (V k.castSucc).toScheme :=
        (V k.castSucc).ι.isEmbedding.isInducing.noetherianSpace
      let hqc : QuasiCompact W.hom := by
        change QuasiCompact j
        exact quasiCompact_of_noetherianSpace_source j
      have hjcomp : j ≫ (V k.succ).ι = (V k.castSucc).ι := T.homOfLE_ι _
      have hW : Set.range W.hom = (Set.range (i k))ᶜ := by
        rw [(hi k).2.2]
        ext x
        change (∃ w, j w = x) ↔ ¬¬((V k.succ).ι x ∈ V k.castSucc)
        rw [not_not]
        constructor
        · rintro ⟨w, rfl⟩
          change (j ≫ (V k.succ).ι) w ∈ V k.castSucc
          rw [hjcomp]
          exact w.property
        · intro hx
          refine ⟨⟨x.val, hx⟩, ?_⟩
          apply (V k.succ).ι.isEmbedding.injective
          change (j ≫ (V k.succ).ι) _ = (V k.succ).ι x
          rw [hjcomp]
          rfl
      obtain ⟨f, g, h, hΔ⟩ := derived_localization d (i k) W hW (L k.succ)
      let F := J k.succ
      have htri := (cbcOpenShriek d (V k.succ).ι inferInstance).mapDerivedCategory
        |>.map_distinguished _ hΔ
      let a : F.obj ((cbcDerivedOpenShriek d j hj).obj
          ((d.pull j).obj (L k.succ))) ≅ (J k.castSucc).obj (L k.castSucc) :=
        (cbcJComp d j (V k.succ).ι).app _ ≪≫
          (cbcJCongr d hjcomp).app _ ≪≫
          (J k.castSucc).mapIso
            (((d.pullComp j (V k.succ).ι).app K).symm ≪≫
              eqToIso (congrArg (fun v ↦ (d.pull v).obj K) hjcomp))
      have hfirst : P.extensionProductIter k.val
          (F.obj ((cbcDerivedOpenShriek d j hj).obj ((d.pull j).obj (L k.succ)))) :=
        iter_of_iso P k.val a.symm ih
      obtain ⟨a₀, v, hv⟩ := hg k
      have hlocal := locallyPerfect_on_stratum d K b s a₀
        (i k ≫ (V k.succ).ι) v hv (hs a₀)
      have hlocal' : IsIntegralLocallyPerfect (Z k) d
          ((d.pull (i k)).obj (L k.succ)) :=
        locallyPerfect_of_iso d ((d.pullComp (i k) (V k.succ).ι).app K) hlocal
      have hthird : P (F.obj ((d.push (i k)).obj ((d.pull (i k)).obj (L k.succ)))) :=
        ObjectProperty.le_shiftClosure (A := ℤ) _ _
          ⟨(V k.succ).toScheme, Z k, (V k.succ).ι, inferInstance, i k, hic,
            (d.pull (i k)).obj (L k.succ), hlocal', ⟨Iso.refl _⟩⟩
      change P.extensionProductIter (k.val + 1) _
      rw [ObjectProperty.extensionProductIter_succ']
      exact ⟨_, _, _, _, _, htri, hfirst, hthird⟩
  let ht : IsIso (V (Fin.last n)).ι := by
    rw [hVn]
    exact inferInstanceAs (IsIso T.topIso.hom)
  let hp := pull_iso_equivalence d (V (Fin.last n)).ι
  have : IsIso (cbcDerivedOpenAdjunction d (V (Fin.last n)).ι).counit :=
    (cbcDerivedOpenAdjunction d (V (Fin.last n)).ι).counit_isIso_of_R_fully_faithful
  exact ⟨n, iter_of_iso P n
    (asIso ((cbcDerivedOpenAdjunction d (V (Fin.last n)).ι).counit.app K))
    (hL (Fin.last n))⟩

end AlgebraicGeometry.Scheme
