/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.LeftExactHomologyEdge
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology

/-! # The derived counit for acyclic cohomology

Source: Stacks, Cohomology on Sites, Tags 0D7S and 0D7U; Homology, Tag 0117.
(blueprint: lem-fd-acyclic-cohomology-derived-counit).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
noncomputable section
universe a b av bv
variable {C : Type a} {D : Type b} [Category.{av} C] [Category.{bv} D]
  [Abelian C] [Abelian D] [EnoughInjectives C]

private theorem acyclic_extension (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    {S : ShortComplex C} (hS : S.ShortExact)
    (h₁ : F.rightAcyclic S.X₁) (h₃ : F.rightAcyclic S.X₃) : F.rightAcyclic S.X₂ := by
  obtain ⟨δ, hm, he⟩ := hS.exists_rightDerived_full_long_exact F
  intro n
  exact ((he (n + 1)).1.isZero_X₂_iff).mpr
    ⟨(h₁ n).eq_of_src _ _, (h₃ n).eq_of_tgt _ _⟩

private theorem cycles_acyclic (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex C ℤ) (a : ℤ) [K.IsStrictlyGE a]
    (hK : ∀ n, F.rightAcyclic (K.X n))
    (hH : ∀ n, F.rightAcyclic (K.homology n)) :
    ∀ n, F.rightAcyclic (K.cycles n) := by
  intro n
  obtain hn | hn := lt_or_ge n a
  · exact F.rightAcyclic.prop_of_isZero
      (IsZero.of_mono (K.iCycles n) (K.isZero_of_isStrictlyGE a n hn))
  · induction n, hn using Int.leInduction with
    | base =>
      have hz : K.d (a - 1) a = 0 :=
        (K.isZero_of_isStrictlyGE a (a - 1) (by omega)).eq_of_src _ _
      exact F.rightAcyclic.prop_of_iso (K.isoHomologyπ (a - 1) a (by simp) hz).symm (hH a)
    | succ n hn ih =>
      let t := K.toCycles n (n + 1)
      have ht : K.iCycles n ≫ t = 0 := by
        apply (cancel_mono (K.iCycles (n + 1))).mp
        simp [t, HomologicalComplex.iCycles_d]
      have w₁ : K.iCycles n ≫ factorThruImage t = 0 := by
        apply (cancel_mono (image.ι t)).mp
        simpa using ht
      let S₁ := ShortComplex.mk (K.iCycles n) (factorThruImage t) w₁
      let S₀ := ShortComplex.mk (K.iCycles n) (K.d n (n + 1)) (K.iCycles_d n (n + 1))
      let φ : S₁ ⟶ S₀ :=
        { τ₁ := 𝟙 _
          τ₂ := 𝟙 _
          τ₃ := image.ι t ≫ K.iCycles (n + 1)
          comm₂₃ := by simp [S₁, S₀, t] }
      have hS₀ : S₀.Exact :=
        ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel n (n + 1) (by simp))
      have hS₁ : S₁.ShortExact :=
        { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hS₀ }
      have hB : F.rightAcyclic (image t) := hS₁.rightAcyclic_X₃ ih (hK n)
      have wt : t ≫ K.homologyπ (n + 1) = 0 := K.toCycles_comp_homologyπ n (n + 1)
      have w₂ : image.ι t ≫ K.homologyπ (n + 1) = 0 := by
        apply (cancel_epi (factorThruImage t)).mp
        simpa using wt
      let S₂ := ShortComplex.mk (image.ι t) (K.homologyπ (n + 1)) w₂
      let S₃ := ShortComplex.mk t (K.homologyπ (n + 1)) wt
      let ψ : S₃ ⟶ S₂ :=
        { τ₁ := factorThruImage t
          τ₂ := 𝟙 _
          τ₃ := 𝟙 _
          comm₁₂ := by simp [S₃, S₂] }
      have hS₃ : S₃.Exact :=
        ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel n (n + 1) (by simp))
      have hS₂ : S₂.ShortExact :=
        { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).mp hS₃ }
      exact acyclic_extension F hS₂ hB (hH (n + 1))
private theorem preserves_homology (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex C ℤ)
    (hK : ∀ n, F.rightAcyclic (K.X n))
    (hZ : ∀ n, F.rightAcyclic (K.cycles n)) (n : ℤ) :
    F.PreservesLeftHomologyOf (K.sc n) := by
  let j := n
  let i := (ComplexShape.up ℤ).prev n
  let t := K.toCycles i j
  have ht : K.iCycles i ≫ t = 0 := by
    apply (cancel_mono (K.iCycles j)).mp
    simp [t, HomologicalComplex.iCycles_d]
  have w₁ : K.iCycles i ≫ factorThruImage t = 0 := by
    apply (cancel_mono (image.ι t)).mp
    simpa using ht
  let S₁ := ShortComplex.mk (K.iCycles i) (factorThruImage t) w₁
  let S₀ := ShortComplex.mk (K.iCycles i) (K.d i j) (K.iCycles_d i j)
  let φ : S₁ ⟶ S₀ :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := image.ι t ≫ K.iCycles j
      comm₂₃ := by simp [S₁, S₀, t] }
  have hS₀ : S₀.Exact :=
    ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel i j (by dsimp [i, j]; simp))
  have hS₁ : S₁.ShortExact :=
    { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hS₀ }
  have hB : F.rightAcyclic (image t) := hS₁.rightAcyclic_X₃ (hZ i) (hK i)
  have wt : t ≫ K.homologyπ j = 0 := K.toCycles_comp_homologyπ i j
  have w₂ : image.ι t ≫ K.homologyπ j = 0 := by
    apply (cancel_epi (factorThruImage t)).mp
    simpa using wt
  let S₂ := ShortComplex.mk (image.ι t) (K.homologyπ j) w₂
  let S₃ := ShortComplex.mk t (K.homologyπ j) wt
  let ψ : S₃ ⟶ S₂ :=
    { τ₁ := factorThruImage t
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S₃, S₂] }
  have hS₃ : S₃.Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel i j (by rfl))
  have hS₂ : S₂.ShortExact :=
    { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).mp hS₃ }
  let φ' := F.mapShortComplex.map ψ
  have : Epi φ'.τ₁ := by
    change Epi (F.map (factorThruImage t))
    exact (hS₁.map_of_rightAcyclic (hZ i)).epi_g
  have : IsIso φ'.τ₂ := by
    change IsIso (F.map (𝟙 _))
    infer_instance
  have : Mono φ'.τ₃ := by
    change Mono (F.map (𝟙 _))
    infer_instance
  have he : (S₃.map F).Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ').mpr
      (hS₂.map_of_rightAcyclic hB).exact
  have : Epi (F.map (K.homologyπ j)) :=
    (hS₂.map_of_rightAcyclic hB).epi_g
  have : Epi (S₃.map F).g := inferInstanceAs (Epi (F.map (K.homologyπ j)))
  have hπ := he.gIsCokernel
  have : PreservesColimit (parallelPair t 0) F :=
    preservesColimit_of_preserves_colimit_cocone
      (K.homologyIsCokernel i j (by rfl))
      ((isColimitMapCoconeCoforkEquiv' F wt).symm hπ)
  have : (K.sc n).leftHomologyData.IsPreservedBy F :=
    { g := inferInstance
      f' := by
        change PreservesColimit (parallelPair t 0) F
        infer_instance }
  exact CategoryTheory.Functor.PreservesLeftHomologyOf.mk' F (K.sc n).leftHomologyData
omit [EnoughInjectives C] in
private theorem map_homologyπ (F : C ⥤ D) [F.Additive] (S : ShortComplex C)
    [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let h := S.leftHomologyData
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  change ((h.map F).cyclesIso.hom ≫ F.map h.π) ≫ F.map h.homologyIso.inv =
    ((h.map F).cyclesIso.hom ≫ F.map h.cyclesIso.inv) ≫ F.map S.homologyπ
  rw [Category.assoc, ← F.map_comp,
    ShortComplex.LeftHomologyData.π_comp_homologyIso_inv, F.map_comp, Category.assoc]



private theorem acyclic_edge (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex C ℤ) (a : ℤ) [K.IsStrictlyGE a]
    (hK : ∀ n, F.rightAcyclic (K.X n))
    (hH : ∀ n, F.rightAcyclic (K.homology n)) (n : ℤ) :
    IsIso (ShortComplex.leftExactHomologyEdge F (K.sc n)) := by
  have : F.PreservesLeftHomologyOf (K.sc n) :=
    preserves_homology F K hK (cycles_acyclic F K a hK hH) n
  let S := K.sc n
  have hc : (ShortComplex.leftExactCyclesIso F S).inv = (S.mapCyclesIso F).hom := by
    apply (cancel_mono (F.map S.iCycles)).mp
    rw [ShortComplex.leftExactCyclesIso_inv_i, ShortComplex.mapCyclesIso_hom_iCycles]
  have he : ShortComplex.leftExactHomologyEdge F S = (S.mapHomologyIso F).hom := by
    apply (cancel_epi (S.map F).homologyπ).mp
    rw [ShortComplex.homologyπ_leftExactHomologyEdge, hc, map_homologyπ]
  change IsIso (ShortComplex.leftExactHomologyEdge F S)
  rw [he]
  infer_instance
omit [EnoughInjectives C] in
private theorem short_edge_mate (F : C ⥤ D) (R : D ⥤ C) [F.Additive] [R.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [PreservesFiniteLimits R]
    (adj : F ⊣ R) (S : ShortComplex D) :
    let εS : (S.map R).map F ⟶ S :=
      { τ₁ := adj.counit.app S.X₁
        τ₂ := adj.counit.app S.X₂
        τ₃ := adj.counit.app S.X₃
        comm₁₂ := (adj.counit.naturality S.f).symm
        comm₂₃ := (adj.counit.naturality S.g).symm }
    ShortComplex.leftExactHomologyEdge R S =
      adj.homEquiv _ _ (((S.map R).mapHomologyIso F).inv ≫ ShortComplex.homologyMap εS) := by
  intro εS
  let T := S.map R
  let e := ShortComplex.leftExactCyclesIso R S
  have hc : (T.mapCyclesIso F).inv ≫ ShortComplex.cyclesMap εS =
      F.map e.inv ≫ adj.counit.app S.cycles := by
    apply (cancel_mono S.iCycles).mp
    rw [Category.assoc, ShortComplex.cyclesMap_i]
    change (T.mapCyclesIso F).inv ≫ (T.map F).iCycles ≫ adj.counit.app S.X₂ = _
    rw [← Category.assoc, ← ShortComplex.mapCyclesIso_hom_iCycles,
      Iso.inv_hom_id_assoc]
    rw [Category.assoc]
    change F.map T.iCycles ≫ adj.counit.app S.X₂ =
      F.map e.inv ≫ adj.counit.app S.cycles ≫ S.iCycles
    have hn : F.map (R.map S.iCycles) ≫ adj.counit.app S.X₂ =
        adj.counit.app S.cycles ≫ S.iCycles := adj.counit.naturality S.iCycles
    rw [← hn, ← Category.assoc, ← F.map_comp]
    exact congrArg (fun f => F.map f ≫ adj.counit.app S.X₂)
      (ShortComplex.leftExactCyclesIso_inv_i R S).symm
  apply (cancel_epi T.homologyπ).mp
  rw [ShortComplex.homologyπ_leftExactHomologyEdge,
    ← adj.homEquiv_naturality_left]
  have hm := map_homologyπ F T
  have hm' : F.map T.homologyπ ≫ (T.mapHomologyIso F).inv =
      (T.mapCyclesIso F).inv ≫ (T.map F).homologyπ := by
    apply (cancel_mono (T.mapHomologyIso F).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hm, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hm', Category.assoc, ShortComplex.homologyπ_naturality,
    ← Category.assoc, hc, Category.assoc,
    adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  rw [← adj.homEquiv_symm_id, Equiv.apply_symm_apply, Category.id_comp]

omit [EnoughInjectives C] in
private theorem injective_counit [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
    (F : C ⥤ D) (R : D ⥤ C) [F.Additive] [R.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [PreservesFiniteLimits R]
    (adj : F ⊣ R) (I : CochainComplex.Plus D) [∀ n, Injective (I.obj.X n)]
    (hε : ∀ q, IsIso (adj.counit.app (I.obj.homology q)))
    (hedge : ∀ q, IsIso (ShortComplex.leftExactHomologyEdge R (I.obj.sc q))) :
    IsIso (adj.derivedPlus.counit.app (DerivedCategory.Plus.Q.obj I)) := by
  let ε := (adj.mapHomologicalComplex (.up ℤ)).counit.app I.obj
  have hq (q : ℤ) : IsIso (HomologicalComplex.homologyMap ε q) := by
    let S := I.obj.sc q
    let εS : (S.map R).map F ⟶ S :=
      { τ₁ := adj.counit.app S.X₁
        τ₂ := adj.counit.app S.X₂
        τ₃ := adj.counit.app S.X₃
        comm₁₂ := (adj.counit.naturality S.f).symm
        comm₂₃ := (adj.counit.naturality S.g).symm }
    have hh := congrArg (adj.homEquiv _ _).symm (short_edge_mate F R adj S)
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_symm_apply] at hh
    have : IsIso (adj.counit.app S.homology) := hε q
    have : IsIso (ShortComplex.leftExactHomologyEdge R S) := hedge q
    have : IsIso (((S.map R).mapHomologyIso F).inv ≫ ShortComplex.homologyMap εS) := by
      rw [← hh]
      infer_instance
    have : IsIso (ShortComplex.homologyMap εS) :=
      IsIso.of_isIso_comp_left ((S.map R).mapHomologyIso F).inv _
    change IsIso (ShortComplex.homologyMap εS)
    infer_instance
  have hεq : QuasiIso ε := by
    rw [quasiIso_iff]
    intro q
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact hq q
  let K := (HomotopyCategory.Plus.quotient D).obj I
  have hmem : (HomotopyCategory.Plus.quasiIso D)
      (adj.mapHomotopyCategoryPlus.counit.app K) := by
    change (HomotopyCategory.quasiIso D (.up ℤ))
      ((HomotopyCategory.Plus.ι D).map (adj.mapHomotopyCategoryPlus.counit.app K))
    rw [Adjunction.ι_map_mapHomotopyCategoryPlus_counit_app]
    change (HomotopyCategory.quasiIso D (.up ℤ))
      ((adj.mapHomotopyCategory (.up ℤ)).counit.app
        ((HomotopyCategory.quotient D _).obj I.obj))
    rw [Adjunction.mapHomotopyCategory_counit_app_quotient]
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr hεq
  have : IsIso (DerivedCategory.Plus.Qh.map
      (adj.mapHomotopyCategoryPlus.counit.app K)) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D) _ hmem
  have : IsIso (R.rightDerivedFunctorPlusUnith.app K) := inferInstance
  have : IsIso (F.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnith.app K) ≫
      adj.derivedPlus.counit.app (DerivedCategory.Plus.Qh.obj K)) := by
    rw [adj.derivedPlus_counit_app_fac]
    infer_instance
  have : IsIso (adj.derivedPlus.counit.app (DerivedCategory.Plus.Qh.obj K)) :=
    IsIso.of_isIso_comp_left
      (F.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnith.app K)) _
  exact (NatTrans.isIso_app_iff_of_iso adj.derivedPlus.counit
    ((DerivedCategory.Plus.quotientCompQhIso D).app I)).mp this

namespace CategoryTheory.Adjunction

omit [EnoughInjectives C] in
/-- Acyclic cohomology and an invertible ordinary counit give cohomology
isomorphisms for R⁺ and an invertible canonical derived counit.

Source: Stacks, Cohomology on Sites, Tags 0D7S and 0D7U; Homology, Tag 0117.
(blueprint: lem-fd-acyclic-cohomology-derived-counit).

Proof: represent L by a bounded-below complex I of injectives. Starting at its
lower bound, use 0 → ZⁿI → Iⁿ → Bⁿ⁺¹I → 0 and
0 → Bⁿ⁺¹I → Zⁿ⁺¹I → Hⁿ⁺¹I → 0 to prove all cycles and boundaries R-acyclic.
The long exact sequences show these sequences remain exact after R, so R
preserves the relevant homology cokernel. Kernel preservation identifies the
cycles, and the canonical edge Hⁿ(RI) → R(HⁿI) is therefore invertible.
Compose it with the injective-model comparison to obtain the asserted isomorphisms.
To compute the counit, cancel the epimorphism from cycles. Naturality at the
cycle inclusion and quotient identifies the adjoint of the edge with homology
of the termwise counit, after the inverse exact-functor homology comparison.
Thus the termwise counit is a quasi-isomorphism. In the derived counit
factorization on I the exact localization comparison, localization of this
quasi-isomorphism, and right-derived unit on I are invertible. Cancel the
unit and transport to L by naturality. No Grothendieck hypothesis is used. -/
theorem acyclic_cohomology_counit [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
    (F : C ⥤ D) (R : D ⥤ C) [F.Additive] [R.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [PreservesFiniteLimits R]
    (adj : F ⊣ R) (L : DerivedCategory.Plus D)
    (hL : ∀ q, R.rightAcyclic ((DerivedCategory.Plus.homologyFunctor D q).obj L))
    (hε : ∀ q, IsIso (adj.counit.app
      ((DerivedCategory.Plus.homologyFunctor D q).obj L))) :
    (∀ q, Nonempty ((DerivedCategory.Plus.homologyFunctor C q).obj
      (R.rightDerivedFunctorPlus.obj L) ≅
        R.obj ((DerivedCategory.Plus.homologyFunctor D q).obj L))) ∧
      IsIso (adj.derivedPlus.counit.app L) := by
  obtain ⟨K, ⟨eK⟩⟩ : ∃ K : HomotopyCategory.Plus D,
      Nonempty (DerivedCategory.Plus.Qh.obj K ≅ L) :=
    ⟨_, ⟨DerivedCategory.Plus.Qh.objObjPreimageIso L⟩⟩
  obtain ⟨M, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective K
  obtain ⟨a, _⟩ := M.2
  obtain ⟨T, _, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective M a
  let I := (InjectiveObject.ι D).mapCochainComplexPlus.obj T
  have : ∀ n, Injective (I.obj.X n) := fun n => (T.obj.X n).2
  have : IsIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient D).map i)) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr hi)
  let e : DerivedCategory.Plus.Q.obj I ≅ L :=
    ((DerivedCategory.Plus.quotientCompQhIso D).app I).symm ≪≫
      (asIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient D).map i))).symm ≪≫
        eK
  let eH (q : ℤ) : I.obj.homology q ≅
      (DerivedCategory.Plus.homologyFunctor D q).obj L :=
    (DerivedCategory.Plus.homologyFunctorObjQIso I q).symm ≪≫
      (DerivedCategory.Plus.homologyFunctor D q).mapIso e
  have hHI (q : ℤ) : R.rightAcyclic (I.obj.homology q) :=
    R.rightAcyclic.prop_of_iso (eH q).symm (hL q)
  obtain ⟨b, hb⟩ := I.2
  let := hb
  have hedge (q : ℤ) : IsIso (ShortComplex.leftExactHomologyEdge R (I.obj.sc q)) :=
    acyclic_edge R I.obj b (fun n => R.rightAcyclic_of_injective _) hHI q
  have hεI (q : ℤ) : IsIso (adj.counit.app (I.obj.homology q)) :=
    (NatTrans.isIso_app_iff_of_iso adj.counit (eH q)).mpr (hε q)
  refine ⟨fun q => ?_, ?_⟩
  · let := hedge q
    exact ⟨(DerivedCategory.Plus.homologyFunctor C q).mapIso
        (R.rightDerivedFunctorPlus.mapIso e).symm ≪≫
      R.homologyRightDerivedFunctorPlusObjQIsoOfInjective I q ≪≫
      asIso (ShortComplex.leftExactHomologyEdge R (I.obj.sc q)) ≪≫ R.mapIso (eH q)⟩
  · have := injective_counit F R adj I hεI hedge
    exact (NatTrans.isIso_app_iff_of_iso adj.derivedPlus.counit e).mp inferInstance
end CategoryTheory.Adjunction
end
