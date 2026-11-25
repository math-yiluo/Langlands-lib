/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAbelian
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.IdealModuleProductExactCalculus
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentFormalShortExactLevels
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.AlgebraicGeometry.FormalModuleSupportConstant

/-!
# Serre subcategories of coherent formal modules with proper support

Source: Stacks Project, Cohomology of Schemes, Lemma 0CYV
(blueprint: lem-weil-pbc-formal-systems-proper-support-serre).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false in
private theorem support_mono {X : Scheme.{u}} {M N : X.Modules}
    (a : M ⟶ N) [Mono a] :
    {x : X | ¬ Subsingleton (M.presheaf.stalk x)} ⊆
      {x : X | ¬ Subsingleton (N.presheaf.stalk x)} := by
  intro x hx hN
  have hm : Mono ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map a) := by
    apply (RingedSpace.module_stalk_exact X.toRingedSpace a).1
    intro U
    have : Mono a.val := (SheafOfModules.forget _).map_mono a
    exact (ModuleCat.mono_iff_injective (a.val.app (op U))).mp inferInstance
  have : Subsingleton ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj N) := hN
  exact hx (Function.Injective.subsingleton
    ((ModuleCat.mono_iff_injective _).mp hm))

set_option backward.isDefEq.respectTransparency false in
private theorem support_epi {X : Scheme.{u}} {M N : X.Modules}
    (a : M ⟶ N) [Epi a] :
    {x : X | ¬ Subsingleton (N.presheaf.stalk x)} ⊆
      {x : X | ¬ Subsingleton (M.presheaf.stalk x)} := by
  intro x hx hM
  let T := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  have hs : Function.Surjective (T.map a).hom := by
    intro z
    obtain ⟨U, hxU, z, rfl⟩ := N.presheaf.exists_germ_eq z
    obtain ⟨ι, V, hV, s, hcover, hs⟩ :=
      ((RingedSpace.module_exactness_local_lifting X.toRingedSpace).2.1 M N a).2.mpr
        inferInstance U z
    have hxV : x ∈ ⨆ i, V i := by rw [hcover]; exact hxU
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxV
    refine ⟨M.presheaf.germ (V i) x hi (s i), ?_⟩
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((PresheafOfModules.toPresheaf _).map a.val) _ = _
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change N.presheaf.germ (V i) x hi (a.val.app (op (V i)) (s i)) = _
    rw [hs i]
    erw [N.presheaf.germ_res_apply]
  have : Subsingleton (T.obj M) := hM
  exact hx (Function.Surjective.subsingleton hs)

set_option backward.isDefEq.respectTransparency false in
private theorem support_shortExact {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (T : ShortComplex (CoherentFormalModule X I))
    (hT : T.ShortExact) :
    {x : X | ¬ Subsingleton ((T.X₂.obj.obj (op 0)).presheaf.stalk x)} =
      {x : X | ¬ Subsingleton ((T.X₁.obj.obj (op 0)).presheaf.stalk x)} ∪
      {x : X | ¬ Subsingleton ((T.X₃.obj.obj (op 0)).presheaf.stalk x)} := by
  classical
  obtain ⟨hlevel, hkernel⟩ := coherentFormalModule_shortExact_levels X I T hT
  have hleft :
      {x : X | ¬ Subsingleton ((T.X₁.obj.obj (op 0)).presheaf.stalk x)} ⊆
        {x : X | ¬ Subsingleton ((T.X₂.obj.obj (op 0)).presheaf.stalk x)} := by
    obtain ⟨m, _, q, hq⟩ := hkernel 0
    have := hq
    exact (support_epi q).trans ((support_mono (kernel.ι (T.g.hom.app (op m)))).trans
      (formalModule_support_eq I T.X₂ m).subset)
  have : Epi (T.g.hom.app (op 0)) := (hlevel 0).2
  apply Set.Subset.antisymm
  · intro x hx
    by_contra h
    have hz : Subsingleton ((T.X₁.obj.obj (op 0)).presheaf.stalk x) ∧
        Subsingleton ((T.X₃.obj.obj (op 0)).presheaf.stalk x) := by
      simpa only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] using h
    have h₁ := hz.1
    have h₃ := hz.2
    let U := T.map ((IsCoherentFormalModule I).ι ⋙
      (evaluation ℕᵒᵖ X.Modules).obj (op 0))
    have : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).PreservesZeroMorphisms :=
      RingedSpace.moduleStalkFunctor_preservesZeroMorphisms_proof X.toRingedSpace x
    have he : (U.map (RingedSpace.moduleStalkFunctor X.toRingedSpace x)).Exact :=
      (RingedSpace.module_stalk_exact X.toRingedSpace U.f).2.2.2.2 _ U.f U.g U.zero
        |>.mp (hlevel 0).1 x
    have : Subsingleton (U.map (RingedSpace.moduleStalkFunctor X.toRingedSpace x)).X₁ := h₁
    have : Subsingleton (U.map (RingedSpace.moduleStalkFunctor X.toRingedSpace x)).X₃ := h₃
    exact hx (ModuleCat.subsingleton_of_isZero
      (he.isZero_of_both_isZero (ModuleCat.isZero_of_subsingleton _)
        (ModuleCat.isZero_of_subsingleton _)))
  · exact Set.union_subset hleft (support_epi (T.g.hom.app (op 0)))

private theorem support_shortExact_anyZero {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (z : HasZeroMorphisms (CoherentFormalModule X I))
    (T : @ShortComplex (CoherentFormalModule X I) _ z) (hT : T.ShortExact) :
    {x : X | ¬ Subsingleton ((T.X₂.obj.obj (op 0)).presheaf.stalk x)} =
      {x : X | ¬ Subsingleton ((T.X₁.obj.obj (op 0)).presheaf.stalk x)} ∪
      {x : X | ¬ Subsingleton ((T.X₃.obj.obj (op 0)).presheaf.stalk x)} := by
  have hz : z = ObjectProperty.instHasZeroMorphismsFullSubcategory
      (IsCoherentFormalModule I) := Subsingleton.elim _ _
  subst z
  exact support_shortExact I T hT

private theorem shortExact_levels_anyZero {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (z : HasZeroMorphisms (CoherentFormalModule X I))
    (T : @ShortComplex (CoherentFormalModule X I) _ z) (hT : T.ShortExact) :
    (∀ n : ℕ, ∃ w : T.f.hom.app (op n) ≫ T.g.hom.app (op n) = 0,
      (ShortComplex.mk (T.f.hom.app (op n)) (T.g.hom.app (op n)) w).Exact ∧
        Epi (T.g.hom.app (op n))) ∧
    (∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧
      ∃ q : kernel (T.g.hom.app (op m)) ⟶ T.X₁.obj.obj (op n), Epi q) := by
  have hz : z = ObjectProperty.instHasZeroMorphismsFullSubcategory
      (IsCoherentFormalModule I) := Subsingleton.elim _ _
  subst z
  obtain ⟨hlevel, hkernel⟩ := coherentFormalModule_shortExact_levels X I T hT
  refine ⟨?_, hkernel⟩
  intro n
  let U := T.map ((IsCoherentFormalModule I).ι ⋙
    (evaluation ℕᵒᵖ X.Modules).obj (op n))
  exact ⟨U.zero, (hlevel n).1, (hlevel n).2⟩

private theorem serre_of_shortExact_iff {C : Type*} [Category* C] [Abelian C]
    (P : ObjectProperty C) (hzero : P 0)
    (hP : ∀ (T : ShortComplex C), T.ShortExact → (P T.X₂ ↔ P T.X₁ ∧ P T.X₃)) :
    P.IsSerreClass where
  exists_zero := ⟨0, isZero_zero C, hzero⟩
  prop_of_mono {A B} a _ hB := by
    have h : (ShortComplex.cokernelSequence a).ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact a
        mono_f := by change Mono a; infer_instance
        epi_g := inferInstance }
    exact ((hP _ h).mp hB).1
  prop_of_epi {A B} a _ hA := by
    have h : (ShortComplex.kernelSequence a).ShortExact :=
      { exact := ShortComplex.kernelSequence_exact a
        mono_f := inferInstance
        epi_g := by change Epi a; infer_instance }
    exact ((hP _ h).mp hA).2
  prop_X₂_of_shortExact {T} hT h₁ h₃ := (hP T hT).mpr ⟨h₁, h₃⟩

private theorem proper_union {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (A B : TopologicalSpace.Closeds X) (hA : Scheme.IsClosedSubsetProperOver f A)
    (hB : Scheme.IsClosedSubsetProperOver f B) :
    Scheme.IsClosedSubsetProperOver f (A ⊔ B) := by
  have h := (Scheme.isClosedSubsetProperOver_union_preimage f).1 2
    (fun i ↦ if i = 0 then A else B) (by
      intro i
      split_ifs <;> assumption)
  have he : (⨆ i : Fin 2, if i = 0 then A else B) = A ⊔ B := by
    apply le_antisymm
    · apply iSup_le
      intro i
      split_ifs
      · exact le_sup_left
      · exact le_sup_right
    · refine sup_le ?_ ?_
      · simpa using (le_iSup (fun i : Fin 2 ↦ if i = 0 then A else B) 0)
      · simpa using (le_iSup (fun i : Fin 2 ↦ if i = 0 then A else B) 1)
  rwa [he] at h

private theorem level_support_closed {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (M : CoherentFormalModule X I) :
    IsClosed {x : X | ¬ Subsingleton ((M.obj.obj (op 0)).presheaf.stalk x)} := by
  have hc := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
    (M.property.1 0)
  have := hc.1
  have := hc.2
  exact (Scheme.Modules.finite_type_module_support_closed X _).2.2.2

private theorem level_isZero {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) [Abelian (CoherentFormalModule X I)] (n : ℕ) :
    IsZero ((0 : CoherentFormalModule X I).obj.obj (op n)) := by
  let E := (IsCoherentFormalModule I).ι ⋙ (evaluation ℕᵒᵖ X.Modules).obj (op n)
  exact E.map_isZero (isZero_zero _)

private theorem ideal_product_isZero {X : Scheme.{u}} (J : X.IdealSheafData)
    (F : X.Modules) (hF : IsZero F) : IsZero (Scheme.idealModuleProduct J.toModulesι F) := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  have : Mono (Scheme.idealModuleProductι J.toModulesι F) := by
    dsimp [Scheme.idealModuleProductι]
    infer_instance
  exact IsZero.of_mono (Scheme.idealModuleProductι J.toModulesι F) hF

-- The original quantified instance binder is used implicitly in the statement.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two full subcategories of coherent formal modules in Lemma 0CYV are Serre
subcategories.  The proof uses the support and annihilator calculations from the
node proof, together with abelianity of `CoherentFormalModule`.
Source: Stacks Project, Cohomology of Schemes, Lemma 0CYV.
(blueprint: lem-weil-pbc-formal-systems-proper-support-serre).
Proof: supports in a short exact sequence are the union of the outer supports;
proper closed subsets and finite unions remain proper.  For the second class,
annihilators pass to subobjects and quotients, while extensions are annihilated
by the product ideal and the corresponding scheme-theoretic union. -/
theorem formalSystems_properSupport_serre
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f]
    (I : X.IdealSheafData) :
    Nonempty (Abelian (@CoherentFormalModule X (isNoetherian_of_locallyOfFiniteType f) I)) ∧
    ∀ [Ab : Abelian (@CoherentFormalModule X (isNoetherian_of_locallyOfFiniteType f) I)],
      ObjectProperty.IsSerreClass
        (fun M : @CoherentFormalModule X (isNoetherian_of_locallyOfFiniteType f) I ↦
          Scheme.Modules.HasSupportProperOver f (M.obj.obj (op 0))) ∧
      ObjectProperty.IsSerreClass
        (fun M : @CoherentFormalModule X (isNoetherian_of_locallyOfFiniteType f) I ↦
          ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (_ : IsClosedImmersion i),
            IsProper (i ≫ f) ∧
            ∀ n : ℕ, IsZero (Scheme.idealModuleProduct i.ker.toModulesι
              (M.obj.obj (op n)))) := by
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  refine ⟨(coherentFormalModule_abelian X I).1, ?_⟩
  intro Ab
  let C := CoherentFormalModule X I
  let : HasZeroMorphisms C :=
    @Preadditive.preadditiveHasZeroMorphisms C _ Ab.toPreadditive
  let supp (M : C) : TopologicalSpace.Closeds X :=
    ⟨{x : X | ¬ Subsingleton ((M.obj.obj (op 0)).presheaf.stalk x)},
      level_support_closed I M⟩
  have supp_eq (T : @ShortComplex C _
      (@Preadditive.preadditiveHasZeroMorphisms C _ Ab.toPreadditive))
      (hT : T.ShortExact) :
      supp T.X₂ = supp T.X₁ ⊔ supp T.X₃ :=
    TopologicalSpace.Closeds.ext (support_shortExact_anyZero I _ T hT)
  have hbot : Scheme.IsClosedSubsetProperOver f ⊥ := by
    apply (Scheme.closed_subset_proper_over_base_properties f ⊥).1.mpr
    refine ⟨⊥_ Scheme, initial.to X, inferInstance, ?_, inferInstance⟩
    ext x
    simp
  have hz : supp (0 : C) = ⊥ := by
    apply TopologicalSpace.Closeds.ext
    ext x
    have : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).PreservesZeroMorphisms :=
      RingedSpace.moduleStalkFunctor_preservesZeroMorphisms_proof X.toRingedSpace x
    have hh := (RingedSpace.moduleStalkFunctor X.toRingedSpace x).map_isZero
      (level_isZero I 0)
    have hn := ModuleCat.subsingleton_of_isZero hh
    have hn' : Subsingleton (((0 : C).obj.obj (op 0)).presheaf.stalk x) := hn
    simp [supp, hn']
  constructor
  · apply serre_of_shortExact_iff
    · exact ⟨supp 0, rfl, hz ▸ hbot⟩
    · intro T hT
      have characterize (M : C) :
          Scheme.Modules.HasSupportProperOver f (M.obj.obj (op 0)) ↔
            Scheme.IsClosedSubsetProperOver f (supp M) := by
        constructor
        · rintro ⟨Z, hZ, hp⟩
          have he : Z = supp M := TopologicalSpace.Closeds.ext hZ
          rwa [← he]
        · intro hp
          exact ⟨supp M, rfl, hp⟩
      rw [characterize, characterize, characterize, supp_eq T hT]
      constructor
      · intro hp
        exact ⟨(Scheme.closed_subset_proper_over_base_properties f _).2.2.1
            _ le_sup_left hp,
          (Scheme.closed_subset_proper_over_base_properties f _).2.2.1
            _ le_sup_right hp⟩
      · rintro ⟨h₁, h₃⟩
        exact proper_union f _ _ h₁ h₃
  · apply serre_of_shortExact_iff
    · refine ⟨⊥_ Scheme, initial.to X, inferInstance, inferInstance, ?_⟩
      intro n
      exact ideal_product_isZero _ _ (level_isZero I n)
    · intro T hT
      obtain ⟨hlevel, hkernel⟩ := shortExact_levels_anyZero I _ T hT
      constructor
      · rintro ⟨Z, i, hi, hp, ha⟩
        have sub (n : ℕ) :
            IsZero (Scheme.idealModuleProduct i.ker.toModulesι (T.X₁.obj.obj (op n))) := by
          obtain ⟨m, _, q, hq⟩ := hkernel n
          have := hq
          exact (Scheme.idealModuleProduct_exact_calculus X).2.1 i.ker q
            ((Scheme.idealModuleProduct_exact_calculus X).1 i.ker
              (kernel.ι (T.g.hom.app (op m))) (ha m))
        have quot (n : ℕ) :
            IsZero (Scheme.idealModuleProduct i.ker.toModulesι (T.X₃.obj.obj (op n))) := by
          obtain ⟨_, _, hepi⟩ := hlevel n
          have := hepi
          exact (Scheme.idealModuleProduct_exact_calculus X).2.1 i.ker
            (T.g.hom.app (op n)) (ha n)
        exact ⟨⟨Z, i, hi, hp, sub⟩, ⟨Z, i, hi, hp, quot⟩⟩
      · rintro ⟨⟨Z, i, hi, hp, ha⟩, ⟨Y, j, hj, hq, hb⟩⟩
        let K := i.ker * j.ker
        have hproper (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
            (hp : IsProper (i ≫ f)) : Scheme.IsClosedSubsetProperOver f i.ker.support := by
          apply (Scheme.closed_subset_proper_over_base_properties f _).1.mpr
          refine ⟨Z, i, inferInstance, ?_, hp⟩
          rw [i.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
        have hpK : Scheme.IsClosedSubsetProperOver f K.support := by
          dsimp only [K]
          rw [Scheme.IdealSheafData.support_mul]
          exact proper_union f _ _ (hproper Z i hp) (hproper Y j hq)
        have hW : IsProper (K.subschemeι ≫ f) :=
          (Scheme.closed_subset_proper_over_base_properties f K.support).2.1.mp hpK
            K.subscheme K.subschemeι (by simp)
        refine ⟨K.subscheme, K.subschemeι, inferInstance, hW, ?_⟩
        intro n
        rw [Scheme.IdealSheafData.ker_subschemeι]
        obtain ⟨w, hexact, _⟩ := hlevel n
        exact (Scheme.idealModuleProduct_exact_calculus X).2.2 i.ker j.ker
          (ShortComplex.mk (T.f.hom.app (op n)) (T.g.hom.app (op n)) w)
          hexact (ha n) (hb n)

end

end AlgebraicGeometry
