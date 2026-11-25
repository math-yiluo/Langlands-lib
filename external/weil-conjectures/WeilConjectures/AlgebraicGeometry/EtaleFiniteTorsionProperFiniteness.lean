/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeFibreDimensionBound
import WeilConjectures.AlgebraicGeometry.Proper.ProperTorsionDirectImageBound
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.AlgebraicGeometry.ProperCohomologyGenericLocalConstancy

/-! # Proper finiteness for ordinary finite-field etale module sheaves

Source: Bhatt--Scholze, The pro-etale topology for schemes, Theorem 6.7.1,
proper alternative, with R = A and maximal ideal zero; Stacks Project, Tags 0A3V,
095U and 0GL0 (blueprint: lem-fd-etale-finite-torsion-proper-finiteness).

The higher direct images use the ordinary small etale sites and the bounded below
right derived direct image of a module sheaf placed in degree zero.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

private theorem higherDirectImage_vanishes
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (q : ℤ) (hq : q < 0 ∨ 2 * (d : ℤ) < q) :
    IsZero (higherDirectImage A f q F) := by
  rcases hq with hq | hq
  · exact Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
      (lowerStar (ModuleCat.{u + 1} A) f)
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) 0 hq
  · let U := moduleAbelianForget A Y
    let F₀ := (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj F
    have ht : Scheme.IsTorsionAbelianSheaf F₀ :=
      (Scheme.isTorsionAbelianSheaf_characterizations F₀).1.mpr
        ((Scheme.isTorsionModuleSheaf_iff_isTorsion F).mp inferInstance)
    obtain ⟨e⟩ := nonempty_higherDirectImage_forget_iso A f q F
    have hz : IsZero (U.obj (higherDirectImage A f q F)) :=
      IsZero.of_iso
        (isZero_higherDirectImage_of_isProper_of_fiber_dimension_le f d hd F₀ ht q hq) e
    apply (IsZero.iff_id_eq_zero _).mpr
    apply U.map_injective
    exact (U.map_id _).trans
      (((IsZero.iff_id_eq_zero _).mp hz).trans (U.map_zero _ _).symm)

/-- The generic-stratum argument of Stacks 0GL0, transported by proper base change. -/
private theorem higherDirectImage_generic_stratum
    (ℓ : ℕ) [Fact ℓ.Prime] (A : Type (u + 1)) [Field A] [Finite A] [CharP A ℓ]
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) (q : ℤ) (hq : 0 ≤ q)
    {T : Set Y} (hT : IsClosed T) (hne : T.Nonempty) :
    ∃ O : Set Y, IsOpen O ∧ (T ∩ O).Nonempty ∧
      ∃ (V : Scheme.{u}) (ι : V ⟶ Y), IsImmersion ι ∧ Set.range ι.base = T ∩ O ∧
        Scheme.IsFiniteLocallyConstantSheaf
          ((upperStar (ModuleCat.{u + 1} A) ι).obj (higherDirectImage A f q F)) := by
  have hirrOpen : ∃ O : Set Y, IsOpen O ∧ IsIrreducible (T ∩ O) := by
    have : Nonempty T := hne.to_subtype
    obtain ⟨U₀, -, ⟨x, hx⟩, hU₀⟩ :=
      TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_forall_eq (α := T)
    obtain ⟨N, hN, hxN, hNirr⟩ :=
      TopologicalSpace.NoetherianSpace.exists_isOpen_isPreirreducible x (hU₀ x hx)
    obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 hN
    refine ⟨O, hO, ?_⟩
    rw [← Subtype.image_preimage_coe]
    exact IsIrreducible.image ⟨⟨x, hxN⟩, hNirr⟩ _
      continuous_subtype_val.continuousOn
  obtain ⟨O, hO, hirr⟩ := hirrOpen
  set x := hirr.genericPoint
  have hx := hirr.isGenericPoint_genericPoint_closure
  obtain ⟨p, hp⟩ := hirr.nonempty
  have hxO : x ∈ O := (hx.mem_open_set_iff hO).2 ⟨p, subset_closure hp, hp.2⟩
  have hTO : closure {x} ∩ O = T ∩ O := by
    rw [hx.def]
    refine Set.Subset.antisymm (fun z hz ↦ ?_) (fun z hz ↦ ⟨subset_closure hz, hz.2⟩)
    exact ⟨closure_minimal Set.inter_subset_left hT hz.1, hz.2⟩
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure {x}, isClosed_closure⟩ : TopologicalSpace.Closeds Y)
  let i := I.subschemeι
  have hi : Set.range i.base = closure {x} := by
    simp [i, I, Scheme.IdealSheafData.range_subschemeι]
  have hemb := i.isClosedEmbedding.isEmbedding
  have : IrreducibleSpace (Set.range i.base) :=
    Subtype.irreducibleSpace (hi ▸ isIrreducible_singleton.closure)
  have : IrreducibleSpace I.subscheme :=
    hemb.toHomeomorph.symm.surjective.irreducibleSpace hemb.toHomeomorph.symm.continuous
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian i
  obtain ⟨y, hy⟩ : x ∈ Set.range i.base := hi ▸ subset_closure rfl
  obtain ⟨_, ⟨(W : I.subscheme.Opens), hW, rfl⟩, hyW, hWO⟩ :=
    I.subscheme.isBasis_affineOpens.exists_subset_of_mem_open
      (a := y) (show y ∈ i.base ⁻¹' O by rw [Set.mem_preimage, hy]; exact hxO)
      (hO.preimage i.continuous)
  have : IsAffine W := hW
  have : Nonempty W := ⟨⟨y, hyW⟩⟩
  have : IsIntegral W := isIntegral_of_isOpenImmersion W.ι
  let s := W.ι ≫ i
  let F' := (upperStar (ModuleCat.{u + 1} A) (pullback.fst f s)).obj F
  have : Scheme.IsConstructibleSheaf F :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).mp hF
  have hF' : Scheme.IsConstructibleEtaleModuleSheaf F' :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F').mpr
      (Scheme.IsConstructibleSheaf.upperStar (pullback.fst f s) F)
  obtain ⟨V, j, hV, hj, hlisse⟩ := proper_cohomology_generic_local_constancy
    ℓ A W (pullback f s) (pullback.snd f s) F' hF' q hq
  have := hV
  have := hj
  have : Scheme.IsFiniteLocallyConstantSheaf
      ((upperStar (ModuleCat.{u + 1} A) j).obj
        (higherDirectImage A (pullback.snd f s) q F')) := hlisse
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let sq := IsPullback.of_hasPullback f s
  have := isIso_baseChange_of_isProper_of_torsionHomology A sq K
    (DerivedCategory.Plus.moduleTorsionHomology_of_isTorsion A X isAddTorsion_of_finite K)
  let e : (upperStar (ModuleCat.{u + 1} A) s).obj (higherDirectImage A f q F) ≅
      higherDirectImage A (pullback.snd f s) q F' :=
    ((upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlusHomologyFunctorIso q).app _ ≪≫
      (_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso
        (asIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} A) sq.toCommSq).app K)) ≪≫
      (_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso
        ((lowerStar (ModuleCat.{u + 1} A) (pullback.snd f s)).rightDerivedFunctorPlus.mapIso
          ((Functor.mapDerivedCategoryPlusSingleFunctor
            (upperStar (ModuleCat.{u + 1} A) (pullback.fst f s)) 0).app F))
  let ι := j ≫ s
  have hflc : Scheme.IsFiniteLocallyConstantSheaf
      ((upperStar (ModuleCat.{u + 1} A) ι).obj (higherDirectImage A f q F)) :=
    Scheme.IsFiniteLocallyConstantSheaf.of_iso
      (F := (upperStar (ModuleCat.{u + 1} A) j).obj
        (higherDirectImage A (pullback.snd f s) q F'))
      ((upperStar (ModuleCat.{u + 1} A) j).mapIso e.symm ≪≫
        ((upperStarComp (ModuleCat.{u + 1} A) j s).app _).symm)
  obtain ⟨O₃, hO₃, hpre⟩ := hemb.isInducing.isOpen_iff.1
    (W.ι.isOpenEmbedding.isOpenMap _ j.isOpenEmbedding.isOpen_range)
  have hr : Set.range ι.base = i.base '' (W.ι.base '' Set.range j.base) := by
    simp only [ι, s, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.image_comp]
  have hrO : Set.range ι.base ⊆ O := by
    rw [hr]
    rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact hWO w.2
  have hr₃ : Set.range ι.base = closure {x} ∩ O₃ := by
    rw [hr, ← hpre, Set.image_preimage_eq_range_inter, hi]
  have hrange : Set.range ι.base = T ∩ (O ∩ O₃) := by
    refine Set.Subset.antisymm (fun z hz ↦ ?_) (fun z ⟨hzT, hzO, hzO₃⟩ ↦ ?_)
    · have hzO := hrO hz
      rw [hr₃] at hz
      exact ⟨(hTO ▸ ⟨hz.1, hzO⟩ : z ∈ T ∩ O).1, hzO, hz.2⟩
    · rw [hr₃]
      exact ⟨(hTO.symm ▸ ⟨hzT, hzO⟩ : z ∈ closure {x} ∩ O).1, hzO₃⟩
  obtain ⟨v⟩ := hV
  exact ⟨O ∩ O₃, hO.inter hO₃, hrange ▸ ⟨ι v, v, rfl⟩,
    V, ι, inferInstance, hrange, hflc⟩

/-- Noetherian induction adjoins a generic finite locally constant stratum at each step. -/
private theorem higherDirectImage_constructible
    (ℓ : ℕ) [Fact ℓ.Prime] (A : Type (u + 1)) [Field A] [Finite A] [CharP A ℓ]
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) (q : ℤ) (hq : 0 ≤ q) :
    Scheme.IsConstructibleEtaleModuleSheaf (higherDirectImage A f q F) := by
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  -- Noetherian induction on open subsets: the complement of `O₀` has a finite partition into
  -- locally closed subsets along which `h_* E` is finite locally constant
  have key (O₀ : TopologicalSpace.Opens Y) : ∃ (n : ℕ) (str : Fin n → Set Y),
      (∀ k, IsLocallyClosed (str k)) ∧ ⋃ k, str k = (O₀ : Set Y)ᶜ ∧
      Pairwise (Function.onFun Disjoint str) ∧ ∀ k, ∃ (V : Scheme.{u}) (ι : V ⟶ Y),
        IsImmersion ι ∧ Set.range ι.base = str k ∧
          Scheme.IsFiniteLocallyConstantSheaf ((ι)^*[ModuleCat.{u + 1} A].obj
            (higherDirectImage A f q F)) := by
    induction O₀ using WellFoundedGT.induction with
    | _ O₀ ih =>
    by_cases hO₀ : (O₀ : Set Y)ᶜ = ∅
    · exact ⟨0, Fin.elim0, fun k ↦ k.elim0, by simp [hO₀], fun k ↦ k.elim0, fun k ↦ k.elim0⟩
    obtain ⟨O, hO, hne, V, ι, hι, hrange, hF⟩ :=
      higherDirectImage_generic_stratum ℓ A f F hF q hq
        O₀.isOpen.isClosed_compl (Set.nonempty_iff_ne_empty.2 hO₀)
    obtain ⟨n, str, hlc, hcov, hdisj, himm⟩ := ih (O₀ ⊔ ⟨O, hO⟩) (by
      refine lt_of_le_of_ne le_sup_left fun heq ↦ ?_
      obtain ⟨q, hq, hqO⟩ := hne
      refine hq ?_
      rw [heq]
      exact Or.inr hqO)
    have hstr (k : Fin n) : str k ⊆ (O₀ : Set Y)ᶜ ∩ Oᶜ := by
      intro q hq
      have hq' : q ∈ ⋃ k, str k := Set.mem_iUnion.2 ⟨k, hq⟩
      rw [hcov] at hq'
      simpa only [TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_mk, Set.mem_compl_iff,
        Set.mem_union, not_or, Set.mem_inter_iff] using hq'
    refine ⟨n + 1, Fin.cons ((O₀ : Set Y)ᶜ ∩ O) str, fun k ↦ ?_, ?_, fun k l hkl ↦ ?_,
      fun k ↦ ?_⟩
    · induction k using Fin.cases with
      | zero => exact O₀.isOpen.isClosed_compl.isLocallyClosed.inter hO.isLocallyClosed
      | succ k => exact hlc k
    · ext q
      simp only [Set.mem_iUnion, Fin.exists_fin_succ, Fin.cons_zero, Fin.cons_succ]
      rw [← Set.mem_iUnion (s := str), hcov]
      simp only [TopologicalSpace.Opens.coe_sup, Set.mem_inter_iff, Set.mem_compl_iff,
        Set.mem_union, TopologicalSpace.Opens.coe_mk, SetLike.mem_coe]
      tauto
    · induction k using Fin.cases with
      | zero =>
        induction l using Fin.cases with
        | zero => exact absurd rfl hkl
        | succ l =>
          exact Set.disjoint_left.2 fun q hq hq' ↦ (hstr l hq').2 hq.2
      | succ k =>
        induction l using Fin.cases with
        | zero =>
          exact Set.disjoint_right.2 fun q hq hq' ↦ (hstr k hq').2 hq.2
        | succ l => exact hdisj fun h ↦ hkl (congrArg Fin.succ h)
    · induction k using Fin.cases with
      | zero => exact ⟨V, ι, hι, hrange, hF⟩
      | succ k => exact himm k
  obtain ⟨n, str, hlc, hcov, hdisj, himm⟩ := key ⊥
  choose D ι hι hrange hF using himm
  exact Scheme.IsConstructibleSheaf.of_noetherianSpace _ str hlc
    (by simpa using hcov) hdisj ι hrange hF

/-- Proper higher direct images of constructible finite-field etale module sheaves are
constructible and vanish outside one interval [0, d], chosen independently of the sheaf.

Source: Bhatt--Scholze, Theorem 6.7.1, proper alternative, specialized to R = A;
Stacks Project, Tags 0A3V, 095U, 03RW and 0GL0
(blueprint: lem-fd-etale-finite-torsion-proper-finiteness).

Proof plan following the six DAG steps:
1. Properness gives finite type and the Noetherian target is quasi-compact.
   The uniform fibre-dimension lemma lem-fin-finite-type-fibre-dimension-bound
   supplies e with every fibre of h of dimension at most e. Choose d = 2e before F.
2. The underlying abelian sheaf of an A-module sheaf is torsion
   (definition-torsion-sheaves--3). Apply lem-kun-proper-torsion-cd-bound
   above 2e and transfer its vanishing to modules by
   lem-sbc-higher-direct-image-forget-comparison; the faithful forgetful functor reflects
   zero objects. For q < 0, right-derived functors preserve lower bounds
   (lem-weil-pbc-derived-functor-negative-vanishing) applied to F[0].
3. Fix F and q >= 0. A nonempty closed T in Y contains a nonempty irreducible relatively
   open piece T ∩ O (lem-sc-noetherian-closed-subset-finite-components,
   lem-sfb-noetherian-component-open). Give the closure of its generic point the reduced
   structure (lem-weil-pbc-reduced-induced-closed-subscheme); it is integral
   (def-pc-integral-scheme) and locally Noetherian. Choose a nonempty affine open W over O
   (lem-weil-pbc-noetherian-open-subscheme-noetherian).
4. Base change h to s : W → Y. Properness persists by lem-pc-proper-base-change, and the
   pullback of F is constructible by prop-constructible-pullback. Bounded-below proper base
   change theorem-proper-base-change-classical-pro for F[0], with the exact inverse-image/homology
   comparison lem-sp-exact-functor-preserves-homology, identifies s^* R^q h_*F with the
   degree-q image of the base change. Apply lem-fd-proper-cohomology-generic-local-constancy
   to obtain a nonempty open V of W where it is finite locally constant; the range of V in Y
   is T ∩ (an ambient open).
5. Well-founded induction on ambient opens O_0
   (lem-weil-pbc-noetherian-scheme-closed-subsets-minimal) builds a finite partition of
   the complement of O_0 into locally closed strata, each realised by an immersion on which
   R^q h_*F is finite locally constant: step 4 gives the new stratum and the induction
   hypothesis for the larger open gives the rest. At O_0 = ∅, locally closed subsets of a
   Noetherian space are constructible (def-weil-constructible-subset), so R^q h_*F is
   constructible (def-weil-pbc-etale-constructible-sheaf).
6. The zero sheaf is finite locally constant with value the zero A-module, hence
   constructible. This covers all remaining degrees from step 2. No ground field,
   absolute dimension bound, or invertibility of ell was used. -/
theorem exists_uniform_bound_constructible_higherDirectImage_of_isProper_finite_field
    (ℓ : ℕ) [Fact ℓ.Prime] (A : Type (u + 1)) [Field A] [Finite A] [CharP A ℓ]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (h : Z ⟶ Y) [IsProper h] :
    ∃ d : ℕ, ∀ (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)),
      Scheme.IsConstructibleEtaleModuleSheaf F → ∀ q : ℤ,
        Scheme.IsConstructibleEtaleModuleSheaf (higherDirectImage A h q F) ∧
          (q < 0 ∨ (d : ℤ) < q → IsZero (higherDirectImage A h q F)) := by
  classical
  obtain ⟨e, he⟩ := exists_fibre_dimension_bound h
  refine ⟨2 * e, fun F hF q ↦ ⟨?_, ?_⟩⟩
  · by_cases hq : q < 0
    · apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      exact Scheme.IsConstructibleSheaf.of_isZero
        (higherDirectImage_vanishes A h e he F q (Or.inl hq))
    · exact higherDirectImage_constructible ℓ A h F hF q (by omega)
  · intro hq
    apply higherDirectImage_vanishes A h e he F q
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hq

end AlgebraicGeometry.Etale
