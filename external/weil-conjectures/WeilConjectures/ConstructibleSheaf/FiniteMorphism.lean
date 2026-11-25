/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.Topology.NoetherianSpace
public import WeilConjectures.SixFunctors.Finite.BaseChange
public import WeilConjectures.SixFunctors.Finite.Counit
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleUnderlyingSets
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAbelianLiftHom
import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison
import WeilConjectures.AlgebraicGeometry.GenericFinitePushforward
import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves

/-!
# Finite direct images of constructible sheaves on Noetherian schemes

Let `Λ` be a finite commutative ring. For a finite morphism `h : V ⟶ U` of schemes with `U`
Noetherian:

- `AlgebraicGeometry.Etale.exists_dense_isFiniteLocallyConstantSheaf_lowerStar` (blueprint
  `lem-weil-pbc-finite-pushforward-generic-constructible`): over an integral Noetherian affine
  base, the direct image of a constructible sheaf is finite locally constant on a dense open.
- `AlgebraicGeometry.Etale.exists_isOpen_isFiniteLocallyConstantSheaf_upperStar_lowerStar`: the
  resulting Noetherian induction step, every nonempty closed subset of `U` has a nonempty
  relatively open subset along which `h_* E` is finite locally constant.
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.lowerStar_of_isFinite` (blueprint
  `lemma-detection-proper-direct-image--1`): the direct image `h_* E` of a
  constructible sheaf is constructible.
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_lowerStar_of_isFinite` (blueprint
  `lemma-detection-proper-direct-image--1`): conversely, if `h_* F` is constructible and `V`
  is Noetherian, then `F` is constructible.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology
open AlgebraicGeometry.Etale

noncomputable section

/-- A nonempty subset `Z` of a Noetherian space has a nonempty irreducible relatively open subset
`Z ∩ O`: inside the Noetherian space `Z`, a point lying in a single irreducible component has a
preirreducible open neighbourhood. -/
lemma TopologicalSpace.NoetherianSpace.exists_isOpen_isIrreducible_inter {α : Type*}
    [TopologicalSpace α] [NoetherianSpace α] {Z : Set α} (hZ : Z.Nonempty) :
    ∃ O : Set α, IsOpen O ∧ IsIrreducible (Z ∩ O) := by
  have : Nonempty Z := hZ.to_subtype
  obtain ⟨U₀, -, ⟨x, hx⟩, hU₀⟩ := exists_isOpen_nonempty_forall_eq (α := Z)
  obtain ⟨N, hN, hxN, hNirr⟩ := exists_isOpen_isPreirreducible x (hU₀ x hx)
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 hN
  refine ⟨O, hO, ?_⟩
  rw [← Subtype.image_preimage_coe]
  exact IsIrreducible.image ⟨⟨x, hxN⟩, hNirr⟩ _ continuous_subtype_val.continuousOn

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- Blueprint `lem-weil-pbc-finite-pushforward-generic-constructible`: Generic finite pushforward
is constructible.

Let `S` be an integral Noetherian affine scheme, `g : Z ⟶ S` a finite morphism and `E` a
constructible sheaf of `Λ`-modules on `Z_ét`. Then there is a dense open `S° ⊆ S` on which the
direct image `g_* E` is finite locally constant (lisse). -/
theorem Etale.exists_dense_isFiniteLocallyConstantSheaf_lowerStar {S Z : Scheme.{u}}
    [IsIntegral S] [IsAffine S] [IsNoetherian S] (g : Z ⟶ S) [IsFinite g]
    (E : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf E] :
    ∃ U : S.Opens, Dense (U : Set S) ∧
      IsFiniteLocallyConstantSheaf
        ((U.ι)^*[ModuleCat.{u + 1} Λ].obj ((g)_*[ModuleCat.{u + 1} Λ].obj E)) := by
  -- the generic lissity of finite direct images of constructible abelian sheaves, applied to
  -- the underlying sheaf of abelian groups of `E`
  have hE := isConstructibleEtaleSheafOfSets_of_module Λ E
    ((isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf E).2 inferInstance)
  obtain ⟨U, hU, hlisse⟩ := exists_dense_open_lisse_finite_directImage S g _ hE
  refine ⟨U, hU, ?_⟩
  let H := (g)_*[ModuleCat.{u + 1} Λ].obj E
  let G := (U.ι)^*[ModuleCat.{u + 1} Λ].obj H
  -- inverse image commutes with forgetting the module structure
  obtain ⟨em⟩ := Etale.pullback_forget_modules_iso Λ U.ι H
  have hL : PreservesFiniteLimits (etaleSetPullback U.ι) := by
    unfold etaleSetPullback Functor.sheafPullbackConstruction.sheafPullback
    let : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
      AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} (Type (u + 1))
    infer_instance
  obtain ⟨ea, -⟩ := etaleInverseImageAbelianLift_hom U S U.ι hL
  let e : (sheafForget U.toScheme.smallEtaleTopology).obj G ≅ _ :=
    (sheafCompose U.toScheme.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).mapIso em ≪≫
      ea.app ((sheafCompose S.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj H)
  -- so the underlying sheaf of sets of `G` is finite locally constant
  have hT : IsFiniteLocallyConstantSheafOfTypes
      ((sheafForget U.toScheme.smallEtaleTopology).obj G) := by
    obtain ⟨⟨𝒰, h𝒰⟩, hfin⟩ := hlisse
    refine ⟨⟨𝒰, fun j ↦ ?_⟩, isFiniteSheaf_of_finite_algClosed_stalks _ fun Ω _ _ s ↦ ?_⟩
    · exact @Sheaf.isConstant_congr _ _ _ _ _ _ _ _
        ((U.toScheme.smallEtaleTopology.overPullback (Type (u + 1)) _).mapIso e.symm) (h𝒰 j)
    · exact @Finite.of_equiv _ _ ((ConcreteCategory.isFinitelyGenerated_iff_finite _).mp
          (hfin.isFinitelyGenerated_sheafFiber Ω s))
        ((pointSmallEtale s).sheafFiber.mapIso e.symm).toEquiv
  -- over the finite ring `Λ` this makes `G` itself finite locally constant
  obtain ⟨𝒰, h𝒰⟩ := (lisseModuleSheaf_iff_underlying_finiteLocallyConstant G).2 hT
  refine (finite_locally_constant_module_values_iff G).1.1 ⟨⟨𝒰, fun i ↦ ?_⟩, h𝒰⟩
  obtain ⟨M, _, ⟨e⟩⟩ := h𝒰 i
  exact Sheaf.isConstant_of_iso _ e

/-- The generic step of `AlgebraicGeometry.Scheme.IsConstructibleSheaf.lowerStar_of_isFinite`:
a nonempty closed subset `Z` of the Noetherian base has a nonempty relatively open subset
`Z ∩ O`, realised by an immersion, along which the direct image `h_* E` pulls back to a finite
locally constant sheaf. Take `Z ∩ O` irreducible with generic point `x`; on an affine open `W` of
the reduced closure of `x` lying over `O` the direct image is, by finite base change, the direct
image along a finite morphism to an integral Noetherian affine scheme, which is finite locally
constant on a dense open
(`AlgebraicGeometry.Etale.exists_dense_isFiniteLocallyConstantSheaf_lowerStar`). -/
theorem Etale.exists_isOpen_isFiniteLocallyConstantSheaf_upperStar_lowerStar {U V : Scheme.{u}}
    [IsNoetherian U] (h : V ⟶ U) [IsFinite h]
    (E : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf E] {Z : Set U}
    (hZ : IsClosed Z) (hne : Z.Nonempty) :
    ∃ O : Set U, IsOpen O ∧ (Z ∩ O).Nonempty ∧ ∃ (Y : Scheme.{u}) (ι : Y ⟶ U), IsImmersion ι ∧
      Set.range ι.base = Z ∩ O ∧
        IsFiniteLocallyConstantSheaf ((ι)^*[ModuleCat.{u + 1} Λ].obj
          ((h)_*[ModuleCat.{u + 1} Λ].obj E)) := by
  obtain ⟨O, hO, hirr⟩ := TopologicalSpace.NoetherianSpace.exists_isOpen_isIrreducible_inter hne
  -- the generic point `x` of `Z ∩ O`
  set x := hirr.genericPoint
  have hx := hirr.isGenericPoint_genericPoint_closure
  obtain ⟨p, hp⟩ := hirr.nonempty
  have hxO : x ∈ O := (hx.mem_open_set_iff hO).2 ⟨p, subset_closure hp, hp.2⟩
  have hZO : closure {x} ∩ O = Z ∩ O := by
    rw [hx.def]
    refine subset_antisymm (fun q ⟨hq, hqO⟩ ↦ ?_) (fun q hq ↦ ⟨subset_closure hq, hq.2⟩)
    exact ⟨closure_minimal Set.inter_subset_left hZ hq, hqO⟩
  -- the integral closed subscheme `i : Y ⟶ U` with support the closure of `x`
  let I := IdealSheafData.vanishingIdeal
    (⟨closure {x}, isClosed_closure⟩ : TopologicalSpace.Closeds U)
  let i := I.subschemeι
  have hi : Set.range i.base = closure {x} := by simp [i, I, IdealSheafData.range_subschemeι]
  have hemb := i.isClosedEmbedding.isEmbedding
  have : IrreducibleSpace (Set.range i.base) :=
    Subtype.irreducibleSpace (hi ▸ isIrreducible_singleton.closure)
  have : IrreducibleSpace I.subscheme :=
    hemb.toHomeomorph.symm.surjective.irreducibleSpace hemb.toHomeomorph.symm.continuous
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian i
  -- an affine open `W` of the closure lying over `O`
  obtain ⟨y, hy⟩ : x ∈ Set.range i.base := hi ▸ subset_closure rfl
  obtain ⟨_, ⟨(W : I.subscheme.Opens), hW, rfl⟩, hyW, hWO⟩ :=
      I.subscheme.isBasis_affineOpens.exists_subset_of_mem_open
      (a := y) (show y ∈ i.base ⁻¹' O by rw [Set.mem_preimage, hy]; exact hxO)
      (hO.preimage i.continuous)
  have : IsAffine W := hW
  have : Nonempty W := ⟨⟨y, hyW⟩⟩
  have : IsIntegral W := isIntegral_of_isOpenImmersion W.ι
  have : IsNoetherian W := {}
  let ιW := W.ι ≫ i
  -- the direct image is finite locally constant on a dense open `S₀` of `W`
  have := IsConstructibleSheaf.upperStar (pullback.fst h ιW) E
  obtain ⟨S₀, hS₀, hlisse⟩ := exists_dense_isFiniteLocallyConstantSheaf_lowerStar
    (pullback.snd h ιW) ((pullback.fst h ιW)^*[ModuleCat.{u + 1} Λ].obj E)
  have sq := IsPullback.of_hasPullback h ιW
  have := Etale.isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} Λ) sq
  let e := asIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app E)
  let ι := S₀.ι ≫ ιW
  have hF : IsFiniteLocallyConstantSheaf ((ι)^*[ModuleCat.{u + 1} Λ].obj
      ((h)_*[ModuleCat.{u + 1} Λ].obj E)) :=
    IsFiniteLocallyConstantSheaf.of_iso (F := (S₀.ι)^*[ModuleCat.{u + 1} Λ].obj
      ((pullback.snd h ιW)_*[ModuleCat.{u + 1} Λ].obj
        ((pullback.fst h ιW)^*[ModuleCat.{u + 1} Λ].obj E)))
      (((S₀.ι)^*[ModuleCat.{u + 1} Λ]).mapIso e.symm ≪≫
        ((upperStarComp (ModuleCat.{u + 1} Λ) S₀.ι ιW).app _).symm)
  -- the range of `ι` is relatively open in `Z`
  obtain ⟨O₃, hO₃, hpre⟩ := hemb.isInducing.isOpen_iff.1
    (W.ι.isOpenEmbedding.isOpenMap _ S₀.isOpen)
  have hr : Set.range ι.base = i.base '' (W.ι.base '' S₀) := by
    simp only [ι, ιW, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι, Set.image_comp]
  have hrO : Set.range ι.base ⊆ O := by
    rw [hr]
    rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact hWO w.2
  have hr₃ : Set.range ι.base = closure {x} ∩ O₃ := by
    rw [hr, ← hpre, Set.image_preimage_eq_range_inter, hi]
  have hrange : Set.range ι.base = Z ∩ (O ∩ O₃) := by
    refine subset_antisymm (fun q hq ↦ ?_) (fun q ⟨hqZ, hqO, hqO₃⟩ ↦ ?_)
    · have hqO := hrO hq
      rw [hr₃] at hq
      exact ⟨(hZO ▸ ⟨hq.1, hqO⟩ : q ∈ Z ∩ O).1, hqO, hq.2⟩
    · rw [hr₃]
      exact ⟨(hZO.symm ▸ ⟨hqZ, hqO⟩ : q ∈ closure {x} ∩ O).1, hqO₃⟩
  obtain ⟨s, hs⟩ := hS₀.nonempty
  refine ⟨O ∩ O₃, hO.inter hO₃, hrange ▸ ⟨_, ⟨s, hs⟩, rfl⟩, _, ι, inferInstance, hrange, hF⟩

/-- Blueprint `lemma-detection-proper-direct-image--1`: Finite pushforward
preserves constructibility on Noetherian schemes.

Let `U` be Noetherian, `h : V ⟶ U` finite and `E` a constructible sheaf of `Λ`-modules on
`V_ét`. Then its direct image `h_* E` is constructible on `U_ét`. -/
theorem Scheme.IsConstructibleSheaf.lowerStar_of_isFinite {U V : Scheme.{u}} [IsNoetherian U]
    (h : V ⟶ U) [IsFinite h] (E : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf E] : IsConstructibleSheaf ((h)_*[ModuleCat.{u + 1} Λ].obj E) := by
  -- Noetherian induction on open subsets: the complement of `O₀` has a finite partition into
  -- locally closed subsets along which `h_* E` is finite locally constant
  have key (O₀ : TopologicalSpace.Opens U) : ∃ (n : ℕ) (str : Fin n → Set U),
      (∀ k, IsLocallyClosed (str k)) ∧ ⋃ k, str k = (O₀ : Set U)ᶜ ∧
      Pairwise (Function.onFun Disjoint str) ∧ ∀ k, ∃ (Y : Scheme.{u}) (ι : Y ⟶ U),
        IsImmersion ι ∧ Set.range ι.base = str k ∧
          IsFiniteLocallyConstantSheaf ((ι)^*[ModuleCat.{u + 1} Λ].obj
            ((h)_*[ModuleCat.{u + 1} Λ].obj E)) := by
    induction O₀ using WellFoundedGT.induction with
    | _ O₀ ih =>
    by_cases hO₀ : (O₀ : Set U)ᶜ = ∅
    · exact ⟨0, Fin.elim0, fun k ↦ k.elim0, by simp [hO₀], fun k ↦ k.elim0, fun k ↦ k.elim0⟩
    obtain ⟨O, hO, hne, Y, ι, hι, hrange, hF⟩ :=
      Etale.exists_isOpen_isFiniteLocallyConstantSheaf_upperStar_lowerStar h E
        O₀.isOpen.isClosed_compl (Set.nonempty_iff_ne_empty.2 hO₀)
    obtain ⟨n, str, hlc, hcov, hdisj, himm⟩ := ih (O₀ ⊔ ⟨O, hO⟩) (by
      refine lt_of_le_of_ne le_sup_left fun heq ↦ ?_
      obtain ⟨q, hq, hqO⟩ := hne
      refine hq ?_
      rw [heq]
      exact Or.inr hqO)
    have hstr (k : Fin n) : str k ⊆ (O₀ : Set U)ᶜ ∩ Oᶜ := by
      intro q hq
      have hq' : q ∈ ⋃ k, str k := Set.mem_iUnion.2 ⟨k, hq⟩
      rw [hcov] at hq'
      simpa only [TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_mk, Set.mem_compl_iff,
        Set.mem_union, not_or, Set.mem_inter_iff] using hq'
    refine ⟨n + 1, Fin.cons ((O₀ : Set U)ᶜ ∩ O) str, fun k ↦ ?_, ?_, fun k l hkl ↦ ?_,
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
      | zero => exact ⟨Y, ι, hι, hrange, hF⟩
      | succ k => exact himm k
  obtain ⟨n, str, hlc, hcov, hdisj, himm⟩ := key ⊥
  choose Y ι hι hrange hF using himm
  exact IsConstructibleSheaf.of_noetherianSpace _ str hlc (by simpa using hcov) hdisj ι hrange hF

/-- Blueprint `lemma-detection-proper-direct-image--1`: Finite direct image reflects
constructibility.

Let `p : Z ⟶ S` be a finite morphism of Noetherian schemes and `F` an étale sheaf of
`Λ`-modules on `Z`. If its direct image `p_* F` is constructible, then `F` is constructible. -/
theorem Scheme.IsConstructibleSheaf.of_lowerStar_of_isFinite {Z S : Scheme.{u}} [IsNoetherian Z]
    [IsNoetherian S] (p : Z ⟶ S) [IsFinite p] (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleSheaf ((p)_*[ModuleCat.{u + 1} Λ].obj F)) : IsConstructibleSheaf F := by
  let ε := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).counit.app F
  have : IsConstructibleSheaf
      (((p)_*[ModuleCat.{u + 1} Λ] ⋙ (p)^*[ModuleCat.{u + 1} Λ]).obj F) :=
    IsConstructibleSheaf.upperStar p ((p)_*[ModuleCat.{u + 1} Λ].obj F)
  have : IsConstructibleSheaf (Limits.kernel ε) := IsConstructibleSheaf.of_mono
    (F := ((p)_*[ModuleCat.{u + 1} Λ] ⋙ (p)^*[ModuleCat.{u + 1} Λ]).obj F) (kernel.ι ε)
  have : IsConstructibleSheaf (Limits.cokernel (kernel.ι ε)) := IsConstructibleSheaf.cokernel _
  let e : Limits.cokernel (kernel.ι ε) ≅ F :=
    (cokernelIsCokernel (kernel.ι ε)).coconePointUniqueUpToIso
      (Abelian.epiIsCokernelOfKernel _ (limit.isLimit _))
  exact IsConstructibleSheaf.of_iso e

end AlgebraicGeometry

end
