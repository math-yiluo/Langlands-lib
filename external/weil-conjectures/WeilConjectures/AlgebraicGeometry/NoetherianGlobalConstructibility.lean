/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
import WeilConjectures.CategoryTheory.CoefficientFiniteLocalSystemsPullback
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.ConstructibleSheaf.Pullback

/-!
# Affine-local and global constructibility on Noetherian schemes

Source: Stacks Project, etale-cohomology.tex, Tag 095E,
lemma-constructible-quasi-compact-quasi-separated; proetale.tex, Tag 09AJ,
definition-constructible; topology.tex, Tag 005L
(auxiliary; not a blueprint node).

The two statements treat the small etale and small pro-etale sites separately. Equivalent
coefficient-sized site models keep the coefficient universe independent of the scheme
universe. The sheaf is an intrinsic module over the constant coefficient ring sheaf.
Finite generation on the etale side is equivalent to finite presentation because the
coefficient ring is Noetherian; it never means finiteness of the underlying set.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace AlgebraicGeometry.Scheme

private noncomputable def modelBaseChangeComp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    coefficientEtaleBaseChange.{u, v} g ⋙ coefficientEtaleBaseChange.{u, v} f ≅
      coefficientEtaleBaseChange.{u, v} (f ≫ g) :=
  NatIso.ofComponents
    (fun (V : smallModelComparisonEtaleSite.{u, v} Z) ↦ AsSmall.up.mapIso
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g).symm.app
        (AsSmall.down.obj V)))
    (by
      intro V W a
      apply ULift.ext
      exact (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g).inv.naturality
        (AsSmall.down.map a))

private noncomputable def etaleFixedPullbackComp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (R : Type (max v (u + 1))) [CommRing R] :
    coefficientEtaleFixedPullback.{u, v} (f ≫ g) R ≅
      coefficientEtaleFixedPullback.{u, v} g R ⋙ coefficientEtaleFixedPullback.{u, v} f R := by
  let adj₁ := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (coefficientEtaleBaseChange.{u, v} (f ≫ g)) (ModuleCat R)
      (smallModelComparisonEtaleTopology.{u, v} Z)
      (smallModelComparisonEtaleTopology.{u, v} X)
  let adj₂ :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (coefficientEtaleBaseChange.{u, v} g) (ModuleCat R)
        (smallModelComparisonEtaleTopology.{u, v} Z)
        (smallModelComparisonEtaleTopology.{u, v} Y)).comp
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (coefficientEtaleBaseChange.{u, v} f) (ModuleCat R)
        (smallModelComparisonEtaleTopology.{u, v} Y)
        (smallModelComparisonEtaleTopology.{u, v} X))
  let i := Functor.sheafPushforwardContinuousComp' (eFG := modelBaseChangeComp f g)
    (ModuleCat R) (smallModelComparisonEtaleTopology.{u, v} Z)
    (smallModelComparisonEtaleTopology.{u, v} Y) (smallModelComparisonEtaleTopology.{u, v} X)
  exact ((conjugateIsoEquiv adj₁ adj₂).symm i.symm).symm

private noncomputable def proModelBaseChangeComp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    coefficientProEtaleModelBaseChange.{u, v} g ⋙ coefficientProEtaleModelBaseChange.{u, v} f ≅
      coefficientProEtaleModelBaseChange.{u, v} (f ≫ g) :=
  NatIso.ofComponents
    (fun (V : coefficientProEtaleSiteModel.{u, v} Z) ↦ AsSmall.up.mapIso
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).symm.app
        (AsSmall.down.obj V)))
    (by
      intro V W a
      apply ULift.ext
      exact (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).inv.naturality
        (AsSmall.down.map a))

private noncomputable def proFixedPullbackComp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (R : Type (max v (u + 1))) [CommRing R] :
    coefficientProEtaleFixedModulePullback.{u, v} (f ≫ g) R ≅
      coefficientProEtaleFixedModulePullback.{u, v} g R ⋙
        coefficientProEtaleFixedModulePullback.{u, v} f R := by
  let adj₁ := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (coefficientProEtaleModelBaseChange.{u, v} (f ≫ g)) (ModuleCat R)
      (coefficientProEtaleModelTopology.{u, v} Z)
      (coefficientProEtaleModelTopology.{u, v} X)
  let adj₂ :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (coefficientProEtaleModelBaseChange.{u, v} g) (ModuleCat R)
        (coefficientProEtaleModelTopology.{u, v} Z)
        (coefficientProEtaleModelTopology.{u, v} Y)).comp
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (coefficientProEtaleModelBaseChange.{u, v} f) (ModuleCat R)
        (coefficientProEtaleModelTopology.{u, v} Y)
        (coefficientProEtaleModelTopology.{u, v} X))
  let i := Functor.sheafPushforwardContinuousComp' (eFG := proModelBaseChangeComp f g)
    (ModuleCat R) (coefficientProEtaleModelTopology.{u, v} Z)
    (coefficientProEtaleModelTopology.{u, v} Y) (coefficientProEtaleModelTopology.{u, v} X)
  exact ((conjugateIsoEquiv adj₁ adj₂).symm i.symm).symm

private theorem coefficientFinite_of_iso {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Type w) [CommRing R]
    {F G : Sheaf J (ModuleCat R)} (e : F ≅ G)
    (h : IsCoefficientModelLocallyConstantFinite J R F) :
    IsCoefficientModelLocallyConstantFinite J R G := by
  intro V
  obtain ⟨S, hS, hm⟩ := h V
  refine ⟨S, hS, ?_⟩
  intro W f hf
  obtain ⟨M, hM, ⟨i⟩⟩ := hm W f hf
  exact ⟨M, hM, ⟨(J.overPullback (ModuleCat R) W).mapIso e.symm ≪≫ i⟩⟩

private theorem etaleFinite_comp
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (R : Type (max v (u + 1))) [CommRing R]
    (F : Sheaf (smallModelComparisonEtaleTopology.{u, v} X) (ModuleCat R))
    (h : IsCoefficientModelLocallyConstantFinite _ R
      ((coefficientEtaleFixedPullback.{u, v} f R).obj F)) :
    IsCoefficientModelLocallyConstantFinite _ R
      ((coefficientEtaleFixedPullback.{u, v} (g ≫ f) R).obj F) := by
  let : CategoryTheory.Limits.PreservesFiniteLimits
      (coefficientEtaleBaseChange.{u, v} g) := by
    let : PreservesFiniteLimits
        (AsSmall.down : smallModelComparisonEtaleSite.{u, v} Y ⥤ Y.Etale) :=
      inferInstanceAs (PreservesFiniteLimits
        (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := Y.Etale)).inverse)
    let : PreservesFiniteLimits
        (AsSmall.up : Z.Etale ⥤ smallModelComparisonEtaleSite.{u, v} Z) :=
      inferInstanceAs (PreservesFiniteLimits
        (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := Z.Etale)).functor)
    let : PreservesFiniteLimits (MorphismProperty.Over.pullback @Etale ⊤ g) :=
      inferInstance
    exact comp_preservesFiniteLimits _ _
  have hp := coefficient_finite_local_systems_pullback
    (smallModelComparisonEtaleTopology.{u, v} Y)
    (smallModelComparisonEtaleTopology.{u, v} Z)
    (coefficientEtaleBaseChange.{u, v} g) R
    ((coefficientEtaleFixedPullback.{u, v} f R).obj F) h
  exact coefficientFinite_of_iso _ R ((etaleFixedPullbackComp g f R).app F).symm hp

private theorem proFinite_comp
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (R : Type (max v (u + 1))) [CommRing R]
    (F : Sheaf (coefficientProEtaleModelTopology.{u, v} X) (ModuleCat R))
    (h : IsCoefficientModelLocallyConstantFinite _ R
      ((coefficientProEtaleFixedModulePullback.{u, v} f R).obj F)) :
    IsCoefficientModelLocallyConstantFinite _ R
      ((coefficientProEtaleFixedModulePullback.{u, v} (g ≫ f) R).obj F) := by
  let : CategoryTheory.Limits.PreservesFiniteLimits
      (coefficientProEtaleModelBaseChange.{u, v} g) := by
    let : PreservesFiniteLimits
        (AsSmall.down : coefficientProEtaleSiteModel.{u, v} Y ⥤ Y.ProEt) :=
      inferInstanceAs (PreservesFiniteLimits
        (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := Y.ProEt)).inverse)
    let : PreservesFiniteLimits
        (AsSmall.up : Z.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} Z) :=
      inferInstanceAs (PreservesFiniteLimits
        (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := Z.ProEt)).functor)
    dsimp only [coefficientProEtaleModelBaseChange]
    infer_instance
  have hp := coefficient_finite_local_systems_pullback
    (coefficientProEtaleModelTopology.{u, v} Y)
    (coefficientProEtaleModelTopology.{u, v} Z)
    (coefficientProEtaleModelBaseChange.{u, v} g) R
    ((coefficientProEtaleFixedModulePullback.{u, v} f R).obj F) h
  exact coefficientFinite_of_iso _ R ((proFixedPullbackComp g f R).app F).symm hp

private theorem finiteLocalModels_iff_presentation
    {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Type w)
    [CommRing R] [IsNoetherianRing R] (F : Sheaf J (ModuleCat R)) :
    IsCoefficientModelLocallyConstantFinite J R F ↔
      ∀ V : C, ∃ T : Sieve V, T ∈ J V ∧
        ∀ (W : C) (f : W ⟶ V), T f →
          ∃ M : ModuleCat R, Module.FinitePresentation R M ∧
            Nonempty (F.over W ≅ (constantSheaf (J.over W) (ModuleCat R)).obj M) := by
  constructor
  · intro h V
    obtain ⟨S, hS, hm⟩ := h V
    refine ⟨S, hS, ?_⟩
    intro W f hf
    obtain ⟨M, hM, he⟩ := hm W f hf
    let := hM
    exact ⟨M, Module.finitePresentation_of_finite R M, he⟩
  · intro h V
    obtain ⟨S, hS, hm⟩ := h V
    refine ⟨S, hS, ?_⟩
    intro W f hf
    obtain ⟨M, hM, he⟩ := hm W f hf
    let := hM
    exact ⟨M, inferInstance, he⟩

private def constructibleStratification {X : Scheme.{u}}
    (S : FiniteLocallyClosedStratification X)
    (hc : ∀ a, Topology.IsConstructible (S.stratum a)) : Stratification X where
  n := S.n
  stratum := S.stratum
  isLocallyClosed_stratum := S.isLocallyClosed_stratum
  isConstructible_stratum := hc
  iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
  pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
  domain := S.domain
  immersion := S.immersion
  isImmersion := S.isImmersion
  range_immersion := S.range_immersion

private def finiteStratification {X : Scheme.{u}} (S : Stratification X) :
    FiniteLocallyClosedStratification X where
  n := S.n
  stratum := S.stratum
  isLocallyClosed_stratum := S.isLocallyClosed_stratum
  iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
  pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
  domain := S.domain
  immersion := S.immersion
  isImmersion := S.isImmersion
  range_immersion := S.range_immersion

private theorem affine_local_stratification_iff
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (P : ∀ {Y : Scheme.{u}}, (Y ⟶ X) → Prop)
    (hP : ∀ {Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y), P f → P (g ≫ f)) :
    (∀ U : X.Opens, IsAffineOpen U →
      ∃ S : Stratification U.toScheme,
        (∀ a, Topology.IsConstructible (S.stratum a)) ∧
        ∀ a, P (S.immersion a ≫ U.ι)) ↔
    ∃ S : Stratification X,
      (∀ a, Topology.IsConstructible (S.stratum a)) ∧ ∀ a, P (S.immersion a) := by
  classical
  constructor
  · intro h
    have charts (x : X) : ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W := by
      obtain ⟨W, hW, hxW, _⟩ := exists_isAffineOpen_mem_and_subset
        (X := X) (x := x) (U := ⊤) trivial
      exact ⟨W, hW, hxW⟩
    choose W hW hxW using charts
    choose S hc hS using fun x ↦ h (W x) (hW x)
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
      (fun x : X ↦ (W x : Set X)) (fun x ↦ (W x).isOpen)
      (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxW x⟩)
    let e : Fin s.card ≃ s := (Fintype.equivFinOfCardEq (by simp)).symm
    let w (a : Fin s.card) : X := (e a).1
    have coverW : (⋃ a : Fin s.card, (W (w a) : Set X)) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
      exact Set.mem_iUnion.mpr ⟨e.symm ⟨y, hy⟩, by simpa [w] using hxy⟩
    obtain ⟨T, hTc, hT⟩ := exists_global_stratification_factoring_local s.card
      (fun a ↦ W (w a)) (fun a ↦ hW (w a)) coverW
      (fun a ↦ S (w a)) (fun a b ↦ hc (w a) b)
    refine ⟨T, hTc, ?_⟩
    intro a
    obtain ⟨i, j, q, hq⟩ := hT a
    have hp := hP ((S (w i)).immersion j ≫ (W (w i)).ι) q (hS (w i) j)
    rwa [hq] at hp
  · rintro ⟨S, _, hS⟩ U _
    refine ⟨S.pullback U.ι, (S.pullback U.ι).isConstructible_stratum, ?_⟩
    intro a
    have hp := hP (S.immersion a)
      (CategoryTheory.Limits.pullback.fst (S.immersion a) U.ι) (hS a)
    rw [CategoryTheory.Limits.pullback.condition] at hp
    exact hp

/-- On the small etale site, affine-local constructibility is equivalent to a single
finite constructible locally closed immersed stratification with locally constant
finitely presented module values. Finite generation in the existing local-constancy
predicate is equivalent to finite presentation over `R`.
Source: Stacks Project, Tag 095E, Noetherian module version; Tags 03RW(3) and 005L
(auxiliary; not a blueprint node).

Proof plan:
1. Choose a finite affine Noetherian cover of X. The underlying spaces of its members
are Noetherian (lem-sc-affine-noetherian-underlying-space), so their finite union is
Noetherian (lem-kun-finite-union-noetherian). Every subset is quasi-compact, including
X and every open (lem-sfb-noetherian-space-compact-subsets); this includes the empty cover.
2. The same cover makes X locally Noetherian (pqf-def-locnoeth), hence quasi-separated
(lem-weil-pbc-locally-noetherian-quasi-separated). Every open in any open subspace is
retrocompact, so every locally closed part is constructible (def-weil-constructible-subset).
3. Pull back trivializing etale coverings using lem-weil-pbc-etale-covering-base-change.
Finite limits of site base change (situation-conventions) and
lem-weil-pbc-left-exact-site-inverse-image-tensor give geometric inverse image and its
composition comparisons. Equivalences to the coefficient-sized sites preserve these data.
4. The scalar identifications and localized composition are
lem-pe-constant-left-module-inverse-image. Apply
lem-sfb-geometric-inverse-image-constant-module to each pulled-back local model: the
same module M gives a constant model, with its finite presentation unchanged. Over R,
Module.finitePresentation_of_finite and the converse instance identify the recorded
finite-generation predicate with finitely presented values.
5. Under affine-local constructibility, take the partitions on the finite affine cover.
theorem-comparison-constructible-sheaves supplies a global immersed refinement
and actual morphisms from its strata to local strata. Pull back their local models by
steps 3-4 to prove the right side; image containment alone is not used as factorization.
6. Conversely, lemma-constructible-pullback-stratification pulls a global partition back
to any affine open, including the empty one. Step 2 gives constructibility of its parts,
and steps 3-4 give their locally constant finitely presented models. No step needs R or M
to be finite as a set. -/
theorem etale_noetherian_global_constructibility
    (X : Scheme.{u}) [IsNoetherian X]
    (R : Type (max v (u + 1))) [CommRing R] [IsNoetherianRing R]
    (F : CategoryTheory.ConstantCompletion.Mod
      (CategoryTheory.ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X)
        R)) :
    IsCoefficientConstructibleEtaleModule X R F ↔
      ∃ S : Stratification X,
        (∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) ∧
        ∀ a : Fin S.n, IsCoefficientModelLocallyConstantFinite
          (smallModelComparisonEtaleTopology.{u, v} (S.domain a)) R
          ((coefficientEtaleFixedPullback.{u, v} (S.immersion a) R).obj
            ((coefficientModelFixedScalars _ R).obj F)) := by
  have h := affine_local_stratification_iff X
    (fun {Y} f ↦ IsCoefficientModelLocallyConstantFinite
      (smallModelComparisonEtaleTopology.{u, v} Y) R
      ((coefficientEtaleFixedPullback.{u, v} f R).obj
        ((coefficientModelFixedScalars _ R).obj F)))
    (fun f g h ↦ etaleFinite_comp f g R _ h)
  constructor
  · intro hF
    apply h.mp
    intro U hU
    obtain ⟨S, hc, hS⟩ := hF U hU
    exact ⟨constructibleStratification S hc, hc, hS⟩
  · intro hF U hU
    obtain ⟨S, hc, hS⟩ := h.mpr hF U hU
    exact ⟨finiteStratification S, hc, hS⟩

/-- On the small pro-etale site, the same affine-local/global equivalence holds with
finitely presented constant module values, without finiteness of the coefficient set.
Source: Stacks Project, Tag 095E, finite-refinement proof; proetale.tex,
Tag 09AJ, definition-constructible; topology.tex, Tag 005L
(auxiliary; not a blueprint node).

Proof plan:
1. A finite affine cover by Noetherian rings has Noetherian members
(lem-sc-affine-noetherian-underlying-space), hence Noetherian union
(lem-kun-finite-union-noetherian). By lem-sfb-noetherian-space-compact-subsets every
subset is quasi-compact, also for the empty scheme and the empty cover.
2. The scheme is locally Noetherian (pqf-def-locnoeth), hence quasi-separated by
lem-weil-pbc-locally-noetherian-quasi-separated. Every open of every open subspace is
retrocompact, so locally closed parts are constructible (def-weil-constructible-subset).
3. det-pe-topos-functoriality-inverse-image supplies preservation of pro-etale covers,
finite limits and composition comparisons for inverse image. Transporting by the
coefficient-sized site equivalences preserves all these operations and coverings.
4. Use lem-pe-constant-left-module-inverse-image for scalar and localized composition
comparisons, then lem-sfb-geometric-inverse-image-constant-module on each member of a
pulled-back trivializing cover. The same finitely presented R-module is the new constant
value. Thus every scheme pullback preserves these local models.
5. Apply theorem-comparison-constructible-sheaves to the partitions on a
finite affine cover. It is a geometric refinement statement independent of sheaves and
coefficients, and it supplies actual factorization morphisms into the local immersed
strata. Step 4 pulls the locally constant finitely presented models to the global strata.
6. Conversely, base change a global partition to an arbitrary affine open using
lemma-constructible-pullback-stratification. The parts are constructible by step 2,
and their local models pull back by step 4. This gives the left side, also on the empty
open, and proves the equivalence without set-finiteness hypotheses. -/
theorem proEtale_noetherian_global_constructibility
    (X : Scheme.{u}) [IsNoetherian X]
    (R : Type (max v (u + 1))) [CommRing R] [IsNoetherianRing R]
    (F : CategoryTheory.ConstantCompletion.Mod
      (CategoryTheory.ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X)
        R)) :
    IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X R F ↔
      ∃ S : Stratification X,
        (∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) ∧
        ∀ (a : Fin S.n) (V : coefficientProEtaleSiteModel.{u, v} (S.domain a)),
          ∃ T : Sieve V, T ∈ coefficientProEtaleModelTopology.{u, v} (S.domain a) V ∧
            ∀ (W : coefficientProEtaleSiteModel.{u, v} (S.domain a)) (f : W ⟶ V), T f →
              ∃ M : ModuleCat.{max v (u + 1)} R, Module.FinitePresentation R M ∧
                Nonempty
                  ((((coefficientProEtaleFixedModulePullback.{u, v} (S.immersion a) R).obj
                      ((coefficientModelFixedScalars _ R).obj F)).over W) ≅
                    (constantSheaf
                      ((coefficientProEtaleModelTopology.{u, v} (S.domain a)).over W)
                      (ModuleCat.{max v (u + 1)} R)).obj M) := by
  have h := affine_local_stratification_iff X
    (fun {Y} f ↦ IsCoefficientModelLocallyConstantFinite
      (coefficientProEtaleModelTopology.{u, v} Y) R
      ((coefficientProEtaleFixedModulePullback.{u, v} f R).obj
        ((coefficientModelFixedScalars _ R).obj F)))
    (fun f g h ↦ proFinite_comp f g R _ h)
  simpa only [IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf,
    finiteLocalModels_iff_presentation] using h

end AlgebraicGeometry.Scheme
