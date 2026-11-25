/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.RingTheory.Ideal.Maps

import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism

/-!
# Finite geometric detection of scalar annihilation

Source: normalization exact-sequence blueprint, finite-coefficient reduction, steps 1 and 3
of `lem-weil-pbc-finite-coefficient-of-finite-stalks`.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The pullback of a constant chart is constant with the same value. -/
private noncomputable def constantChartPullbackIso
    {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : X.Etale)
    (M : ModuleCat.{u + 1} Λ)
    (e : G.over U ≅ (constantSheaf (X.smallEtaleTopology.over U)
      (ModuleCat.{u + 1} Λ)).obj M) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom).obj G ≅
      (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M := by
  have : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom).IsContinuous
      (X.smallGrothendieckTopology @AlgebraicGeometry.Etale)
      (U.left.smallGrothendieckTopology @AlgebraicGeometry.Etale) :=
    Scheme.isContinuous_overPullback @AlgebraicGeometry.Etale
      @AlgebraicGeometry.Etale le_rfl U.hom
  have : (MorphismProperty.Over.map ⊤ U.prop).IsContinuous
      (U.left.smallGrothendieckTopology @AlgebraicGeometry.Etale)
      (X.smallGrothendieckTopology @AlgebraicGeometry.Etale) :=
    Scheme.isContinuous_overMap U.prop le_rfl
  let a₁ := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom) (ModuleCat.{u + 1} Λ)
    (X.smallGrothendieckTopology @AlgebraicGeometry.Etale)
    (U.left.smallGrothendieckTopology @AlgebraicGeometry.Etale)
  let siteAdj := MorphismProperty.Over.mapPullbackAdj
    @AlgebraicGeometry.Etale ⊤ U.hom U.prop trivial
  let a₂ := siteAdj.sheafPushforwardContinuous (E := ModuleCat.{u + 1} Λ)
    (U.left.smallGrothendieckTopology @AlgebraicGeometry.Etale)
    (X.smallGrothendieckTopology @AlgebraicGeometry.Etale)
  let ρ := a₁.leftAdjointUniq a₂
  let σ : (Etale.overSheafEquiv U (ModuleCat.{u + 1} Λ)).functor.obj (G.over U) ≅
      ((MorphismProperty.Over.map ⊤ U.prop).sheafPushforwardContinuous
        (ModuleCat.{u + 1} Λ) (U.left.smallGrothendieckTopology @AlgebraicGeometry.Etale)
          (X.smallGrothendieckTopology @AlgebraicGeometry.Etale)).obj G :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (Functor.isoWhiskerRight (NatIso.op (Etale.etaleToOverCompForgetIso U).symm) G.obj)
  exact ρ.app G ≪≫ σ.symm ≪≫
    (Etale.overSheafEquiv U (ModuleCat.{u + 1} Λ)).functor.mapIso e ≪≫
    ((Etale.overEquiv U).constantSheafSheafCongrIso
      (X.smallEtaleTopology.over U) U.left.smallEtaleTopology
      (ModuleCat.{u + 1} Λ) Over.mkIdTerminal).app M

/-- The fibre functor sends scalar multiplication to scalar multiplication. -/
private theorem fiber_map_smul_id {Λ : Type (u + 1)} [CommRing Λ]
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (x : X) (r : Λ) :
    (pointSmallEtale (X.algClosurePoint x)).sheafFiber.map (r • 𝟙 F) =
      r • 𝟙 (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj F) := by
  apply (pointSmallEtale (X.algClosurePoint x)).presheafFiber_hom_ext
  intro U t
  change _ ≫ (pointSmallEtale (X.algClosurePoint x)).presheafFiber.map
    (r • 𝟙 F).hom = _
  rw [GrothendieckTopology.Point.toPresheafFiber_naturality]
  change (r • 𝟙 F.obj).app _ ≫ _ = _ ≫ (r • 𝟙 _)
  change (r • 𝟙 (F.obj.obj _)) ≫ _ = _ ≫ (r • 𝟙 _)
  simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp]
  exact (Category.comp_id _).symm

/-- A scalar annihilating all geometric stalks annihilates every section module. -/
private theorem stalk_annihilator_le_sections {Λ : Type (u + 1)} [CommRing Λ]
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (⨅ x : X, Module.annihilator Λ
      ((((pointSmallEtale (X.algClosurePoint x)).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj F)) ≤
      ⨅ U : X.Etaleᵒᵖ, Module.annihilator Λ (F.obj.obj U) := by
  have : CategoryTheory.AB5OfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    CategoryTheory.AB5OfSize_of_univLE.{u, u, u + 1, u + 1} (ModuleCat.{u + 1} Λ)
  intro r hr
  have hz : r • 𝟙 F = 0 := by
    apply sheafHom_ext_of_sheafFiber_map_algClosurePoint (A := ModuleCat.{u + 1} Λ)
    intro x
    let e := ((pointSmallEtale (X.algClosurePoint x)).uliftSheafFiberIso.{u + 1}
      (ModuleCat.{u + 1} Λ)).app F
    have hru := Module.mem_annihilator.mp (Ideal.mem_iInf.mp hr x)
    have hrl : r ∈ Module.annihilator Λ
        (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj F) := by
      apply Module.mem_annihilator.mpr
      intro m
      obtain ⟨m', rfl⟩ := e.toLinearEquiv.surjective m
      simpa using congrArg e.hom.hom (hru m')
    have hzero := ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).map_zero F F
    rw [fiber_map_smul_id F x r, hzero]
    ext m
    exact Module.mem_annihilator.mp hrl m
  apply Ideal.mem_iInf.mpr
  intro U
  apply Module.mem_annihilator.mpr
  intro m
  have h := congrArg (fun f : F ⟶ F => (f.hom.app U).hom m) hz
  exact h

/-- A constant chart identifies the annihilator of each of its stalks. -/
private theorem annihilator_stalk_constantChart {Λ : Type (u + 1)} [CommRing Λ]
    {X : Scheme.{u}} (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : X.Etale) (M : ModuleCat.{u + 1} Λ)
    (e : G.over U ≅ (constantSheaf (X.smallEtaleTopology.over U)
      (ModuleCat.{u + 1} Λ)).obj M)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ U.left) :
    Module.annihilator Λ (((pointSmallEtale (t ≫ U.hom)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj G) =
      Module.annihilator Λ M := by
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    Limits.preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1} _
  let d := ((AlgebraicGeometry.Etale.upperStarCompSheafFiberIso
    (ModuleCat.{u + 1} Λ) U.hom t).app G).symm ≪≫
    (pointSmallEtale t).sheafFiber.mapIso (constantChartPullbackIso G U M e) ≪≫
    (pointSmallEtale t).sheafFiberConstantSheafIso M
  exact d.toLinearEquiv.annihilator_eq

/-- A locally constant module sheaf on a compact scheme has finitely many stalk ideals. -/
private theorem exists_finite_stalk_ideals_of_locallyConstant
    {Λ : Type (u + 1)} [CommRing Λ] (X : Scheme.{u}) [CompactSpace X]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : IsLocallyConstantSheaf G) :
    ∃ I : Finset (Ideal Λ), ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ X),
      Module.annihilator Λ (((pointSmallEtale t).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj G) ∈ I := by
  classical
  have : JointlySurjective etalePrecoverage :=
    inferInstanceAs (JointlySurjective (precoverage @AlgebraicGeometry.Etale))
  obtain ⟨D⟩ := hG.nonempty_locallyConstantDatum
  let 𝒰 := D.cover
  have hvalues (i : 𝒰.I₀) : ∃ M : ModuleCat.{u + 1} Λ,
      Nonempty ((constantSheaf (X.smallEtaleTopology.over
        (𝒰.etalePrecoverageToEtale i)) (ModuleCat.{u + 1} Λ)).obj M ≅
          G.over (𝒰.etalePrecoverageToEtale i)) := by
    have := D.isConstant i
    exact (G.over (𝒰.etalePrecoverageToEtale i)).mem_essImage_of_isConstant
  choose M e using hvalues
  have hopen (i : 𝒰.I₀) : IsOpen (Set.range (𝒰.f i)) := by
    have : AlgebraicGeometry.Etale (𝒰.f i) := 𝒰.map_prop i
    exact (𝒰.f i).isOpenMap.isOpen_range
  have hcover : Set.univ ⊆ ⋃ i, Set.range (𝒰.f i) := by
    intro x _
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
    exact Set.mem_iUnion.mpr ⟨i, y, hy⟩
  obtain ⟨J, hJ⟩ := isCompact_univ.elim_finite_subcover
    (fun i ↦ Set.range (𝒰.f i)) hopen hcover
  refine ⟨J.image (fun i ↦ Module.annihilator Λ (M i)), ?_⟩
  intro Ω _ _ t
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hJ (Set.mem_univ (t default)))
  obtain ⟨hi, y, hy⟩ := Set.mem_iUnion.mp hi
  have : AlgebraicGeometry.Etale (𝒰.f i) := 𝒰.map_prop i
  obtain ⟨l, hl, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f i) t y hy
  have h := annihilator_stalk_constantChart G (𝒰.etalePrecoverageToEtale i)
    (M i) (e i).some.symm Ω l
  change Module.annihilator Λ (((pointSmallEtale (l ≫ 𝒰.f i)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj G) = _ at h
  rw [hl] at h
  exact Finset.mem_image.mpr ⟨i, hi, h.symm⟩

/-- Finite stratification and compact constant charts give a finite range of stalk ideals. -/
private theorem finite_range_stalk_annihilator {Λ : Type (u + 1)} [CommRing Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleSheaf F) :
    (Set.range (fun x : X ↦ Module.annihilator Λ
      ((((pointSmallEtale (X.algClosurePoint x)).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj F))).Finite := by
  classical
  obtain ⟨S, hS⟩ := hF.exists_stratification
  have hcompact (i : Fin S.n) : CompactSpace (S.domain i) := by
    have : TopologicalSpace.NoetherianSpace (S.domain i) :=
      (S.immersion i).isEmbedding.isInducing.noetherianSpace
    infer_instance
  have hfinite (i : Fin S.n) : ∃ I : Finset (Ideal Λ),
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S.domain i),
        Module.annihilator Λ (((pointSmallEtale t).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj
          ((AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} Λ)
            (S.immersion i)).obj F)) ∈ I := by
    have := hcompact i
    exact exists_finite_stalk_ideals_of_locallyConstant (S.domain i) _
      (hS i).toIsLocallyConstantSheaf
  choose I hI using hfinite
  apply (Finset.finite_toSet (Finset.univ.biUnion I)).subset
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ ⋃ i, S.stratum i := by rw [S.iUnion_stratum_eq_univ]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  rw [← S.range_immersion i] at hi
  obtain ⟨t, ht⟩ := exists_comp_eq_of_mem_range (S.immersion i) (X.algClosurePoint x)
    (by simpa using hi)
  let e := (AlgebraicGeometry.Etale.upperStarCompSheafFiberIso
    (ModuleCat.{u + 1} Λ) (S.immersion i) t).app F
  let d := ((pointSmallEtale (X.algClosurePoint x)).uliftSheafFiberIso.{u + 1}
    (ModuleCat.{u + 1} Λ)).app F
  have h := hI i _ t
  change Module.annihilator Λ ((AlgebraicGeometry.Etale.upperStar
    (ModuleCat.{u + 1} Λ) (S.immersion i) ⋙
      (pointSmallEtale t).sheafFiber).obj F) ∈ I i at h
  rw [e.toLinearEquiv.annihilator_eq, ht] at h
  change Module.annihilator Λ
    ((((pointSmallEtale (X.algClosurePoint x)).ulift.{u + 1}).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj F) ∈ Finset.univ.biUnion I
  rw [d.toLinearEquiv.annihilator_eq]
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, h⟩

/-- Finitely many geometric stalks detect scalar annihilation of a constructible module sheaf.
This does not require finite stalks or a finite coefficient ring.

Source: normalization exact-sequence blueprint, finite-coefficient reduction in
`lem-weil-pbc-finite-pushforward-finite-stalk-module`; steps 1 and 3 of
`lem-weil-pbc-finite-coefficient-of-finite-stalks`.
(blueprint: lem-weil-pbc-constructible-finite-stalk-annihilator-detection)

Proof: Choose the finite stratification witnessing constructibility. Each stratum is a
subspace of the Noetherian space X, hence compact. Its locally constant restriction has an
etale trivializing cover; openness of the chart maps and compactness give a finite subcover.
A geometric point lifts through a chart containing its image. The localized-site equivalence
identifies the chart restriction with its inverse image; the inverse-image stalk formula and
constant-sheaf stalk formula identify the stalk with that chart's constant module. Thus the
annihilators of all geometric stalks on a stratum lie in a finite set of ideals. Every
algebraic-closure point of X lifts through the immersion of a stratum containing its image.
The inverse-image stalk formula and the universe-lift isomorphism show that the annihilators
of F's displayed stalks lie in the finite union of those finite sets.

Enumerate the finite range of the stalk-annihilator function and choose a point x_i realizing
each ideal in that range. The intersection at these points is contained in the intersection
at all points of X, since every stalk ideal equals one of the selected ideals. For a scalar
in the latter intersection, transport annihilation through the universe-lift isomorphism.
The colimit cocone's naturality shows that its scalar endomorphism on a stalk is the stalk
of its scalar endomorphism on F. Joint faithfulness of geometric stalks makes that sheaf
endomorphism zero. Evaluate on each etale object to obtain annihilation of every section.
For empty X the range is empty, its enumeration has length zero, and joint faithfulness
applies vacuously. For the zero sheaf each stalk ideal is the unit ideal. No finiteness of
section modules, or of the coefficient ring, is used. -/
theorem exists_finite_stalk_annihilator_detection
    (Λ : Type (u + 1)) [CommRing Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleSheaf F) :
    ∃ (n : ℕ) (x : Fin n → X),
      (⨅ i : Fin n, Module.annihilator Λ
        ((((pointSmallEtale (X.algClosurePoint (x i))).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj F)) ≤
      ⨅ U : X.Etaleᵒᵖ, Module.annihilator Λ (F.obj.obj U) := by
  classical
  let a (x : X) : Ideal Λ := Module.annihilator Λ
    ((((pointSmallEtale (X.algClosurePoint x)).ulift.{u + 1}).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj F)
  have ha : (Set.range a).Finite := finite_range_stalk_annihilator F hF
  obtain ⟨n, J, -, hJ⟩ := ha.fin_param
  have hrep (i : Fin n) : ∃ x : X, a x = J i := by
    have : J i ∈ Set.range a := hJ ▸ Set.mem_range_self i
    exact this
  choose x hx using hrep
  refine ⟨n, x, le_trans ?_ (stalk_annihilator_le_sections F)⟩
  change (⨅ i : Fin n, a (x i)) ≤ ⨅ y : X, a y
  apply le_iInf
  intro y
  obtain ⟨i, hi⟩ := Set.mem_range.mp (hJ.symm ▸ Set.mem_range_self y)
  rw [← hi, ← hx i]
  exact iInf_le _ i

end AlgebraicGeometry.Scheme
