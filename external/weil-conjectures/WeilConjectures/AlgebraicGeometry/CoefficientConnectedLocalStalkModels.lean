/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
public import WeilConjectures.AlgebraicGeometry.CoefficientEtaleDerivedStalk
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.AlgebraicGeometry.CoefficientEtaleDerivedChartAtlas
public import Mathlib.Topology.Connected.Basic
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Local models given by a specified geometric stalk on a connected component

Source: Stacks Project, Etale Cohomology, Tag 09BI, and Pro-etale Cohomology, Tag 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem stalks_agree_on_component
    {T : Type*} [TopologicalSpace T] {D : Type*} [Category D]
    {I : Type*} (O : I → Set T) (hopen : ∀ i, IsOpen (O i))
    (hcover : ∀ x, ∃ i, x ∈ O i) (M : I → D) (F : T → D)
    (hmodel : ∀ i x, x ∈ O i → Nonempty (M i ≅ F x))
    (z x : T) (hx : x ∈ connectedComponent z) : Nonempty (F z ≅ F x) := by
  classical
  let G : Set T := {y | Nonempty (F z ≅ F y)}
  have hg : IsOpen G := by
    apply isOpen_iff_forall_mem_open.mpr
    intro y hy
    obtain ⟨i, hi⟩ := hcover y
    refine ⟨O i, ?_, hopen i, hi⟩
    intro t ht
    obtain ⟨e⟩ := hy
    obtain ⟨ey⟩ := hmodel i y hi
    obtain ⟨et⟩ := hmodel i t ht
    exact ⟨e ≪≫ ey.symm ≪≫ et⟩
  have hgc : IsOpen Gᶜ := by
    apply isOpen_iff_forall_mem_open.mpr
    intro y hy
    obtain ⟨i, hi⟩ := hcover y
    refine ⟨O i, ?_, hopen i, hi⟩
    intro t ht he
    obtain ⟨e⟩ := he
    obtain ⟨ey⟩ := hmodel i y hi
    obtain ⟨et⟩ := hmodel i t ht
    exact hy ⟨e ≪≫ et.symm ≪≫ ey⟩
  have hsub : connectedComponent z ⊆ G :=
    isPreconnected_connectedComponent.subset_left_of_subset_union hg hgc
      disjoint_compl_right (by intro y _; exact (em (y ∈ G)))
      ⟨z, mem_connectedComponent, ⟨Iso.refl _⟩⟩
  exact hsub hx

/-- A bounded lisse complex has the specified stalk as a common local model on
objects mapping into its connected component.
Source: Stacks Project, Etale Cohomology, Tag 09BI; Pro-etale Cohomology, Tag 09C6,
first paragraph, before the weak-contractibility argument.
(auxiliary; not a blueprint node).

Proof: Obtain an etale chart through each point, with its individual algebraic
model, its stalk identifications and its comparison realization, from
coefficient_etale_derived_chart_atlas. The set of points whose stalk is
isomorphic to the stalk at z is open: any chart containing such a point lies
in the set. Its complement is open by the same chart argument. Preconnectedness
of the connected component of z therefore puts that whole component in the set.
For each point of U, pull back an etale chart through its image. The resulting
family is jointly surjective by the scheme pullback carrier lemma, so is an
etale, hence pro-etale, covering family. Transport its generated sieve through
AsSmall. Every arrow in this sieve factors through a chosen chart, where the
atlas realizes the pullback of K by its model. Compose the isomorphism from the
specified stalk at z to the stalk at the chart's chosen point with the inverse
of that chart's stalk identification, and apply constant realization followed
by slice restriction. This gives the required local isomorphism. If U is empty,
the family is empty and is still covering by the same surjectivity criterion.
Neither openness of connected components nor a separate empty-slice argument
is needed -/
theorem coefficient_connected_local_stalk_models
    (X : Scheme.{u}) [IsNoetherian X]
    (B : Type (max v (u + 1))) [CommRing B] [IsNoetherianRing B]
    (z : X) (U : coefficientProEtaleSiteModel.{u, v} X)
    (himage : Set.range
      (((AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).obj U).hom.base) ⊆
        connectedComponent z)
    (K : ConstantCompletion.D
      (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X) B))
    (hbounded : ∃ c d : ℤ, ∀ q : ℤ, q < c ∨ d < q →
      IsZero ((coefficientModelCohomology _ q).obj K))
    (hlisse : ∀ q : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules
      (smallModelComparisonEtaleTopology.{u, v} X) B
      ((coefficientModelCohomology _ q).obj K)) :
    letI := HasDerivedCategory.standard (ConstantCompletion.Mod
      (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) B))
    ∃ S : Sieve U, S ∈ coefficientProEtaleModelTopology.{u, v} X U ∧
      ∀ (V : coefficientProEtaleSiteModel.{u, v} X) (f : V ⟶ U), S f →
        Nonempty ((adicResidueRestriction
          (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) B) V).obj
            ((commutativeSiteDerivedConstantModuleFunctor.{max v (u + 1), max v (u + 1),
              max v (u + 1), max v (u + 1) + 1}
              (coefficientProEtaleModelTopology.{u, v} X) B).obj
              ((coefficientEtaleDerivedStalk X B (X.algClosurePoint z)).obj K)) ≅
          (adicResidueRestriction
          (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) B) V).obj
            ((adicFinitePullback.{u, v} X B).obj K)) := by
  classical
  let := HasDerivedCategory.standard (ConstantCompletion.Mod
    (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) B))
  obtain ⟨W, M, hw, hstalk, hcomparison⟩ :=
    coefficient_etale_derived_chart_atlas X B K hbounded hlisse
  let stalk (x : X) := (coefficientEtaleDerivedStalk X B (X.algClosurePoint x)).obj K
  have heq (x : X) (hx : x ∈ connectedComponent z) : Nonempty (stalk z ≅ stalk x) :=
    stalks_agree_on_component (fun i ↦ Set.range (W i).hom.base)
      (fun i ↦ (W i).hom.isOpenMap.isOpen_range) (fun x ↦ ⟨x, hw x⟩)
      M stalk hstalk z x hx
  let U' := (AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).obj U
  let p (x : U'.left) : X := U'.hom x
  let Y (x : U'.left) := pullback (W (p x)).hom U'.hom
  let V (x : U'.left) : X.ProEt :=
    ProEt.mk (pullback.snd (W (p x)).hom U'.hom ≫ U'.hom)
  let f (x : U'.left) : V x ⟶ U' :=
    MorphismProperty.Over.homMk (pullback.snd (W (p x)).hom U'.hom) rfl
  let g (x : U'.left) : V x ⟶ (toProEt X).obj (W (p x)) :=
    MorphismProperty.Over.homMk (pullback.fst (W (p x)).hom U'.hom) pullback.condition
  have hcover : Presieve.ofArrows V f ∈ ProEt.precoverage X U' := by
    rw [ProEt.precoverage, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    apply etalePrecoverage_le_proetalePrecoverage
    change Presieve.ofArrows Y (fun x ↦ pullback.snd (W (p x)).hom U'.hom) ∈
      etalePrecoverage U'.left
    apply (ofArrows_mem_precoverage_iff _).mpr
    refine ⟨fun x ↦ ?_, fun _ ↦ inferInstance⟩
    obtain ⟨y, hy⟩ := hw (p x)
    obtain ⟨t, _, ht⟩ := Pullback.exists_preimage_pullback y x hy
    exact ⟨x, t, ht⟩
  let e : X.ProEt ≌ coefficientProEtaleSiteModel.{u, v} X := AsSmall.equiv
  have : e.functor.IsDenseSubsite (ProEt.topology X)
      (coefficientProEtaleModelTopology.{u, v} X) :=
    inferInstanceAs (e.functor.IsDenseSubsite (ProEt.topology X)
      (e.inverse.inducedTopology (ProEt.topology X)))
  let S := Sieve.ofArrows (fun x ↦ e.functor.obj (V x)) (fun x ↦ e.functor.map (f x))
  have hS : S ∈ coefficientProEtaleModelTopology.{u, v} X U := by
    dsimp only [S]
    rw [← Sieve.functorPushforward_ofArrows]
    exact (e.functor.functorPushforward_mem_iff (ProEt.topology X)
      (coefficientProEtaleModelTopology.{u, v} X)).mpr
        (Precoverage.generate_mem_toGrothendieck hcover)
  refine ⟨S, hS, ?_⟩
  intro T a ha
  obtain ⟨_, b, _, ⟨x⟩, _⟩ := ha
  have ht : Nonempty
      ((adicResidueRestriction
        (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) B) T).obj
          ((commutativeSiteDerivedConstantModuleFunctor.{max v (u + 1), max v (u + 1),
            max v (u + 1), max v (u + 1) + 1}
            (coefficientProEtaleModelTopology.{u, v} X) B).obj (M (p x))) ≅
        (adicResidueRestriction
          (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) B) T).obj
            ((adicFinitePullback.{u, v} X B).obj K)) :=
    hcomparison (p x) T (e.inverse.map b ≫ g x)
  obtain ⟨et⟩ := ht
  obtain ⟨ez⟩ := heq (p x) (himage ⟨x, rfl⟩)
  obtain ⟨ex⟩ := hstalk (p x) (p x) (hw (p x))
  exact ⟨(adicResidueRestriction
      (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) B) T).mapIso
        ((commutativeSiteDerivedConstantModuleFunctor.{max v (u + 1), max v (u + 1),
          max v (u + 1), max v (u + 1) + 1}
          (coefficientProEtaleModelTopology.{u, v} X) B).mapIso (ez ≪≫ ex.symm)) ≪≫ et⟩

end AlgebraicGeometry.Scheme
