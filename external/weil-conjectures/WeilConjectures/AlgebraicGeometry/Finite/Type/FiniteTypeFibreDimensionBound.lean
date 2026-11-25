/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart.CoordinateFibreDimension
import WeilConjectures.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairs
import WeilConjectures.Topology.DimensionSupremumLocalDimensions

/-!
# Uniform dimension bound for fibres of a finite-type morphism

Source: Stacks Project, Morphisms, Tag 0A3V,
lemma-morphism-finite-type-bounded-dimension
(blueprint: lem-fin-finite-type-fibre-dimension-bound).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem dimensionAt_openEmbedding {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] {g : A → B}
    (hg : Topology.IsOpenEmbedding g) (a : A) :
    topologicalKrullDimAt a = topologicalKrullDimAt (g a) := by
  let e := hg.isEmbedding.toHomeomorph
  have hle : topologicalKrullDimAt a ≤ topologicalKrullDimAt (e a) := by
    refine le_iInf₂ fun U ha ↦ ?_
    let V : TopologicalSpace.Opens A :=
      ⟨e ⁻¹' U, U.isOpen.preimage e.continuous⟩
    exact (iInf₂_le V ha).trans
      ((e.isEmbedding.toIsInducing.restrictPreimage
        (U : Set (Set.range g))).topologicalKrullDim_le)
  have hge : topologicalKrullDimAt (e a) ≤ topologicalKrullDimAt a := by
    refine le_iInf₂ fun U ha ↦ ?_
    let V : TopologicalSpace.Opens (Set.range g) :=
      ⟨e.symm ⁻¹' U, U.isOpen.preimage e.symm.continuous⟩
    exact (iInf₂_le V (by simpa [V] using ha)).trans
      ((e.symm.isEmbedding.toIsInducing.restrictPreimage (U : Set A)).topologicalKrullDim_le)
  exact hle.antisymm hge |>.trans
    (hg.isOpen_range.topologicalKrullDimAt_eq (Set.mem_range_self a))

private theorem fibre_dimension_target_open_immersion
    {X Y T : Scheme.{u}} (f : X ⟶ Y) (j : Y ⟶ T) [IsOpenImmersion j] (x : X) :
    topologicalKrullDimAt (f.asFiber x) =
      topologicalKrullDimAt ((f ≫ j).asFiber x) := by
  have hsets : f ⁻¹' {f x} = (f ≫ j) ⁻¹' {(f ≫ j) x} := by
    ext z
    exact j.isEmbedding.injective.eq_iff.symm
  let e := (f.fiberHomeo (f x)).trans
    ((Homeomorph.setCongr hsets).trans ((f ≫ j).fiberHomeo ((f ≫ j) x)).symm)
  have hp : e (f.asFiber x) = (f ≫ j).asFiber x := by
    apply ((f ≫ j).fiberHomeo _).injective
    simp [e, Scheme.Hom.asFiber]
    rfl
  have hle : topologicalKrullDimAt (f.asFiber x) ≤
      topologicalKrullDimAt (e (f.asFiber x)) := by
    refine le_iInf₂ fun U ha ↦ ?_
    let V : TopologicalSpace.Opens (f.fiber (f x)) :=
      ⟨e ⁻¹' (U : Set ((f ≫ j).fiber ((f ≫ j) x))),
        U.isOpen.preimage e.continuous⟩
    exact (iInf₂_le V ha).trans
      ((e.isEmbedding.toIsInducing.restrictPreimage (U : Set _)).topologicalKrullDim_le)
  have hge : topologicalKrullDimAt (e (f.asFiber x)) ≤
      topologicalKrullDimAt (f.asFiber x) := by
    refine le_iInf₂ fun U ha ↦ ?_
    let V : TopologicalSpace.Opens ((f ≫ j).fiber ((f ≫ j) x)) :=
      ⟨e.symm ⁻¹' (U : Set (f.fiber (f x))), U.isOpen.preimage e.symm.continuous⟩
    exact (iInf₂_le V (by simpa [V] using ha)).trans
      ((e.symm.isEmbedding.toIsInducing.restrictPreimage
        (U : Set (f.fiber (f x)))).topologicalKrullDim_le)
  exact hle.antisymm hge |>.trans (congrArg _ hp)

private theorem fibre_dimension_resLE
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (U : X.Opens)
    (hUV : U ≤ f ⁻¹ᵁ V) (x : U.toScheme) :
    topologicalKrullDimAt ((f.resLE V U hUV).asFiber x) =
      topologicalKrullDimAt (f.asFiber (U.ι x)) := by
  rw [fibre_dimension_target_open_immersion (f.resLE V U hUV) V.ι x,
    Scheme.Hom.resLE_comp_ι]
  let i := U.ι
  let q : (i ≫ f).fiber ((i ≫ f) x) ⟶ f.fiber (f (i x)) :=
    Limits.pullback.map (i ≫ f) (Y.fromSpecResidueField (f (i x))) f
      (Y.fromSpecResidueField (f (i x))) i (𝟙 _) (𝟙 _) (by simp) (by simp)
  have : IsOpenImmersion q :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance rfl (by simp)
  have hpoint : q ((i ≫ f).asFiber x) = f.asFiber (i x) := by
    apply (f.fiberι _).isEmbedding.injective
    have hfst : q ≫ f.fiberι _ = (i ≫ f).fiberι _ ≫ i := by
      simp [q, Scheme.Hom.fiberι]
    have hh := congrArg
      (fun a : (i ≫ f).fiber ((i ≫ f) x) ⟶ X ↦ a ((i ≫ f).asFiber x)) hfst
    simpa only [Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber] using hh
  exact (dimensionAt_openEmbedding q.isOpenEmbedding _).trans (congrArg _ hpoint)

/-- A finite local fibre dimension bounds the local fibre dimension on a neighbourhood.

Source: Stacks Project, Morphisms, Tag 02FZ, affine reduction to Algebra Tag 00QH.
(blueprint: lem-weil-pbc-bounded-local-fibre-dimension-neighbourhood)

Proof: choose affine neighbourhoods of `f x` and `x` and restrict `f` to them. The
restricted coordinate-ring map is finite type. Open immersions on source and target
preserve local fibre dimension, so the affine coordinate fibre comparison identifies
the dimension at the coordinate prime of `x` with `d`. Apply the bounded-open-upstairs
lemma to that prime. Pull its open neighbourhood back along the affine isomorphism
and include it into `X`. At every point of this neighbourhood the same restriction
and affine comparisons transport the coordinate bound to the required fibre bound. -/
theorem exists_bounded_fibre_dimension_neighbourhood
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : X) (d : ℕ) (hd : topologicalKrullDimAt (f.asFiber x) = (d : WithBot ℕ∞)) :
    ∃ W : X.Opens, x ∈ W ∧
      ∀ z ∈ W, topologicalKrullDimAt (f.asFiber z) ≤ (d : WithBot ℕ∞) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV (f ⁻¹ᵁ V).isOpen
  let U : X.Opens := U
  let V : Y.Opens := V
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  let g := f.resLE V U hUV
  let : Algebra Γ(V.toScheme, ⊤) Γ(U.toScheme, ⊤) := g.appTop.hom.toAlgebra
  have : Algebra.FiniteType Γ(V.toScheme, ⊤) Γ(U.toScheme, ⊤) :=
    HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType).mp inferInstance
  let a : U.toScheme := ⟨x, hxU⟩
  let q : PrimeSpectrum Γ(U.toScheme, ⊤) := U.toScheme.isoSpec.hom a
  have hcoord (z : U.toScheme) := affine_coordinate_fibre_dimension_eq g z
  have hdim : topologicalKrullDimAt
      (PrimeSpectrum.preimageEquivFiber Γ(V.toScheme, ⊤) Γ(U.toScheme, ⊤)
        (PrimeSpectrum.comap (algebraMap Γ(V.toScheme, ⊤) Γ(U.toScheme, ⊤)) q)
        ⟨q, rfl⟩) = (d : WithBot ℕ∞) := by
    exact (hcoord a).symm.trans ((fibre_dimension_resLE f V U hUV a).trans hd)
  obtain ⟨O, hO, hqO, hbound⟩ := Algebra.fibre_dimension_bounded_open_upstairs q d hdim
  let O' : U.toScheme.Opens := ⟨U.toScheme.isoSpec.hom ⁻¹' O,
    hO.preimage U.toScheme.isoSpec.hom.continuous⟩
  refine ⟨U.ι ''ᵁ O', ?_, ?_⟩
  · exact ⟨a, hqO, rfl⟩
  · intro z hz
    obtain ⟨z', hz', rfl⟩ := hz
    have hb := hbound _ hz'
    exact (fibre_dimension_resLE f V U hUV z').ge.trans
      ((hcoord z').le.trans hb)

/-- A finite-type morphism with quasi-compact target has a uniform finite bound on the
Krull dimensions of its scheme-theoretic fibres, including empty fibres of dimension bottom.

Source: Stacks Project, Morphisms, Tag 0A3V,
lemma-morphism-finite-type-bounded-dimension.
(blueprint: lem-fin-finite-type-fibre-dimension-bound)

Proof:
1. Quasi-compactness of f and Y gives quasi-compactness of X by
   `lem-weil-pbc-quasi-compact-morphism-preimage-qc-open`.
2. Each whole fibre is quasi-compact and locally of finite type over its residue field.
   Apply `lem-kun-dimension-finite-type` to bound its dimension by a natural number.
   The local dimension e(x) at the point over x is at most this bound and is nonnegative:
   every neighbourhood contains x and hence the irreducible closed subset given by its
   singleton closure. Thus e(x) is itself a natural number.
3. Choose affine neighbourhoods U of x and V of f(x), with U contained in f⁻¹(V).
   Restricting the source induces an open immersion on fibres, and restricting the target
   leaves the set-theoretic fibre unchanged. Homeomorphism invariance and
   `lem-weil-pbc-dimension-at-point-open-subspace` identify local dimensions with those
   for U → V. Now `lem-sbc-affine-coordinate-fibre-dimension` and
   `lem-weil-pbc-fibre-dimension-bounded-open-upstairs` give an open neighbourhood W(x)
   of x on which all local fibre dimensions are at most e(x).
4. A finite collection of the W(x) covers X. Take the maximum d of its bounds, using
   zero for an empty collection. Every local dimension in every fibre is at most d.
   Apply `lem-weil-pbc-dimension-supremum-local-dimensions` to bound its global dimension.
   This also covers empty fibres, whose empty supremum is bottom. -/
theorem exists_fibre_dimension_bound {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [CompactSpace Y] :
    ∃ d : ℕ, ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hfinite (x : X) : ∃ d : ℕ,
      topologicalKrullDimAt (f.asFiber x) = (d : WithBot ℕ∞) := by
    have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) := by
      dsimp [Scheme.Hom.fiberToSpecResidueField]
      infer_instance
    have : QuasiCompact (f.fiberToSpecResidueField (f x)) := by
      dsimp [Scheme.Hom.fiberToSpecResidueField]
      infer_instance
    obtain ⟨n, hn⟩ := exists_topologicalKrullDim_le (f.fiberToSpecResidueField (f x))
    have hle : topologicalKrullDimAt (f.asFiber x) ≤ (n : WithBot ℕ∞) :=
      ((iInf₂_le ⊤ trivial).trans
        (topologicalKrullDim_subspace_le (f.fiber (f x)) Set.univ)).trans hn
    have hnonneg : 0 ≤ topologicalKrullDimAt (f.asFiber x) := by
      refine le_iInf₂ fun U hx ↦ ?_
      apply Order.krullDim_nonneg_iff.mpr
      exact ⟨⟨closure {⟨f.asFiber x, hx⟩}, isIrreducible_singleton.closure,
        isClosed_closure⟩⟩
    generalize topologicalKrullDimAt (f.asFiber x) = e at hle hnonneg ⊢
    induction e using WithBot.recBotCoe with
    | bot => exact False.elim ((not_le_of_gt (by decide : (⊥ : WithBot ℕ∞) < 0)) hnonneg)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        exact False.elim ((not_le_of_gt
          (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top n))) hle)
      | coe e => exact ⟨e, rfl⟩
  have hneighbourhood (x : X) : ∃ (d : ℕ) (W : X.Opens), x ∈ W ∧
      ∀ z ∈ W, topologicalKrullDimAt (f.asFiber z) ≤ (d : WithBot ℕ∞) := by
    obtain ⟨d, hd⟩ := hfinite x
    obtain ⟨W, hxW, hW⟩ := exists_bounded_fibre_dimension_neighbourhood f x d hd
    exact ⟨d, W, hxW, hW⟩
  choose d W hmem hbound using hneighbourhood
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ (W x : Set X)) (fun x ↦ (W x).isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hmem x⟩)
  refine ⟨s.sup d, fun y ↦ ?_⟩
  rw [topologicalKrullDim_eq_iSup_topologicalKrullDimAt]
  refine iSup_le fun z ↦ ?_
  generalize hxdef : f.fiberι y z = x
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  have hx := hbound a x hxa
  have heq : topologicalKrullDimAt z = topologicalKrullDimAt (f.asFiber x) := by
    have hxy : f x = y := by
      rw [← hxdef]
      exact (f.fiberHomeo y z).2
    subst y
    congr 1
    apply (f.fiberι _).isEmbedding.injective
    simpa using hxdef
  rw [heq]
  exact hx.trans (by exact_mod_cast Finset.le_sup (f := d) ha)

end AlgebraicGeometry
