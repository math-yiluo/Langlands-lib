/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.CohenMacaulayFlatQuasiFiniteChart
import WeilConjectures.AlgebraicGeometry.FlatQuasiFiniteSmoothDimension

/-! # Constant dimension neighbourhoods in a Cohen-Macaulay family

Source: Stacks Project, Tags 00RH and 0A21 (10); the local step underlying 02NM.
(blueprint: lem-sbc-cohen-macaulay-fibre-dimension-neighbourhood)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem fibre_dimension_eq_of_flat_quasiFinite_chart
    {V P T : Scheme.{u}} (h : V ⟶ P) (g : P ⟶ T) (n : ℕ)
    [Flat h] [LocallyQuasiFinite h] [LocallyOfFinitePresentation h]
    [SmoothOfRelativeDimension n g] (x : V) :
    topologicalKrullDimAt ((h ≫ g).asFiber x) = (n : WithBot ℕ∞) := by
  let t := (h ≫ g) x
  let q : (h ≫ g).fiber t ⟶ g.fiber t :=
    Limits.pullback.lift ((h ≫ g).fiberι t ≫ h)
      ((h ≫ g).fiberToSpecResidueField t) (by simp [Scheme.Hom.fiber_fac])
  have hq : q ≫ g.fiberι t = (h ≫ g).fiberι t ≫ h := by
    simp [q, Scheme.Hom.fiberι]
  have hqt : q ≫ g.fiberToSpecResidueField t =
      (h ≫ g).fiberToSpecResidueField t := by
    simp [q, Scheme.Hom.fiberToSpecResidueField]
  have hpb : IsPullback q ((h ≫ g).fiberι t) (g.fiberι t) h := by
    apply IsPullback.of_right (h₁₂ := g.fiberToSpecResidueField t) _ hq
      (IsPullback.of_hasPullback g (T.fromSpecResidueField t)).flip
    rw [hqt]
    exact (IsPullback.of_hasPullback (h ≫ g) (T.fromSpecResidueField t)).flip
  have : Flat q := MorphismProperty.of_isPullback hpb.flip inferInstance
  have : LocallyQuasiFinite q := MorphismProperty.of_isPullback hpb.flip inferInstance
  have : LocallyOfFinitePresentation q :=
    MorphismProperty.of_isPullback hpb.flip inferInstance
  have : SmoothOfRelativeDimension n (g.fiberToSpecResidueField t) := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := n)
    exact MorphismProperty.pullback_snd _ _ inferInstance
  exact topologicalKrullDimAt_eq_of_flat_quasiFinite_to_smooth
    q (g.fiberToSpecResidueField t) n ((h ≫ g).asFiber x)

set_option backward.isDefEq.respectTransparency false in
private theorem fibre_dimension_open_immersion
    {V X T : Scheme.{u}} (i : V ⟶ X) [IsOpenImmersion i] (f : X ⟶ T) (x : V) :
    topologicalKrullDimAt ((i ≫ f).asFiber x) =
      topologicalKrullDimAt (f.asFiber (i x)) := by
  let q : (i ≫ f).fiber ((i ≫ f) x) ⟶ f.fiber (f (i x)) :=
    Limits.pullback.map (i ≫ f) (T.fromSpecResidueField (f (i x))) f
      (T.fromSpecResidueField (f (i x))) i (𝟙 _) (𝟙 _) (by simp) (by simp)
  have : IsOpenImmersion q :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance rfl (by simp)
  have hpoint : q ((i ≫ f).asFiber x) = f.asFiber (i x) := by
    apply (f.fiberι _).isEmbedding.injective
    have hfst : q ≫ f.fiberι _ = (i ≫ f).fiberι _ ≫ i := by
      simp [q, Scheme.Hom.fiberι]
    have hh := congrArg
      (fun a : (i ≫ f).fiber ((i ≫ f) x) ⟶ X ↦ a ((i ≫ f).asFiber x)) hfst
    simpa only [Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber] using hh
  rw [← hpoint]
  apply le_antisymm
  · refine le_iInf₂ fun U hx ↦ ?_
    let V : TopologicalSpace.Opens ((i ≫ f).fiber ((i ≫ f) x)) :=
      ⟨q ⁻¹' U, U.isOpen.preimage q.continuous⟩
    let a : V → U := fun z ↦ ⟨q z, z.2⟩
    have ha : IsInducing a :=
      .of_comp (g := Subtype.val) (by fun_prop) continuous_subtype_val
        (q.isOpenEmbedding.toIsEmbedding.toIsInducing.comp IsInducing.subtypeVal)
    exact (iInf₂_le V hx).trans ha.topologicalKrullDim_le
  · refine le_iInf₂ fun U hx ↦ ?_
    let V : TopologicalSpace.Opens (f.fiber (f (i x))) :=
      ⟨q '' U, q.isOpenEmbedding.isOpenMap _ U.isOpen⟩
    refine (iInf₂_le V ⟨_, hx, rfl⟩).trans ?_
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (q.isOpenEmbedding.toIsEmbedding.homeomorphImage (U : Set _)).symm.isHomeomorph).le

/-- Local fibre dimension is a finite constant near each point of the given open.

Source: Stacks Project, Tags 00RH and 0A21 (10); the local step underlying 02NM.
Proof: Work in the source open W intersected with the inverse image of U.
Choose affine neighbourhoods of f(y) in U and y in this source open. Their ring
map R to S is flat and finitely presented. The fibre local ring at the prime q
of y is the given fibre stalk, so hdepth makes it Cohen-Macaulay. Its local
relative dimension n is a natural number, since the fibre is locally of finite
type over a field. Tag 0A21 (10) identifies this relative dimension with local
topological fibre dimension. The proof of Tag 00RH gives an open neighbourhood
of q where that relative dimension is n: after a principal shrinking choose a
quasi-finite map R[t_1,...,t_n] to S. On the fibre its target local ring is
Cohen-Macaulay and its source is regular, so the fibre map is flat (00RE).
Fibrewise flatness (00R7) gives flatness of the polynomial map at q. Openness
of flatness (00RC) gives a further principal shrinking on which it is flat.
At every point of this shrinking, base change makes the corresponding fibre
map flat and quasi-finite over polynomial n-space. The local dimension formula
therefore gives relative dimension n at every point (again 00RE).
The image O of this principal affine open is open in X, contains y, and lies
in W. Open fibre inclusions and the residue-field restriction isomorphisms
preserve local topological dimension, giving the equality for all z in O.
Only the fibre stalk at y is assumed Cohen-Macaulay; no partition is used.
(blueprint: lem-sbc-cohen-macaulay-fibre-dimension-neighbourhood) -/
theorem exists_constant_fibre_dimension_neighbourhood_of_depth_eq_ringKrullDim
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)] (W : X.Opens)
    (y : X) (hy : y ∈ W) (ht : f y ∈ U)
    (hdepth :
      (IsLocalRing.depth (R := (f.fiber (f y)).presheaf.stalk (f.asFiber y))
        ((f.fiber (f y)).presheaf.stalk (f.asFiber y)) : WithBot ℕ∞) =
          ringKrullDim ((f.fiber (f y)).presheaf.stalk (f.asFiber y))) :
    ∃ (n : ℕ) (O : X.Opens), y ∈ O ∧ O ≤ W ∧
      ∀ z ∈ O, topologicalKrullDimAt (f.asFiber z) = (n : WithBot ℕ∞) := by
  obtain ⟨n, V, P, h, g, hyV, hh, hq, hfp, hg, hfac⟩ :=
    exists_flat_quasiFinite_chart_of_fibre_depth_eq_ringKrullDim f U y ht hdepth
  have : Flat h := hh
  have : LocallyQuasiFinite h := hq
  have : LocallyOfFinitePresentation h := hfp
  have : SmoothOfRelativeDimension n g := hg
  refine ⟨n, V ⊓ W, ⟨hyV, hy⟩, inf_le_right, ?_⟩
  intro z hz
  let zV : V.toScheme := ⟨z, hz.1⟩
  have hdim := fibre_dimension_eq_of_flat_quasiFinite_chart h g n zV
  rw [hfac] at hdim
  exact (fibre_dimension_open_immersion V.ι f zV).symm.trans hdim

end AlgebraicGeometry
