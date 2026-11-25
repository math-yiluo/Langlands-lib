/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
import WeilConjectures.AlgebraicGeometry.Compactification.GeometricallyConnectedAlgebraicClosure
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Fiber

/-!
# Clopen dimension loci in proper smooth connected families

## References

* Stacks Project, Morphisms, Tags 02G1, 02G2, 02NK, 01W1, 01W4, 01TH
* Varieties, Tags 0387 and 06LH
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- A nonempty smooth connected scheme over a field has one relative dimension.
private theorem connected_smooth_exists_relative_dimension
    {k : Type u} [Field k] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))
    [Smooth g] [ConnectedSpace Y] : ∃ n : ℕ, SmoothOfRelativeDimension n g := by
  have := LocallyOfFiniteType.isLocallyNoetherian g
  have := IsRegular.of_smooth g
  have := IsRegular.isIntegral Y
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  obtain ⟨U, V, -, -, hy, e, n, hn⟩ := Smooth.exists_smoothOfRelativeDimension_resLE g y
  have : Nonempty V := ⟨⟨y, hy⟩⟩
  have : SmoothOfRelativeDimension n (V.ι ≫ g) := by
    rw [← Scheme.Hom.resLE_comp_ι g e]
    have : SmoothOfRelativeDimension (n + 0) (g.resLE U V e ≫ U.ι) := inferInstance
    simpa using this
  refine ⟨n, (smoothOfRelativeDimension_iff_topologicalKrullDim_eq g n).mpr ?_⟩
  exact (topologicalKrullDim_opens_eq g V).symm.trans
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension (V.ι ≫ g) n)

private theorem geometricallyConnected_of_connected_geometric_fibres
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hc : ∀ s : S, ConnectedSpace
      ↥(pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s))) : GeometricallyConnected f := by
  apply (GeometricallyConnected.iff_geometricallyConnected_fiber f).mpr
  intro s
  let := f.fiberOverSpecResidueField s
  apply (geometricallyConnected_iff_connectedSpace_of_isAlgClosed
    (k := S.residueField s) (Ω := AlgebraicClosure (S.residueField s)) (f.fiber s)).mpr
  let e := pullbackLeftPullbackSndIso f (S.fromSpecResidueField s)
    (Spec.map (CommRingCat.ofHom
      (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))))
  exact e.hom.homeomorph.connectedSpace_iff.mpr (hc s)

private theorem fibre_geometric_dimension_eq
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [GeometricallyConnected f] (s : S) :
    ∃ n : ℕ, SmoothOfRelativeDimension n (f.fiberToSpecResidueField s) ∧
      topologicalKrullDim (f.fiber s) = (n : WithBot ℕ∞) ∧
      topologicalKrullDim
        ↥(pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s)) = (n : WithBot ℕ∞) := by
  have : Smooth (f.fiberToSpecResidueField s) :=
    MorphismProperty.pullback_snd f (S.fromSpecResidueField s) inferInstance
  obtain ⟨n, hn⟩ := connected_smooth_exists_relative_dimension (f.fiberToSpecResidueField s)
  have := hn
  refine ⟨n, hn, topologicalKrullDim_eq_of_smoothOfRelativeDimension
    (f.fiberToSpecResidueField s) n, ?_⟩
  let g := Spec.map (CommRingCat.ofHom
    (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s))))
  rw [← IsHomeomorph.topologicalKrullDim_eq _
    (pullbackLeftPullbackSndIso f (S.fromSpecResidueField s) g).hom.homeomorph.isHomeomorph]
  exact topologicalKrullDim_eq_of_smoothOfRelativeDimension
    (pullback.snd (f.fiberToSpecResidueField s) g) n

private theorem smooth_connected_isPureDimension
    {k : Type u} [Field k] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))
    [Smooth g] [ConnectedSpace Y] (n : ℕ)
    (hdim : topologicalKrullDim Y = (n : WithBot ℕ∞)) : Y.IsPureDimension n := by
  have := LocallyOfFiniteType.isLocallyNoetherian g
  have := IsRegular.of_smooth g
  have := IsRegular.irreducibleSpace Y
  intro Z hZ
  have hZeq : Z = Set.univ := by simpa only [irreducibleComponents_eq_singleton,
    Set.mem_singleton_iff] using hZ
  subst Z
  exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y).isHomeomorph).trans
    hdim

/-- The geometric fibre dimension partitions the base of a proper smooth family with
nonempty connected geometric fibres into clopen loci. On each locus the geometric fibres
have the indicated pure dimension, and the dimension-zero family is quasi-finite. -/
theorem proper_smooth_connected_fibre_dimension_loci
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f] [Smooth f]
    (d : ℕ)
    (hconnected : ∀ s : S, ConnectedSpace
      ↥(pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)))
    (hbound : ∀ s : S, topologicalKrullDim
      ↥(pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)) ≤
        (d : WithBot ℕ∞)) :
    ∃ U : Fin (d + 1) → S.Opens,
      (∀ i : Fin (d + 1), (U i : Set S) = {s : S | topologicalKrullDim
        ↥(pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)) =
          (i.val : WithBot ℕ∞)}) ∧
      (∀ i : Fin (d + 1), IsClosed (U i : Set S)) ∧
      Pairwise (fun i j : Fin (d + 1) ↦ Disjoint (U i : Set S) (U j : Set S)) ∧
      (⨆ i : Fin (d + 1), U i) = ⊤ ∧
      (∀ i : Fin (d + 1),
        IsProper (pullback.snd f (U i).ι) ∧ Smooth (pullback.snd f (U i).ι) ∧
        ∀ s : (U i).toScheme,
          Nonempty ((pullback.snd f (U i).ι).fiber s) ∧
          GeometricallyConnected ((pullback.snd f (U i).ι).fiberToSpecResidueField s) ∧
          (pullback (pullback.snd f (U i).ι)
            (Spec.map (CommRingCat.ofHom (algebraMap ((U i).toScheme.residueField s)
              (AlgebraicClosure ((U i).toScheme.residueField s)))) ≫
                (U i).toScheme.fromSpecResidueField s)).IsPureDimension i.val) ∧
      (pullback.snd f (U 0).ι).IsQuasiFinite := by
  classical
  have := geometricallyConnected_of_connected_geometric_fibres f hconnected
  let D : S → WithBot ℕ∞ := fun s ↦ topologicalKrullDim
    ↥(pullback f (Spec.map (CommRingCat.ofHom
      (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
        S.fromSpecResidueField s))
  have hDf (x : X) : D (f x) = topologicalKrullDimAt (f.asFiber x) := by
    obtain ⟨n, hn, -, hg⟩ := fibre_geometric_dimension_eq f (f x)
    have := hn
    exact hg.trans (topologicalKrullDimAt_eq_of_smoothOfRelativeDimension
      (f.fiberToSpecResidueField (f x)) n (f.asFiber x)).symm
  have hD : IsLocallyConstant D := by
    intro A
    have hq := (f.isClosedMap.isQuotientMap f.continuous f.surjective).isCoinducing
    apply hq.isOpen_preimage.mp
    change IsOpen ((fun x : X ↦ D (f x)) ⁻¹' A)
    simpa only [hDf] using Smooth.isLocallyConstant_topologicalKrullDimAt_asFiber f A
  let U : Fin (d + 1) → S.Opens := fun i ↦
    ⟨{s | D s = (i.val : WithBot ℕ∞)}, hD.isOpen_fiber _⟩
  have hrel (i : Fin (d + 1)) : SmoothOfRelativeDimension i.val
      (pullback.snd f (U i).ι) := by
    apply smoothOfRelativeDimension_of_fiberToSpecResidueField
    intro s
    obtain ⟨n, hn, hord, -⟩ := fibre_geometric_dimension_eq
      (pullback.snd f (U i).ι) s
    obtain ⟨m, -, hm, hgm⟩ := fibre_geometric_dimension_eq f ((U i).ι s)
    have hi : D ((U i).ι s) = (i.val : WithBot ℕ∞) := s.property
    have hnval : (n : WithBot ℕ∞) = (i.val : WithBot ℕ∞) :=
      hord.symm.trans ((topologicalKrullDim_fiber_of_isPullback
        (IsPullback.of_hasPullback f (U i).ι) s).trans (hm.trans (hgm.symm.trans hi)))
    have hni : n = i.val := by exact_mod_cast hnval
    exact hni ▸ hn
  refine ⟨U, fun _ ↦ rfl, fun i ↦ hD.isClosed_fiber _, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro s hi hj
    have heq : (i.val : WithBot ℕ∞) = (j.val : WithBot ℕ∞) := hi.symm.trans hj
    have : i.val = j.val := by exact_mod_cast heq
    exact hij (Fin.ext this)
  · apply top_unique
    intro s _
    obtain ⟨n, -, -, hn⟩ := fibre_geometric_dimension_eq f s
    have hnle : n ≤ d := by exact_mod_cast (hn ▸ hbound s)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨n, Nat.lt_succ_of_le hnle⟩, hn⟩
  · intro i
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro s
    refine ⟨inferInstance, inferInstance, ?_⟩
    have := hrel i
    let g := pullback.snd f (U i).ι
    let p := Spec.map (CommRingCat.ofHom
      (algebraMap ((U i).toScheme.residueField s)
        (AlgebraicClosure ((U i).toScheme.residueField s)))) ≫
          (U i).toScheme.fromSpecResidueField s
    have : ConnectedSpace ↥(pullback g p) :=
      GeometricallyConnected.geometrically_connectedSpace p _ _
        (IsPullback.of_hasPullback _ _)
    exact smooth_connected_isPureDimension (pullback.snd g p) i.val
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension (pullback.snd g p) i.val)
  · have : SmoothOfRelativeDimension 0 (pullback.snd f (U 0).ι) := by
      simpa using hrel 0
    have : Etale (pullback.snd f (U 0).ι) :=
      (Etale.iff_smoothOfRelativeDimension_zero (pullback.snd f (U 0).ι)).mpr inferInstance
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro x
    exact isOpen_discrete _

end AlgebraicGeometry
