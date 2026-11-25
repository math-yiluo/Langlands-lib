/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.BaseChange
import WeilConjectures.AlgebraicGeometry.Compactification.GeometricallyConnectedAlgebraicClosure
import WeilConjectures.AlgebraicGeometry.Flat.FlatProperComponentCountLowerSemicontinuous
import WeilConjectures.AlgebraicGeometry.Proper.ProperReducedGlobalSectionsProduct

/-!
# Geometric component counts in proper smooth families

## References

* Stacks Project, Tag 0E0N, specialized to smooth morphisms
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem finrankH_unit_eq_card_components
    (k : Type u) [Field k] [IsAlgClosed k] (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of k))]
    [IsProper (Y ↘ Spec (CommRingCat.of k))] [IsReduced Y] :
    Scheme.Modules.finrankH k (X := Y) (SheafOfModules.unit Y.ringCatSheaf) 0 =
      Nat.card (ConnectedComponents Y) := by
  obtain ⟨hfin, _, ⟨e, he, _⟩, _⟩ := Scheme.proper_reduced_globalSections_product k Y
  have : Finite (ConnectedComponents Y) := hfin
  let M := SheafOfModules.unit Y.ringCatSheaf
  let e₀ := Scheme.Modules.H.zeroLinearEquiv M
  let e₁ : (ConnectedComponents Y → k) ≃ₗ[k] Scheme.Modules.H (X := Y) M 0 :=
    { e.toAddEquiv.trans e₀.symm.toAddEquiv with
      map_smul' := fun c a ↦ by
        change e₀.symm (e (c • a)) = c • e₀.symm (e a)
        rw [Scheme.Modules.smul_H_eq_globalSectionsRingHom_smul,
          ← e₀.symm.map_smul]
        congr 1
        change e ((fun _ ↦ c) * a) = Scheme.globalSectionsRingHom k c * e a
        rw [map_mul, he]
        rfl }
  classical
  let : Fintype (ConnectedComponents Y) := Fintype.ofFinite _
  exact e₁.finrank_eq.symm.trans (by simp [Nat.card_eq_fintype_card])

private theorem connectedSpace_iff_card_components_eq_one
    (Y : Type*) [TopologicalSpace Y] :
    ConnectedSpace Y ↔ Nat.card (ConnectedComponents Y) = 1 := by
  constructor
  · intro h
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  · intro h
    obtain ⟨hsub, hnon⟩ := Nat.card_eq_one_iff_unique.mp h
    have : Subsingleton (ConnectedComponents Y) := hsub
    obtain ⟨y⟩ := ConnectedComponents.nonempty_iff_nonempty.mp hnon
    apply connectedSpace_iff_connectedComponent.mpr
    refine ⟨y, Set.eq_univ_of_forall fun z ↦ ?_⟩
    exact ConnectedComponents.coe_eq_coe'.mp (Subsingleton.elim _ _)

private theorem geometricallyConnected_fiber_iff_connectedSpace
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    GeometricallyConnected (f.fiberToSpecResidueField s) ↔
      ConnectedSpace ↥(pullback f
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s)) := by
  let := f.fiberOverSpecResidueField s
  have h := geometricallyConnected_iff_connectedSpace_of_isAlgClosed
    (k := S.residueField s) (Ω := AlgebraicClosure (S.residueField s)) (f.fiber s)
  exact h.trans (Homeomorph.connectedSpace_iff
    (pullbackLeftPullbackSndIso f (S.fromSpecResidueField s)
    (Spec.map (CommRingCat.ofHom
      (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))))).hom.homeomorph)

private theorem hFiber_unit_eq_card_geometric_components
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] (s : S) :
    Scheme.Modules.hFiber (X := X) (SheafOfModules.unit X.ringCatSheaf) f 0 s =
      Nat.card (ConnectedComponents ↥(pullback f
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s))) := by
  let K := AlgebraicClosure (S.residueField s)
  let y : Spec (.of K) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K)) ≫
      S.fromSpecResidueField s
  let Y := pullback f y
  let : Y.Over (Spec (.of K)) := ⟨pullback.snd f y⟩
  have : IsProper (Y ↘ Spec (.of K)) := inferInstanceAs (IsProper (pullback.snd f y))
  have : IsReduced Y := isReduced_of_smooth (pullback.snd f y)
  obtain ⟨p⟩ : Nonempty (Spec (.of K)) := inferInstance
  have : (SheafOfModules.unit X.ringCatSheaf).IsInvertible :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  have : (SheafOfModules.unit X.ringCatSheaf).IsFiniteLocallyFree :=
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
  have : (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have h := Scheme.Modules.hFiber_pullback_of_isPullback f (SheafOfModules.unit X.ringCatSheaf)
    y (pullback.fst f y) (pullback.snd f y) (IsPullback.of_hasPullback f y) 0 p
  rw [Scheme.Modules.hFiber_eq_finrankH, Scheme.Hom.comp_apply] at h
  have hp : y.base p = s := S.fromSpecResidueField_apply s _
  change _ = Scheme.Modules.hFiber (SheafOfModules.unit X.ringCatSheaf) f 0 (y.base p) at h
  rw [hp] at h
  rw [← h]
  exact (Scheme.Modules.finrankH_congr K
    (Scheme.Modules.pullbackObjUnitIso (pullback.fst f y)) 0).trans
    (finrankH_unit_eq_card_components K Y)

/-- In a proper smooth family the geometric connected component count is finite and locally
constant, vanishes for empty fibres, and geometric connectedness persists near any point where
it holds. -/
theorem proper_smooth_geometric_components_locally_constant
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] :
    (∀ s : S, Finite (ConnectedComponents ↥(pullback f
      (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)))) ∧
    IsLocallyConstant (fun s : S ↦ Nat.card (ConnectedComponents ↥(pullback f
      (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)))) ∧
    (∀ s : S, IsEmpty ↥(pullback f
      (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)) →
      Nat.card (ConnectedComponents ↥(pullback f
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s))) = 0) ∧
    (∀ s : S, GeometricallyConnected (f.fiberToSpecResidueField s) →
      ∃ U : S.Opens, s ∈ U ∧
        ∀ t : S, t ∈ U → GeometricallyConnected (f.fiberToSpecResidueField t)) := by
  obtain ⟨n, hn, hempty, hlower⟩ := f.geometricComponentCount_lowerSemicontinuous
  have hnβ (s : S) :
      n s = Scheme.Modules.hFiber (X := X) (SheafOfModules.unit X.ringCatSheaf) f 0 s :=
    (hn s).2.trans (hFiber_unit_eq_card_geometric_components f s).symm
  have := Scheme.Modules.isGrothendieckAbelian X
  have : (SheafOfModules.unit X.ringCatSheaf).IsInvertible :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  have : (SheafOfModules.unit X.ringCatSheaf).IsFiniteLocallyFree :=
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
  have : (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have hupper : UpperSemicontinuous n := by
    have h := Scheme.Modules.upperSemicontinuous_hFiber f (SheafOfModules.unit X.ringCatSheaf)
      (Scheme.Modules.isFlatOver_of_isInvertible f _) 0
    have heq : n =
        Scheme.Modules.hFiber (X := X) (SheafOfModules.unit X.ringCatSheaf) f 0 := funext hnβ
    rwa [← heq] at h
  have hlocal : IsLocallyConstant n := by
    apply (IsLocallyConstant.iff_exists_open n).mpr
    intro s
    obtain ⟨V, hsV, hV⟩ := hlower s
    let W : S.Opens := ⟨{t | n t < n s + 1}, hupper.isOpen_preimage _⟩
    refine ⟨(V ⊓ W : S.Opens), (V ⊓ W).isOpen, ⟨hsV, Nat.lt_succ_self _⟩, ?_⟩
    intro t ht
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp ht.2) (hV t ht.1)
  refine ⟨fun s ↦ (hn s).1, ?_, ?_, ?_⟩
  · have heq : n = fun s ↦ Nat.card (ConnectedComponents ↥(pullback f
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s))) := funext fun s ↦ (hn s).2
    rwa [← heq]
  · intro s hs
    rw [← (hn s).2]
    exact hempty s hs
  · intro s hs
    have hgc (t : S) : GeometricallyConnected (f.fiberToSpecResidueField t) ↔ n t = 1 := by
      rw [(hn t).2]
      exact (geometricallyConnected_fiber_iff_connectedSpace f t).trans
        (connectedSpace_iff_card_components_eq_one _)
    refine ⟨⟨{t | n t = n s}, hlocal.isOpen_fiber _⟩, rfl, ?_⟩
    intro t ht
    exact (hgc t).mpr (ht.trans ((hgc s).mp hs))

end AlgebraicGeometry
