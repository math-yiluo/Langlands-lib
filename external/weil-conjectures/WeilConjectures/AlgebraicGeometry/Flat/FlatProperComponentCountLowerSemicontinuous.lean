/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricComponentCountBaseChange
import WeilConjectures.AlgebraicGeometry.Proper.Geometric.ProperGeometricFibreClopenPartition

/-!
# Lower semicontinuity of geometric connected component counts

Source: Stacks Project, More on Morphisms, Tag 0BUI,
`lemma-proper-flat-nr-geom-conn-comps-lower-semicontinuous`
(blueprint: lem-weil-pbc-flat-proper-component-count-lower-semicontinuous).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem finite_geometricComponents {X S : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] (s : S) :
    Finite (ConnectedComponents (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
        (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s) : Scheme.{u})) := by
  let y := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
    (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s
  have : IsLocallyNoetherian (pullback f y) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f y)
  have : IsNoetherian (pullback f y) := ⟨⟩
  exact inferInstanceAs (Finite (ConnectedComponents ↥(pullback f y)))

private theorem natCard_geometricComponents_baseChange {X S U : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] (g : U ⟶ S) (u : U) :
    Nat.card (ConnectedComponents (pullback (pullback.snd f g)
      (Spec.map (CommRingCat.ofHom (algebraMap (U.residueField u)
        (AlgebraicClosure (U.residueField u)))) ≫ U.fromSpecResidueField u) : Scheme.{u})) =
    Nat.card (ConnectedComponents (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField (g u))
        (AlgebraicClosure (S.residueField (g u))))) ≫
          S.fromSpecResidueField (g u)) : Scheme.{u})) := by
  have := finite_geometricComponents (pullback.snd f g) u
  have := finite_geometricComponents f (g u)
  let := Fintype.ofFinite (ConnectedComponents (pullback (pullback.snd f g)
    (Spec.map (CommRingCat.ofHom (algebraMap (U.residueField u)
      (AlgebraicClosure (U.residueField u)))) ≫ U.fromSpecResidueField u) : Scheme.{u}))
  let := Fintype.ofFinite (ConnectedComponents (pullback f
    (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField (g u))
      (AlgebraicClosure (S.residueField (g u))))) ≫
        S.fromSpecResidueField (g u)) : Scheme.{u}))
  have h := (geometricComponentCount_baseChange f).2 U g u
    (AlgebraicClosure (S.residueField (g u))) (AlgebraicClosure (U.residueField u))
    (CommRingCat.ofHom (algebraMap (S.residueField (g u))
      (AlgebraicClosure (S.residueField (g u)))))
    (CommRingCat.ofHom (algebraMap (U.residueField u) (AlgebraicClosure (U.residueField u))))
  simpa only [ENat.card_eq_coe_fintype_card, ENat.natCast_inj,
    Nat.card_eq_fintype_card] using h

private theorem card_le_of_clopen_partition {Y : Type*} [TopologicalSpace Y]
    [Finite (ConnectedComponents Y)] {m : ℕ} (C : Fin m → Set Y)
    (hcl : ∀ i, IsClopen (C i)) (hd : Pairwise (fun i j ↦ Disjoint (C i) (C j)))
    (hcov : ⋃ i, C i = Set.univ) (hne : ∀ i, (C i).Nonempty) :
    m ≤ Nat.card (ConnectedComponents Y) := by
  classical
  let e := ConnectedComponents.equivOfIsClopen hcl hd hcov
  let a : Fin m → ConnectedComponents Y :=
    fun i ↦ e.symm ⟨i, ConnectedComponents.mk ⟨(hne i).choose, (hne i).choose_spec⟩⟩
  have ha : Function.Injective a := by
    intro i j h
    exact congrArg Sigma.fst (e.symm.injective h)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective a ha

/-- Source: Stacks Project, More on Morphisms, Tag 0BUI.
(blueprint: lem-weil-pbc-flat-proper-component-count-lower-semicontinuous)

The geometric fibres of a proper flat finitely presented morphism have finitely many
connected components. Their count is zero for an empty fibre and is lower semicontinuous,
expressed by the neighbourhood inequality. The function `n` is specified by `Nat.card` of
`ConnectedComponents`, the quotient by equality of maximal connected subsets.
Properness already implies quasi-compactness and quasi-separatedness, so finite
presentation is expressed by the remaining locally-of-finite-presentation condition.

Proof:
1. Every geometric fibre is proper over its algebraically closed field, hence Noetherian.
   Its connected-component quotient is finite. Define `n` by its natural cardinality;
   an empty fibre has an empty component quotient.
2. Apply `exists_etale_geometricFibre_clopen_partition`, the Stein splitting step of
   Tag 0BUI. It supplies a pointed étale neighbourhood and a finite clopen partition
   of the pulled-back source. At the marked geometric fibre each piece is connected
   and nonempty, so the partition indexes its connected components.
3. Base-change invariance (`lem-weil-pbc-geometric-component-count-base-change`)
   identifies that number of pieces with `n s`. Finiteness justifies conversion from
   the extended-natural count in that theorem to the natural count used here.
4. The pulled-back morphism is flat and locally of finite presentation, hence open.
   Intersect the finitely many open images of the clopen pieces. The marked point
   belongs to this intersection. Every geometric fibre over it meets every piece:
   a point in each ordinary fibre lifts to a compatible point in the scheme pullback
   with the algebraic closure. This is Mathlib's `Scheme.Pullback.exists_preimage_pullback`.
5. A disjoint clopen covering partitions the connected-component quotient into a
   disjoint sum of the piece quotients. Choose one component in every nonempty piece.
   This gives an injection from the finite index set and proves the lower bound.
   It also covers the empty partition, whose intersection of images is the whole base.
6. The étale neighbourhood map is open. Its image of the intersection is therefore
   an open neighbourhood of `s`. At any point of that image choose a preimage point
   and use base-change invariance again to transfer the inequality to the original base.
-/
theorem Scheme.Hom.geometricComponentCount_lowerSemicontinuous
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] :
    ∃ n : S → ℕ,
      (∀ s : S,
        Finite (ConnectedComponents (pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
            (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s) : Scheme.{u})) ∧
        n s = Nat.card (ConnectedComponents (pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
            (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s) : Scheme.{u}))) ∧
      (∀ s : S, IsEmpty (pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
          (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s) : Scheme.{u}) →
        n s = 0) ∧
      ∀ s : S, ∃ V : S.Opens, s ∈ V ∧ ∀ t : S, t ∈ V → n s ≤ n t := by
  classical
  let n : S → ℕ := fun s ↦ Nat.card (ConnectedComponents (pullback f
    (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
      (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s) : Scheme.{u}))
  refine ⟨n, fun s ↦ ⟨finite_geometricComponents f s, rfl⟩, ?_, ?_⟩
  · intro s hs
    have : IsEmpty (ConnectedComponents (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
        (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s) : Scheme.{u})) :=
      ConnectedComponents.isEmpty_iff_isEmpty.mpr hs
    exact Nat.card_of_isEmpty
  · intro s
    obtain ⟨U, g, u, hg, hu, m, V, hclosed, hdisj, hcover, hconn⟩ :=
      f.exists_etale_geometricFibre_clopen_partition s
    have : Etale g := hg
    let p := pullback.snd f g
    let y := fun w : U ↦ Spec.map (CommRingCat.ofHom (algebraMap (U.residueField w)
      (AlgebraicClosure (U.residueField w)))) ≫ U.fromSpecResidueField w
    let C := fun (w : U) (i : Fin m) ↦
      (pullback.fst p (y w)) ⁻¹' (V i : Set ↥(pullback f g))
    have hcl (w : U) (i : Fin m) : IsClopen (C w i) :=
      ⟨(hclosed i).preimage (pullback.fst p (y w)).continuous,
        (V i).isOpen.preimage (pullback.fst p (y w)).continuous⟩
    have hd (w : U) : Pairwise (fun i j ↦ Disjoint (C w i) (C w j)) := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro z hzi hzj
      exact Set.disjoint_left.mp (TopologicalSpace.Opens.coe_disjoint.mpr (hdisj hij))
        hzi hzj
    have hcov (w : U) : ⋃ i, C w i = Set.univ := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      have hz : pullback.fst p (y w) z ∈ (⨆ i, V i) := by rw [hcover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.mp hz
    let e := ConnectedComponents.equivOfIsClopenOfIsConnected
      (hcl u) (hd u) (hcov u) hconn
    have hcount : n s = m := by
      have h := natCard_geometricComponents_baseChange f g u
      rw [hu] at h
      exact h.symm.trans ((Nat.card_congr e).trans (Nat.card_fin m))
    let W : U.Opens := ⨅ i, ⟨p '' (V i : Set ↥(pullback f g)),
      p.isOpenMap _ (V i).isOpen⟩
    have hmem (w : U) : w ∈ W ↔ ∀ i, w ∈ p '' (V i : Set ↥(pullback f g)) := by
      simp only [W, ← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
      rfl
    have huW : u ∈ W := by
      apply (hmem u).mpr
      intro i
      obtain ⟨z, hz⟩ := (hconn i).nonempty
      refine ⟨pullback.fst p (y u) z, hz, ?_⟩
      have h := congrArg (fun a : pullback p (y u) ⟶ U ↦ a z)
        (pullback.condition (f := p) (g := y u))
      exact h.trans (U.fromSpecResidueField_apply u _)
    refine ⟨⟨g '' (W : Set U), g.isOpenMap _ W.isOpen⟩, ⟨u, huW, hu⟩, ?_⟩
    intro t ht
    obtain ⟨w, hw, rfl⟩ := ht
    have hne (i : Fin m) : (C w i).Nonempty := by
      obtain ⟨x, hx, hpx⟩ := (hmem w).mp hw i
      obtain ⟨a⟩ : Nonempty (Spec (CommRingCat.of (AlgebraicClosure (U.residueField w)))) :=
        inferInstance
      obtain ⟨z, hzx, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := y w)
        x a (hpx.trans (U.fromSpecResidueField_apply w _).symm)
      exact ⟨z, by change pullback.fst p (y w) z ∈ V i; rwa [hzx]⟩
    have := finite_geometricComponents p w
    rw [hcount]
    change m ≤ Nat.card (ConnectedComponents (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField (g w))
        (AlgebraicClosure (S.residueField (g w))))) ≫
          S.fromSpecResidueField (g w)) : Scheme.{u}))
    rw [← natCard_geometricComponents_baseChange f g w]
    exact card_le_of_clopen_partition (C w) (hcl w) (hd w) (hcov w) hne

end AlgebraicGeometry
