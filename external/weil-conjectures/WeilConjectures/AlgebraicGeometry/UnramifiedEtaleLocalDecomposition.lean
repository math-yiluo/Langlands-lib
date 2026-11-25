/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.UnramifiedEtaleFiniteNeighbourhoods
import WeilConjectures.AlgebraicGeometry.FiniteUnramifiedNeighbourhoodsDisjointRefinement

/-!
# Étale-local decomposition near unramified fibre points

Source: Stacks Project, Étale Morphisms, Lemma 41.17.2, Tag 04HI
(blueprint: lem-weil-pbc-unramified-etale-local-decomposition).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Stacks Project, Étale Morphisms, Lemma 41.17.2 (Tag 04HI)
(blueprint: lem-weil-pbc-unramified-etale-local-decomposition).
A separated morphism unramified at finitely many points over `s` admits an étale
neighbourhood with a clopen decomposition into closed immersions through the chosen point
and a remainder whose fibre contains no point mapping to a listed point. The finite family
is indexed by pairs `(i,j)` with `i : Fin n` and `j : Fin (m i)`. Opens specify their actual
open subschemes via `Scheme.Opens.toScheme`; disjointness and covering give the disjoint
union decomposition. No residue-field isomorphism is required of the étale neighbourhood.

Proof:
1. Choose unramified open neighbourhoods of the listed points and take their finite union.
   Use `lem-weil-pbc-unramified-fibre-point-isolated` and
   `lem-weil-pbc-etale-local-finite-multiple-points` to obtain finite open pieces after an
   étale base change. Unramifiedness persists by
   `lem-weil-pbc-unramified-base-change-open` (Stacks 02G6 and 02GA).
2. Shrink the neighbourhood to an affine open, using
   `definition-torsion-sheaves--3`. Apply
   `lem-weil-pbc-finite-unramified-one-point-closed` to the finite unramified pieces and
   intersect the resulting neighbourhoods. On each shrinking replace every piece by its
   base change; `lem-weil-pbc-open-fibre-product` identifies it with the inverse-image open.
3. The pullback is separated. Each piece is proper over the base, so
   `lem-weil-pbc-proper-over-separated` makes its inclusion closed. Intersections of pairs
   of pieces have closed images in the base avoiding the chosen point, by the exclusion
   in `lem-weil-pbc-etale-local-finite-multiple-points`.
4. Delete these finitely many images and base change the pieces again, using
   `lem-weil-pbc-open-fibre-product`. They are now disjoint and clopen. Their clopen
   complement is the remainder, with the required exclusion. If the listed points exhaust
   the original fibre, the remainder's fibre is empty. -/
theorem exists_etale_closed_immersion_decomposition_of_unramified_at_points
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (s : S)
    (n : ℕ) (x : Fin n → X) (hx : ∀ i, f.base (x i) = s)
    (hunramified : ∀ i, ∃ O : X.Opens, x i ∈ O ∧
      LocallyOfFiniteType (O.ι ≫ f) ∧ IsOpenImmersion (pullback.diagonal (O.ι ≫ f))) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S) (u : U),
      Etale g ∧ g.base u = s ∧
      ∃ (m : Fin n → ℕ) (W : (pullback f g).Opens)
        (V : (Σ i : Fin n, Fin (m i)) → (pullback f g).Opens),
        IsClosed (W : Set ↥(pullback f g)) ∧
        (∀ a, IsClosed (V a : Set ↥(pullback f g))) ∧
        Pairwise (fun a b ↦ Disjoint (V a) (V b)) ∧
        (∀ a, Disjoint W (V a)) ∧
        W ⊔ iSup V = ⊤ ∧
        (∀ a, IsClosedImmersion ((V a).ι ≫ pullback.snd f g) ∧
          u ∈ Set.range (((V a).ι ≫ pullback.snd f g).base)) ∧
        (∀ p : ↥(pullback f g), p ∈ W → (pullback.snd f g).base p = u →
          ∀ i, (pullback.fst f g).base p ≠ x i) ∧
        ((∀ y : X, f.base y = s ↔ ∃ i, y = x i) →
          ∀ p : ↥(pullback f g), p ∈ W → (pullback.snd f g).base p ≠ u) := by
  obtain ⟨U, g, u, hg, hus, m, V, v, hpieces, hinjective, hexhaust⟩ :=
    exists_etale_finite_unramified_neighbourhoods f s n x hx hunramified
  obtain ⟨B, huB, V', hclosed, hdisjoint, himmersions, hcover⟩ :=
    exists_disjoint_closed_immersion_refinement f g u n x m V v
      hpieces hinjective hexhaust
  let : Etale g := hg
  let g' : B.toScheme ⟶ S := B.ι ≫ g
  let u' : B.toScheme := ⟨u, huB⟩
  have hu' : g'.base u' = s := hus
  have hclosedUnion : IsClosed (⋃ a, (V' a : Set ↥(pullback f g'))) :=
    isClosed_iUnion_of_finite hclosed
  let W : (pullback f g').Opens :=
    ⟨(⋃ a, (V' a : Set ↥(pullback f g')))ᶜ, hclosedUnion.isOpen_compl⟩
  refine ⟨B.toScheme, g', u', inferInstance, hu', m, W, V', ?_, hclosed,
    hdisjoint, ?_, ?_, himmersions, ?_, ?_⟩
  · exact (isOpen_iUnion fun a ↦ (V' a).isOpen).isClosed_compl
  · intro a
    rw [disjoint_iff]
    apply TopologicalSpace.Opens.ext
    ext p
    simp only [TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_bot,
      Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    exact fun ⟨hpW, hpV⟩ ↦ hpW (Set.mem_iUnion.mpr ⟨a, hpV⟩)
  · apply TopologicalSpace.Opens.ext
    simp only [TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_iSup,
      TopologicalSpace.Opens.coe_top]
    exact Set.compl_union_self _
  · intro p hpW hpu i hpx
    obtain ⟨a, ha⟩ := hcover i p hpu hpx
    exact hpW (Set.mem_iUnion.mpr ⟨a, ha⟩)
  · intro hall p hpW hpu
    have hcomm := congrArg (fun k : pullback f g' ⟶ S ↦ k.base p)
      (pullback.condition (f := f) (g := g'))
    have hfs : f.base ((pullback.fst f g').base p) = s := by
      simpa only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply,
        hpu, hu'] using hcomm
    obtain ⟨i, hi⟩ := (hall ((pullback.fst f g').base p)).mp hfs
    obtain ⟨a, ha⟩ := hcover i p hpu hi
    exact hpW (Set.mem_iUnion.mpr ⟨a, ha⟩)

end AlgebraicGeometry
