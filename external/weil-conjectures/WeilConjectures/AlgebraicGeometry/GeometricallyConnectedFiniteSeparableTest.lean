/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.FieldTheory.Separable
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition
import WeilConjectures.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends
import WeilConjectures.AlgebraicGeometry.GeometricallyConnectedCheckAfterExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Testing geometric connectedness by finite separable extensions

Source: Stacks Project, Varieties, Lemma Tag 0389
(blueprint: lem-weil-pbc-geometrically-connected-finite-separable-test).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem invariant_clopen_eq_empty_or_univ
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsGalois k L]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [ConnectedSpace X]
    (U : Set ↥(pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L)))))
    (hU : IsClopen U)
    (hinv : ∀ σ : L ≃ₐ[k] L,
      (baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)) '' U = U) :
    U = ∅ ∨ U = Set.univ := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let p := pullback.fst (X ↘ Spec (.of k)) g
  have : Surjective g := ⟨fun x ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  have hp : Function.Surjective p := p.surjective
  obtain ⟨A, hA, hpreA⟩ := exists_closed_subset_of_galois_invariant k L X U hU.isClosed hinv
  have hinvc : ∀ σ : L ≃ₐ[k] L,
      (baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)) '' Uᶜ = Uᶜ := by
    intro σ
    have : IsIso (specAlgEquivOver σ).left := by
      change IsIso (Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom))
      exact inferInstanceAs (IsIso (Spec.map σ.toRingEquiv.toCommRingCatIso.hom))
    have : IsIso (baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)) :=
      (isPullback_baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)).isIso_fst_of_isIso
    have hbij : Function.Bijective
        (baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)) := by
      simpa only [Function.Bijective, Function.Injective, Function.Surjective,
        Scheme.Hom.homeomorph_apply] using
        (baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)).homeomorph.bijective
    rw [Set.image_compl_eq hbij, hinv σ]
  obtain ⟨B, hB, hpreB⟩ :=
    exists_closed_subset_of_galois_invariant k L X Uᶜ hU.compl.isClosed hinvc
  have hB_eq : B = Aᶜ := by
    apply Set.preimage_injective.mpr hp
    simpa only [p, g, Set.preimage_compl, hpreA] using hpreB
  have hAclopen : IsClopen A := ⟨hA, by simpa only [hB_eq, compl_compl] using hB.isOpen_compl⟩
  rcases isClopen_iff.mp hAclopen with h | h
  · left
    simpa only [h, Set.preimage_empty] using hpreA.symm
  · right
    simpa only [h, Set.preimage_univ] using hpreA.symm

/-- A scheme over a field is geometrically connected precisely when its base change to
 every finite separable field extension is connected.
Source: Stacks Project, Varieties, Lemma Tag 0389
(blueprint: lem-weil-pbc-geometrically-connected-finite-separable-test).

Proof:
1. Geometric connectedness gives connectedness after every field extension, hence every
   finite separable extension (def-pc-geometrically-irreducible).
2. Conversely, assume the finite separable tests hold. Choose a separable closure `ks/k`,
   Galois over `k` and every intermediate field
   (lem-weil-pbc-separable-closure-exists-galois). The automorphisms of `ks/k` act on `Y_ks`
   by base change (def-pc-base-change), contravariantly, and fix its projection `p` to `Y`.
   This projection is surjective (lem-weil-pbc-surjective-base-change).
3. The degree-one test `k/k` makes `Y` nonempty, so `Y_ks` is nonempty too
   (def-weil-connected-scheme, def-weil-pbc-separable-algebraic-extension).
4. If `Y` were not geometrically connected, `Y_ks` would be disconnected: otherwise
   lem-weil-separably-closed-geometrically-connected and
   lem-weil-geometrically-connected-check-after-extension imply geometric connectedness of `Y`.
   Thus write `Y_ks` as the disjoint union of nonempty clopen subsets `Ubar` and `Vbar`.
5. For every quasi-compact open `W` of `Y`, its inverse image `W_ks` is quasi-compact:
   the projection is quasi-compact by lem-weil-pbc-qcqs-morphism-permanence, and `W` is a
   finite union of affine opens (def-weil-finite-type-morphism). Its intersections with
   `Ubar` and `Vbar` are quasi-compact by lem-weil-pbc-closed-in-quasi-compact. By
   lem-weil-pbc-galois-base-change-qc-open-descends they are invariant under automorphisms
   fixing some finite intermediate field `k_W`.
6. Choose a point of `Ubar` and an affine neighbourhood `W0` of its image in `Y`.
   Set `k' = k_W0` and `H = Aut(ks/k')`. This extension is finite and separable algebraic
   by lem-weil-pbc-separable-closure-exists-galois; `W0_ks` intersected with `Ubar` is
   nonempty and `H`-invariant.
7. There are only finitely many `H`-translates of each intersection in step 5.
   Indeed, if the inverses of two automorphisms agree on `k_W`, their translates agree,
   since their quotient fixes `k_W`. There are finitely many embeddings of `k_W` into `ks`
   by lem-weil-pbc-finite-extension-finitely-many-embeddings.
8. Define `U_W` as the intersection of the translates of `W_ks` intersected with `Ubar`,
   and `V_W` as the union of the translates of `W_ks` intersected with `Vbar`.
   By step 7 these operations are finite, giving complementary clopen subsets of `W_ks`.
   They are `H`-invariant by reindexing automorphisms. Also `U_W0` is nonempty, and
   `V_W` contains `W_ks` intersected with `Vbar`.
9. If `W` is contained in `W'`, invariance of `W_ks` and bijectivity of automorphisms
   imply `W_ks` intersected with `U_W'` equals `U_W`, and similarly for `V`.
   For arbitrary `W,W'`, apply this to the quasi-compact open `W` union `W'` to obtain
   compatibility on their overlap.
10. Take the unions of `U_W` and `V_W` over all quasi-compact opens. The compatibility
    gives a complementary open, hence clopen, partition of `Y_ks`, since affine opens
    cover `Y`. Both pieces are `H`-invariant. The first contains `U_W0`; the second
    contains every point of `Vbar` by choosing an affine neighbourhood of its image.
11. Pullback pasting identifies `Y_ks` with the base change of `Y_k'` to `ks`
    (lem-weil-pbc-cartesian-square-pasting, def-pc-fibre-product), with the same `H`-action.
    By lem-weil-pbc-galois-invariant-closed-subset-descends the two pieces descend to closed
    subsets of `Y_k'`. Surjectivity of `Y_ks` to `Y_k'`
    (lem-weil-pbc-surjective-base-change) makes these subsets complementary and nonempty.
    This contradicts the connectedness test for the finite separable extension `k'/k`.
-/
theorem GeometricallyConnected.iff_connectedSpace_finite_separable
    (k : Type u) [Field k] (Y : Scheme.{u}) [Y.Over (Spec (.of k))] :
    GeometricallyConnected (Y ↘ Spec (.of k)) ↔
      ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K]
        [Algebra.IsSeparable k K],
        ConnectedSpace ↥(pullback (Y ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  constructor
  · intro h K _ _ _ _
    have := h
    exact pullback_of_geometrically GeometricallyConnected.geometrically_connectedSpace _ _
  · intro h
    let L := SeparableClosure k
    let f := Y ↘ Spec (.of k)
    let g := Spec.map (CommRingCat.ofHom (algebraMap k L))
    have hYk := h k
    have : Nonempty Y :=
      ⟨(pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k))))
        (Nonempty.some hYk.toNonempty)⟩
    have hconn : ConnectedSpace ↥(pullback f g) := by
      apply connectedSpace_iff_clopen.mpr
      refine ⟨inferInstance, fun U hU ↦ ?_⟩
      by_contra! hne
      obtain ⟨K, hK, V, hV, hVne, hVcne, hVinv⟩ :=
        exists_finite_invariant_clopen_partition k L Y f U hU
          hne.1 (Set.nonempty_compl.mpr hne.2)
      have := hK
      let YK := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      let fK := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      let : YK.Over (Spec (.of K)) := ⟨fK⟩
      have : ConnectedSpace YK := h K
      rcases invariant_clopen_eq_empty_or_univ K L YK V hV hVinv with hV0 | hV1
      · exact hVne.ne_empty hV0
      · exact hVcne.ne_empty (by rw [hV1, Set.compl_univ])
    exact (geometricallyConnected_iff_of_fieldExtension (k := k) (k' := L) Y).mpr
      (GeometricallyConnected.of_connectedSpace_of_isSepClosed (pullback.snd f g))

end AlgebraicGeometry
