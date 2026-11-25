/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetInsertion

/-! # Reassembly of one ordered Čech row

Source: Stacks Project, Tags 08C1, 08C0, and 01FG.
(blueprint: lem-sc-principal-open-cech-subset-row-reassembly).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance] Classical.propDecidable

private theorem sum_apply {M N : AddCommGrpCat.{u}} {ι : Type*}
    (g : ι → (M ⟶ N)) (s : Finset ι) (x : M) :
    (∑ i ∈ s, g i) x = ∑ i ∈ s, g i x := by
  rw [← AddMonoidHom.finsetSum_apply]
  exact congr($(map_sum AddCommGrpCat.homAddEquiv g s) x)

/-- Reassemble a family supported on one row from its tuple coordinates.

Source: Stacks Project, Tags 01FM and 08C1, ordered Čech totalization.
(blueprint: lem-sc-principal-open-cech-subset-row-reassembly).

Proof: Expand subset insertion as the sum of its single-subset insertions.
The support hypothesis kills subsets whose cardinality is not p+1.
Increasing enumeration bijects the remaining subsets with increasing (p+1)-tuples.
The coordinate hypothesis identifies each section-transported summand with the
corresponding coordinate of w. The equality of total degrees identifies its
coefficient degree with q. Proof irrelevance identifies all degree witnesses.
The sum of the tuple singletons is w; additivity of the extension isomorphism
and total inclusion gives the result. If p is larger than the index set,
both tuple and supported-subset families are empty, so both sides are zero. -/
theorem principalSubsetRowReassembly
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) (n : ℤ) (p : ℕ) (q : ℤ) :
    let V := principalSubsetUnion A r f
    let U : Fin r → V.toScheme.Opens := fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
    let K := (alternatingCechDoubleFunctor U).obj (principalSubsetRestriction A r f J)
    let H := forget₂
      (ModuleCat.{u} ((moduleRings V.toScheme.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat
    let P := alternatingCechModulePresheaf.obj ((principalSubsetRestriction A r f J).X q)
    let L := alternatingCechComplex U P
    let e : (K.X (p : ℤ)).X q ≅ L.X p :=
      L.extendXIso ComplexShape.embeddingUpNat rfl
    ∀ (hdeg : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ((p : ℤ), q) = n)
      (w : L.X p) (s : principalSubsetCoordinates A r f J n),
      (∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card ≠ p + 1 → s S = 0) →
      (∀ (S : {S : Finset (Fin r) // S.Nonempty}) (hcard : S.val.card = p + 1),
        HEq (w (S.val.orderEmbOfFin hcard))
          ((principalSubsetSectionTransport A r f
            (J.X (n + 1 - (S.val.card : ℤ))) S).hom (s S))) →
      (H.map (e.inv ≫ K.ιTotal (ComplexShape.up ℤ) (p : ℤ) q n hdeg)) w =
        principalSubsetInsertion A r f J n s := by
  classical
  intro V U K H P L e hdeg w s hs hw
  let F := Finset.univ.filter (fun S : {S : Finset (Fin r) // S.Nonempty} ↦
    S.val.card = p + 1)
  have hinsertion : principalSubsetInsertion A r f J n s =
      ∑ S ∈ F, principalSubsetInsertOne A r f J n S (s S) := by
    unfold principalSubsetInsertion
    rw [sum_apply]
    change (∑ S, principalSubsetInsertOne A r f J n S (s S)) = _
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S _ hS
    have hc : S.val.card ≠ p + 1 := by simpa only [F, Finset.mem_filter,
      Finset.mem_univ, true_and] using hS
    rw [hs S hc, map_zero]
  rw [hinsertion, ← Finset.univ_sum_single w, map_sum]
  symm
  apply Finset.sum_bij
    (fun S hS ↦ S.val.orderEmbOfFin (show S.val.card = p + 1 from
      (Finset.mem_filter.mp hS).2))
  · intro S hS
    exact Finset.mem_univ _
  · intro S hS T hT hST
    apply Subtype.ext
    apply Finset.coe_injective
    simpa only [Finset.range_orderEmbOfFin] using
      congrArg (fun t : Fin (p + 1) ↪o Fin r ↦ Set.range t) hST
  · intro t _
    let S : {S : Finset (Fin r) // S.Nonempty} :=
      ⟨Finset.univ.map t.toEmbedding,
        ⟨t 0, Finset.mem_map.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩⟩
    have hc : S.val.card = p + 1 := by
      simp only [S, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    have hS : S ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
    refine ⟨S, hS, ?_⟩
    symm
    apply Finset.orderEmbOfFin_unique'
    intro i
    exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
  · intro S hS
    have hc := (Finset.mem_filter.mp hS).2
    have hp : p = S.val.card - 1 := by omega
    have hq : q = n + 1 - (S.val.card : ℤ) := by
      change (p : ℤ) + q = n at hdeg
      omega
    subst p
    subst q
    have hh : w (principalSubsetTuple r S) =
        (principalSubsetSectionTransport A r f
          (J.X (n + 1 - (S.val.card : ℤ))) S).hom (s S) := eq_of_heq (hw S hc)
    dsimp only [principalSubsetInsertOne]
    change K.ιTotal (ComplexShape.up ℤ) _ _ n _
      (e.inv (Pi.single (principalSubsetTuple r S)
        ((principalSubsetSectionTransport A r f
          (J.X (n + 1 - (S.val.card : ℤ))) S).hom (s S)))) = _
    rw [← hh]
    rfl

end AlgebraicGeometry
