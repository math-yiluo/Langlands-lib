import Langlands.CommutativeAlgebra.Popescu.RegularSequenceFlatStatement
import Langlands.Algebra.IdealLocalFlatnessCriterion
import Langlands.MathlibBase

/-! # Flatness from the closed fibre along an ideal -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace RegularParameter

open IsLocalRing

open scoped TensorProduct

/-- Let `B → S` be a local map of Noetherian local rings and `J ⊂ B` a proper ideal with
`J ⊗_B S → S` injective. Suppose `𝔪_B = J + (z₁, …, z_r)`, the images of the `z_j` form a weakly
regular sequence on `B/J`, and their images form a weakly regular sequence on `S/JS`. Then `S` is
flat over `B`. (Local flatness criterion along `J`, with the closed fibre flat by Stacks 07DY.) -/
theorem flat_of_fibre (hN3 : RegularSequenceFlatStatement.{u}) {B S : Type u} [CommRing B]
    [CommRing S] [IsLocalRing B] [IsNoetherianRing B] [IsLocalRing S] [IsNoetherianRing S]
    [Algebra B S] [IsLocalHom (algebraMap B S)] (J : Ideal B) (hJ : J ≠ ⊤)
    (hinj : Function.Injective (LinearMap.rTensor S J.subtype)) {r : ℕ} (z : Fin r → B)
    (hmax : maximalIdeal B = J ⊔ Ideal.span (Set.range z))
    (hβ : RingTheory.Sequence.IsWeaklyRegular (B ⧸ J)
      (List.ofFn fun j => Ideal.Quotient.mk J (z j)))
    (hγ : RingTheory.Sequence.IsWeaklyRegular (S ⧸ J.map (algebraMap B S))
      (List.ofFn fun j => Ideal.Quotient.mk (J.map (algebraMap B S)) (algebraMap B S (z j)))) :
    Module.Flat B S := by
  have hJS : J.map (algebraMap B S) ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top
      ((Ideal.map_mono (le_maximalIdeal hJ)).trans (map_maximalIdeal_le _))
  have : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (B ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have : Nontrivial (S ⧸ J.map (algebraMap B S)) := Ideal.Quotient.nontrivial_iff.mpr hJS
  have : IsLocalRing (S ⧸ J.map (algebraMap B S)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hloc : IsLocalHom (algebraMap (B ⧸ J) (S ⧸ J.map (algebraMap B S))) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    by_cases hy : y ∈ maximalIdeal B
    · exfalso
      have hgy : algebraMap B S y ∈ maximalIdeal S := map_nonunit (algebraMap B S) y hy
      have h1 : Ideal.Quotient.mk (J.map (algebraMap B S)) (algebraMap B S y) ∈
          maximalIdeal (S ⧸ J.map (algebraMap B S)) := by
        rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk (J.map (algebraMap B S)))
          Ideal.Quotient.mk_surjective]
        exact Ideal.mem_map_of_mem _ hgy
      exact (mem_maximalIdeal _).mp h1 hx
    · have hyu : IsUnit y := by
        by_contra h'
        exact hy ((mem_maximalIdeal _).mpr h')
      exact hyu.map (Ideal.Quotient.mk J)
  have hα : Ideal.ofList (List.ofFn fun j => Ideal.Quotient.mk J (z j)) =
      maximalIdeal (B ⧸ J) := by
    rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective,
      hmax, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span,
      ← Set.range_comp]
    unfold Ideal.ofList
    congr 1
    ext x
    simp only [List.mem_ofFn, Set.mem_ofPred_eq, Set.mem_range, Function.comp_apply]
  have hγ' : RingTheory.Sequence.IsWeaklyRegular (S ⧸ J.map (algebraMap B S))
      ((List.ofFn fun j => Ideal.Quotient.mk J (z j)).map
        (algebraMap (B ⧸ J) (S ⧸ J.map (algebraMap B S)))) := by
    rw [List.map_ofFn]
    exact hγ
  have hfibflat : Module.Flat (B ⧸ J) (S ⧸ J.map (algebraMap B S)) :=
    hN3 _ _ _ hα hβ hγ'
  have hfib : Module.Flat (B ⧸ J) ((B ⧸ J) ⊗[B] S) :=
    Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S J).symm.toLinearEquiv
  exact Langlands.Algebra.idealLocalFlatnessCriterion B S S J hJ inferInstance hinj hfib

end RegularParameter

end Langlands.CommutativeAlgebra.Popescu
