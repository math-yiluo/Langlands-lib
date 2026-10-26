import Langlands.Representation.Geometric.NestedLeviCompatibilityStatement

/-! # Compatibility through actual nested Levi refinements -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric

universe uA uK

namespace NestedLeviCompatibilityProof

private theorem repeat_blockIndex {A : Type uA} {n : ℕ}
    (B : BlockShape n) (S : BlockRefinement B) (a : Fin B.length → A) (x : Fin n) :
    a (((B.flattenBlockEquiv S).symm (blockIndex (B.flatten S) x)).1) =
      a (blockIndex B x) := by
  obtain ⟨⟨k, c⟩, rfl⟩ := (B.flatten S).indexEquiv.surjective x
  change a (((B.flattenBlockEquiv S).symm
      (blockIndex (B.flatten S) ((B.flatten S).index k c))).1) =
    a (blockIndex B ((B.flatten S).index k c))
  rw [blockIndex_index, B.flatten_index S k c, blockIndex_index]

private theorem transport_blockIndex {A : Type uA} {n : ℕ} {C C' : BlockShape n}
    (h : C = C') (v : Fin C.length → A) (x : Fin n) :
    (h ▸ v) (blockIndex C' x) = v (blockIndex C x) := by
  subst C'
  rfl

private theorem transport_leviEmbedding (K : Type uK) [CommRing K]
    {n : ℕ} {C C' : BlockShape n} (h : C = C') (m : C.Levi K) :
    C'.leviEmbedding K (h ▸ m) = C.leviEmbedding K m := by
  subst C'
  rfl

end NestedLeviCompatibilityProof

/-- Repeated parameters and actual fine-Levi inclusions agree with direct refinement. -/
theorem nestedLeviCompatibility : NestedLeviCompatibilityStatement.{uA,uK} := by
  constructor
  · intro A n B Q R S h a
    let aD : Fin (B.flatten Q).length → A :=
      fun j => a ((B.flattenBlockEquiv Q).symm j).1
    let aC : Fin ((B.flatten Q).flatten R).length → A :=
      fun k => aD (((B.flatten Q).flattenBlockEquiv R).symm k).1
    change (h ▸ aC) = fun k => a ((B.flattenBlockEquiv S).symm k).1
    funext k
    let x : Fin n := (B.flatten S).index k ⟨0, (B.flatten S).positive k⟩
    have hk : blockIndex (B.flatten S) x = k := blockIndex_index _ _ _
    calc
      (h ▸ aC) k = (h ▸ aC) (blockIndex (B.flatten S) x) := by rw [hk]
      _ = aC (blockIndex ((B.flatten Q).flatten R) x) :=
        NestedLeviCompatibilityProof.transport_blockIndex h aC x
      _ = aD (blockIndex (B.flatten Q) x) :=
        NestedLeviCompatibilityProof.repeat_blockIndex (B.flatten Q) R aD x
      _ = a (blockIndex B x) :=
        NestedLeviCompatibilityProof.repeat_blockIndex B Q a x
      _ = a (((B.flattenBlockEquiv S).symm (blockIndex (B.flatten S) x)).1) :=
        (NestedLeviCompatibilityProof.repeat_blockIndex B S a x).symm
      _ = a ((B.flattenBlockEquiv S).symm k).1 := by rw [hk]
  · intro K _ n B Q R S h m
    apply B.leviEmbedding_injective K
    rw [flattenedLeviEquiv_embedding, flattenedLeviEquiv_embedding,
      flattenedLeviEquiv_embedding]
    exact NestedLeviCompatibilityProof.transport_leviEmbedding K h m

end Langlands
