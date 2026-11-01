import Langlands.Representation.Geometric.TypeASolomonCoefficientProof
import Langlands.Representation.Geometric.RefinementUniqueness
import Langlands.Representation.Classification.ProductLeviMinimalIndex
import Langlands.Representation.Aubert.RefinedAlternatingConstruction

/-! Source-refinement fibers for the actual type-A Solomon coefficients. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear CuspidalSupport ProductLeviMinimalIndex

universe uF

variable {n : ℕ}

/-- A standard block Weyl subgroup determines its ordered positive block shape. -/
theorem blockWeyl_injective : Function.Injective (blockWeyl (n := n)) := by
  intro B C h
  apply BlockShape.cuts_injective
  exact le_antisymm ((blockWeyl_le_iff_cuts_subset B C).mp h.ge)
    ((blockWeyl_le_iff_cuts_subset C B).mp h.le)

/-- The flattened Weyl subgroup determines every component of a refinement. -/
theorem blockWeyl_flatten_injective (B : BlockShape n) :
    Function.Injective (fun S : BlockRefinement B => blockWeyl (B.flatten S)) := by
  intro S R h
  funext i
  apply blockWeyl_injective
  have hrel (a b : Fin (B.size i)) :
      blockIndex (S i) a = blockIndex (S i) b ↔
        blockIndex (R i) a = blockIndex (R i) b := by
    have hh := SetLike.ext_iff.mp h (Equiv.swap (B.index i a) (B.index i b))
    simpa only [TypeASolomon.swap_mem_blockWeyl_iff,
      blockIndex_flatten_index_eq_iff] using hh
  ext v
  change (∀ a, blockIndex (S i) (v a) = blockIndex (S i) a) ↔
    ∀ a, blockIndex (R i) (v a) = blockIndex (R i) a
  exact forall_congr' fun a => hrel (v a) a

section ActualSubgroups

variable (F : Type uF) [CommRing F]
  (B C : BlockShape n) (w : Equiv.Perm (Fin n)) (S : BlockRefinement B)

/-- Flattening carries the actual refined subgroup onto the ordinary flattened Levi. -/
theorem refinedLevi_map_leviEmbedding :
    (refinedLevi F B S).map (B.leviEmbedding F) = (B.flatten S).leviSubgroup F := by
  ext g
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨(flattenedLeviEquiv F B S).symm ⟨m, hm⟩,
      flattenedLeviEquiv_symm_embedding F B S ⟨m, hm⟩⟩
  · rintro ⟨m, rfl⟩
    exact ⟨(flattenedLeviEquiv F B S m).val,
      (flattenedLeviEquiv F B S m).property,
      flattenedLeviEquiv_embedding F B S m⟩

/-- The source intersection in product coordinates is the literal ambient intersection. -/
theorem sourceLevi_map_leviEmbedding :
    (sourceLevi F B C w).map (B.leviEmbedding F) =
      B.leviSubgroup F ⊓
        (C.leviSubgroup F).comap (MulAut.conj (permutation n F w)).toMonoidHom := by
  ext g
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, rfl⟩, hm⟩
  · rintro ⟨⟨m, rfl⟩, hm⟩
    exact ⟨m, hm, rfl⟩

/-- An actual source-Levi equality gives precisely the source-side Weyl intersection. -/
theorem blockWeyl_flatten_eq_intersection
    [Nontrivial F]
    (hS : sourceLevi F B C w = refinedLevi F B S) :
    blockWeyl (B.flatten S) =
      blockWeyl B ⊓ (blockWeyl C).comap (MulAut.conj w).toMonoidHom := by
  have hmat : (B.flatten S).leviSubgroup F =
      B.leviSubgroup F ⊓
        (C.leviSubgroup F).comap (MulAut.conj (permutation n F w)).toMonoidHom := by
    rw [← refinedLevi_map_leviEmbedding F B S, ← hS,
      sourceLevi_map_leviEmbedding F B C w]
  ext v
  have hh := SetLike.ext_iff.mp hmat (permutation n F v)
  change permutation n F v ∈ (B.flatten S).leviSubgroup F ↔
    permutation n F v ∈ B.leviSubgroup F ∧
      permutation n F w * permutation n F v * (permutation n F w)⁻¹ ∈
        C.leviSubgroup F at hh
  change v ∈ blockWeyl (B.flatten S) ↔ v ∈ blockWeyl B ∧
    w * v * w⁻¹ ∈ blockWeyl C
  simpa only [← map_inv, ← map_mul, permutation_mem_levi_iff] using hh

end ActualSubgroups

/-- The signed source-refinement fiber count, over every target block shape. -/
def refinementSolomonCoefficient (B : BlockShape n)
    (S : ∀ C : BlockShape n, MinimalRepresentatives B C → BlockRefinement B)
    (Q : BlockRefinement B) : ℤ := by
  let _ : Fintype (BlockShape n) := Fintype.ofFinite _
  exact ∑ C : BlockShape n, (-1 : ℤ) ^ (n - C.length) *
    (Nat.card {w : MinimalRepresentatives B C // S C w = Q} : ℤ)

/-- For actual intersection refinements, the fiber coefficients are the intrinsic
product-Levi signs, with no positivity restriction on the total rank. -/
theorem refinementSolomonCoefficient_eq
    (F : Type uF) [CommRing F] [Nontrivial F] (B : BlockShape n)
    (S : ∀ C : BlockShape n, MinimalRepresentatives B C → BlockRefinement B)
    (hS : ∀ C w, sourceLevi F B C w.val = refinedLevi F B (S C w))
    (Q : BlockRefinement B) :
    refinementSolomonCoefficient B S Q = (-1 : ℤ) ^ Aubert.refinementSignExponent B Q := by
  classical
  let _ : Fintype (BlockShape n) := Fintype.ofFinite _
  have hfiber (C : BlockShape n) (w : MinimalRepresentatives B C) :
      S C w = Q ↔ blockWeyl B ⊓
        (blockWeyl C).comap (MulAut.conj w.val).toMonoidHom = blockWeyl (B.flatten Q) := by
    rw [← blockWeyl_flatten_eq_intersection F B C w.val (S C w) (hS C w)]
    exact (blockWeyl_flatten_injective B).eq_iff.symm
  have hc := typeASolomonCoefficientStatement n B (B.flatten Q) (blockWeyl_flatten_le B Q)
  have hcard (C : BlockShape n) :
      Nat.card {w : MinimalRepresentatives B C // S C w = Q} =
        Nat.card {w : MinimalRepresentatives B C // blockWeyl B ⊓
          (blockWeyl C).comap (MulAut.conj w.val).toMonoidHom = blockWeyl (B.flatten Q)} :=
    Nat.card_congr (Equiv.subtypeEquivRight (hfiber C))
  simpa only [refinementSolomonCoefficient, hcard,
    Aubert.refinementSignExponent_eq, BlockShape.flatten] using hc

end Langlands.Geometric
