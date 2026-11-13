import Langlands.Representation.Classification.A6iiGeometric
import Langlands.Representation.Classification.A6iiCount
import Langlands.Representation.Classification.ProductLeviMinimalIndex
import Langlands.Representation.Parabolic.FlattenedProductInduction
import Langlands.Representation.Geometric.WeylUniquenessProof
import Langlands.Group.GL.NestedRefinement

/-!
# Shape bookkeeping for the irreducible-product argument

A reordering of the flattened blocks that keeps the order inside every outer
block is a minimal representative; counts in opposite Jacquet modules move along
equalities of shapes; and the normalized product along a flattened shape is the
product of the blockwise products.
-/

noncomputable section

namespace Langlands.Classification.A6ii

open CategoryTheory GeneralLinear Geometric RelativeJacquetMultiplicity

universe uF uV uT

section Minimal

variable {n : ℕ}

/-- A reordering of the blocks of a flattened shape which keeps the order of the
blocks inside each outer block is a minimal representative for the outer shape. -/
theorem isMinimalRepresentative_permute_flatten (B : BlockShape n) (S : BlockRefinement B)
    (e : Equiv.Perm (Fin (B.flatten S).length))
    (hstab : ∀ k k', ((B.flattenBlockEquiv S).symm k).1 = ((B.flattenBlockEquiv S).symm k').1 →
      k < k' → e.symm k < e.symm k') :
    IsMinimalRepresentative B ((B.flatten S).permute e) ((B.flatten S).blockPermutation e) := by
  have hP := (CuspidalSupport.isMinimalRepresentative_iff _ _ _).mp
    (CuspidalSupport.isMinimalRepresentative_blockPermutation (B.flatten S) e)
  refine (CuspidalSupport.isMinimalRepresentative_iff _ _ _).mpr ⟨?_, hP.2⟩
  intro a b hab hlt
  by_cases hk : blockIndex (B.flatten S) a = blockIndex (B.flatten S) b
  · exact hP.1 a b hk hlt
  · have hkl : blockIndex (B.flatten S) a < blockIndex (B.flatten S) b :=
      lt_of_le_of_ne (blockIndex_monotone (B.flatten S) hlt.le) hk
    rw [ProductLeviMinimalIndex.blockIndex_eq_flatten B S a,
      ProductLeviMinimalIndex.blockIndex_eq_flatten B S b] at hab
    have he := hstab _ _ hab hkl
    rw [← CuspidalSupport.blockIndex_blockPermutation,
      ← CuspidalSupport.blockIndex_blockPermutation] at he
    by_contra hne
    exact absurd (blockIndex_monotone _ (not_lt.mp hne)) (not_le.mpr he)

end Minimal

section Equivs

variable {G H : Type*} [Monoid G] [Monoid H] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Pulling back along a group equivalence and then along its inverse changes
nothing. -/
def compSymmCompEquiv (ρ : Representation ℂ G V) (e : G ≃* H) :
    Representation.Equiv (((ρ.comp e.symm.toMonoidHom).comp e.toMonoidHom :
      Representation ℂ G V)) ρ :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ V) (fun g => LinearMap.ext fun v => by
    change ρ (e.symm (e g)) v = ρ g v
    rw [MulEquiv.symm_apply_apply])

end Equivs

section Cast

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Counts of twisted test representations move along an equality of shapes
whose exponents correspond. -/
theorem count_cast {n : ℕ} {C C' : BlockShape n} (h : C = C')
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) (ω : Rep.{uT} ℂ (C.Levi F.Carrier))
    (v₀ : Fin C.length → ℝ) (v : Fin C'.length → ℝ)
    (hv : ∀ k, v (Fin.cast (congrArg BlockShape.length h) k) = v₀ k) {c : ℕ}
    (hc : HasJordanHolderMultiplicity (CuspidalJacquetMultiplicity.oppositeJacquet T C' A)
      (Rep.of (T.leviRealPowerTwist C' v (h ▸ ω : Rep.{uT} ℂ (C'.Levi F.Carrier)).ρ)) c) :
    HasJordanHolderMultiplicity (CuspidalJacquetMultiplicity.oppositeJacquet T C A)
      (Rep.of (T.leviRealPowerTwist C v₀ ω.ρ)) c := by
  subst h
  have hvv : v = v₀ := funext fun k => hv k
  subst hvv
  exact hc

/-- The exponent of the fine twist along a composed refinement is the exponent of
the outer block reached through the middle shape. -/
theorem outer_composeRefinement {n : ℕ} (B : BlockShape n) (Q : BlockRefinement B)
    (R : BlockRefinement (B.flatten Q)) (k : Fin ((B.flatten Q).flatten R).length) :
    ((B.flattenBlockEquiv (B.composeRefinement Q R)).symm
        (Fin.cast (B.flatten_composeRefinement_length Q R) k)).1 =
      ((B.flattenBlockEquiv Q).symm
        (((B.flatten Q).flattenBlockEquiv R).symm k).1).1 := by
  obtain ⟨p, rfl⟩ := (B.nestedFlattenBlockEquiv Q R).surjective k
  rw [B.flatten_composeRefinement_block Q R p, BlockShape.composedFlattenBlockEquiv_apply,
    Equiv.symm_apply_apply, BlockShape.nestedFlattenBlockEquiv_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

end Cast

section Regrouping

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The normalized product along a flattened shape is the product of the
blockwise normalized products. -/
theorem nonempty_flatten_iso {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (C : letI := T.topology
      ∀ i j, SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((S i).size j) F.Carrier)) :
    letI := T.topology
    Nonempty ((T.normalizedProductInductionFunctor (B.flatten S)).obj
        (fun k => C ((B.flattenBlockEquiv S).symm k).1 ((B.flattenBlockEquiv S).symm k).2) ≅
      (T.normalizedProductInductionFunctor B).obj
        (fun i => (T.normalizedProductInductionFunctor (S i)).obj (C i))) := by
  let := T.topology
  exact ⟨SmoothRep.mkIso (Parabolic.flattenedProductInducedEquiv.{uF, uV} F T B S C)⟩

end Regrouping

end Langlands.Classification.A6ii
