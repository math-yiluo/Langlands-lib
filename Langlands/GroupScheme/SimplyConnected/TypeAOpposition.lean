import Langlands.GroupScheme.SimplyConnected.TypeDVectorQuotient
import Langlands.GroupScheme.Reductive.TitsIndexOpposition
import Langlands.GroupScheme.SimplyConnected.TypeARankOneOrbit
import Langlands.GroupScheme.SimplyConnected.InnerTypeANormOneReduction
import Langlands.LinearAlgebra.TypeANegationWeyl

/-! # Actual type-A opposition is chain reversal -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme
namespace TitsIndexData

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

/-- The actual opposition permutation expressed in any supplied numbering. -/
def numberedOpposition {n : ℕ} (e : d.Vertex ≃ Fin n) : Equiv.Perm (Fin n) :=
  (e.symm.trans d.opposition).trans e

@[simp] theorem numberedOpposition_apply {n : ℕ} (e : d.Vertex ≃ Fin n) (i : Fin n) :
    d.numberedOpposition e i = e (d.opposition (e.symm i)) := rfl

/-- In a numbered type-A root datum with full integral coroot span, actual
opposition is reversal of the entire chain. -/
theorem opposition_eq_rev_of_A_of_corootSpan {n : ℕ} (e : d.Vertex ≃ Fin n)
    (hA : ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b))
    (hspan : d.pinning.toSplitPinning.rootDatum.corootSpan ℤ = ⊤) (a : d.Vertex) :
    e (d.opposition a) = Fin.revPerm (e a) := by
  by_cases hn : 2 ≤ n
  · let f : Fin n → Fin n := fun i => e (d.opposition (e.symm i))
    have hf : ∀ i j, CartanMatrix.A n (f i) (f j) = CartanMatrix.A n i j := by
      intro i j
      calc
        CartanMatrix.A n (f i) (f j) =
            d.cartan (d.opposition (e.symm i)) (d.opposition (e.symm j)) :=
          (hA _ _).symm
        _ = d.cartan (e.symm i) (e.symm j) := d.opposition_cartan _ _
        _ = CartanMatrix.A n i j := by simpa using hA (e.symm i) (e.symm j)
    rcases TypeACartan.eq_id_or_rev_of_preserves f hf with hid | hrev
    · have hfix (i : d.Vertex) : d.opposition i = i := by
        apply e.injective
        simpa [f] using hid (e i)
      have hopp : d.oppositionAut = 1 := by
        apply Subtype.ext
        apply InnerTypeANormOneReduction.aut_eq_one_of_simple
          d.pinning.toSplitPinning.base hspan
        intro i
        exact congrArg Subtype.val (hfix i)
      have hw := (d.pinning.toSplitPinning.basedRootDatumProjection_eq_one_iff
        (Langlands.RootDatumNegation.negAut d.pinning.toSplitPinning.rootDatum)).mp hopp
      exact False.elim (Langlands.TypeANegationWeyl.negAut_not_mem_weylGroup
        d.pinning.toSplitPinning.rootDatum d.pinning.toSplitPinning.base e hA hspan hn hw)
    · simpa [f] using hrev (e a)
  · apply Fin.ext
    simp only [Fin.revPerm_apply, Fin.val_rev]
    have := (e (d.opposition a)).isLt
    have := (e a).isLt
    omega

/-- In every actual simply connected type-A index, opposition reverses any
numbering preserving all Cartan entries. -/
theorem opposition_eq_rev_of_A {n : ℕ} (e : d.Vertex ≃ Fin n)
    (hA : ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b))
    (hsc : IsSimplyConnected G) (a : d.Vertex) :
    e (d.opposition a) = Fin.revPerm (e a) :=
  d.opposition_eq_rev_of_A_of_corootSpan e hA
    (d.pinning_corootSpan_eq_top hsc) a

/-- The numbered opposition permutation is exactly chain reversal in type A. -/
theorem numberedOpposition_eq_rev_of_A {n : ℕ} (e : d.Vertex ≃ Fin n)
    (hA : ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b))
    (hsc : IsSimplyConnected G) : d.numberedOpposition e = Fin.revPerm := by
  apply Equiv.ext
  intro i
  simpa using d.opposition_eq_rev_of_A e hA hsc (e.symm i)

end TitsIndexData
end Langlands.GroupScheme
