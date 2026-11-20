import Langlands.GroupScheme.SimplyConnected.TypeE6KernelWeights
import Langlands.GroupScheme.SimplyConnected.StarOrbitWeights

/-! # The first E6 kernel weight in another A5 numbering -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

private theorem a5_endpoint_iff (i : Fin 5) :
    (∃ j : Fin 5, ∀ l : Fin 5, CartanMatrix.A 5 i l = -1 ↔ l = j) ↔
      i = 0 ∨ i = 4 := by
  revert i
  simp only [CartanMatrix.A, Matrix.of_apply]
  decide

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  {d : TitsIndexData G} {a : TitsIndexData H} {ι : H ⟶ G}
  (c : d.KernelComparison ι a)
  (q : d.Vertex ≃ Fin 6)
  (hq : d.IsNumberingOf (CartanMatrix.E 6) (fun i => i.val = 1) q)

/-- The first integral fundamental weight in the induced A5 numbering of
the actual E6 kernel. -/
def KernelComparison.e6BranchFirstWeight (hsc : IsSimplyConnected H) :
    characterLattice a.pinning.toSplitPinning.torus :=
  a.absoluteFundamentalCharacter hsc ((c.e6BranchNumbering q hq).symm 0)

/-- The basis character is the integral weight used in the E6 restriction formula. -/
theorem KernelComparison.e6BranchFirstWeight_eq_firstWeight (hsc : IsSimplyConnected H) :
    c.e6BranchFirstWeight q hq hsc =
      Langlands.TypeANegationWeyl.firstWeight a.pinning.rootDatum a.pinning.base
        (c.e6BranchNumbering q hq) (a.pinning_corootSpan_eq_top hsc) (by decide) := by
  classical
  let r := c.e6BranchNumbering q hq
  change a.absoluteFundamentalCharacter hsc (r.symm 0) =
    Langlands.TypeANegationWeyl.firstWeight a.pinning.rootDatum a.pinning.base
      r (a.pinning_corootSpan_eq_top hsc) (by decide)
  apply IntegralWeylVector.eq_of_pairing_simple_eq
    a.pinning.rootDatum a.pinning.base (a.pinning_corootSpan_eq_top hsc)
  intro x
  simp only [Langlands.TypeANegationWeyl.pairing_firstWeight, absoluteFundamentalCharacter,
    Langlands.RootDatum.fundamentalWeightBasis_pairing, Equiv.eq_symm_apply,
    Fin.ext_iff, Fin.val_zero]

/-- The first vertex in the E6 branch complement is an endpoint of the
actual kernel in every numbering with its A5 Cartan entries. -/
theorem KernelComparison.e6BranchFirstVertex_eq_endpoint
    (e : a.Vertex ≃ Fin 5)
    (he : ∀ x y, a.cartan x y = CartanMatrix.A 5 (e x) (e y)) :
    let first := (c.e6BranchNumbering q hq).symm 0
    first = e.symm 0 ∨ first = e.symm 4 := by
  let r := c.e6BranchNumbering q hq
  let first := r.symm 0
  have hzero : ∀ i : Fin 5, CartanMatrix.A 5 0 i = -1 ↔ i = 1 := by
    simp only [CartanMatrix.A, Matrix.of_apply]
    decide
  have hend : e first = 0 ∨ e first = 4 := by
    apply (a5_endpoint_iff (e first)).mp
    refine ⟨e (r.symm 1), fun i => ?_⟩
    have hrow : CartanMatrix.A 5 (e first) i = CartanMatrix.A 5 0 (r (e.symm i)) := by
      rw [← e.apply_symm_apply i, ← he]
      rw [c.e6BranchNumbering_cartan q hq]
      simp [first, r]
    rw [hrow, hzero, ← r.eq_symm_apply]
    constructor
    · intro hi
      simpa only [e.apply_symm_apply] using congrArg e hi
    · intro hi
      simpa only [e.symm_apply_apply] using congrArg e.symm hi
  exact hend.imp e.eq_symm_apply.mpr e.eq_symm_apply.mpr

/-- The first weight of the E6 branch complement is the actual fundamental
character at one of the endpoints of any numbering of the same kernel. -/
theorem KernelComparison.e6BranchFirstWeight_eq_endpoint
    (hsc : IsSimplyConnected H) (e : a.Vertex ≃ Fin 5)
    (he : ∀ x y, a.cartan x y = CartanMatrix.A 5 (e x) (e y)) :
    c.e6BranchFirstWeight q hq hsc = a.absoluteFundamentalCharacter hsc (e.symm 0) ∨
      c.e6BranchFirstWeight q hq hsc = a.absoluteFundamentalCharacter hsc (e.symm 4) := by
  exact (c.e6BranchFirstVertex_eq_endpoint q hq e he).imp
    (congrArg (a.absoluteFundamentalCharacter hsc)) (congrArg (a.absoluteFundamentalCharacter hsc))

end Langlands.GroupScheme.TitsIndexData
