import Langlands.LinearAlgebra.CartanE6Root
import Langlands.LinearAlgebra.TypeE6NegationWeyl
import Langlands.GroupScheme.SimplyConnected.TypeAOpposition

/-! # Actual E6 opposition exchanges the two equal arms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

/-- Under an actual E6 numbering and full coroot span, opposition is arm exchange. -/
theorem opposition_eq_symmetry_of_E6_of_corootSpan (e : d.Vertex ≃ Fin 6)
    (hE : ∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b))
    (hspan : d.pinning.toSplitPinning.rootDatum.corootSpan ℤ = ⊤) (a : d.Vertex) :
    e (d.opposition a) = Langlands.CartanE6Root.symmetry (e a) := by
  let f : Fin 6 → Fin 6 := fun i => e (d.opposition (e.symm i))
  have hf : ∀ i j, CartanMatrix.E 6 (f i) (f j) = CartanMatrix.E 6 i j := by
    intro i j
    calc
      CartanMatrix.E 6 (f i) (f j) =
          d.cartan (d.opposition (e.symm i)) (d.opposition (e.symm j)) :=
        (hE _ _).symm
      _ = d.cartan (e.symm i) (e.symm j) := d.opposition_cartan _ _
      _ = CartanMatrix.E 6 i j := by simpa using hE (e.symm i) (e.symm j)
  rcases Langlands.CartanE6Root.eq_id_or_symmetry_of_preserves f hf with hid | hsym
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
    exact False.elim (Langlands.TypeE6NegationWeyl.negAut_not_mem_weylGroup
      d.pinning.toSplitPinning.rootDatum d.pinning.toSplitPinning.base e hE hspan hw)
  · simpa [f] using hsym (e a)

/-- In every simply connected actual E6 index, opposition is the full arm exchange. -/
theorem opposition_eq_symmetry_of_E6 (e : d.Vertex ≃ Fin 6)
    (hE : ∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b))
    (hsc : IsSimplyConnected G) (a : d.Vertex) :
    e (d.opposition a) = Langlands.CartanE6Root.symmetry (e a) :=
  d.opposition_eq_symmetry_of_E6_of_corootSpan e hE
    (d.pinning_corootSpan_eq_top hsc) a

end Langlands.GroupScheme.TitsIndexData
