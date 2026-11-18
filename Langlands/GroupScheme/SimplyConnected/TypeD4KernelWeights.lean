import Langlands.GroupScheme.Reductive.TitsKernelWeightRestriction
import Langlands.GroupScheme.SimplyConnected.TypeEAnisotropicKernelModel
import Langlands.GroupScheme.SimplyConnected.TypeD4CentralCharacters
import Langlands.GroupScheme.Reductive.TitsCartanComponent

/-! # Actual leaf vertices and weights in the centrally marked D4 kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TitsIndexData

variable {K : Type u} [Field K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {d : TitsIndexData G}

/-- Exactly the leaves of a centrally marked D4 numbering are zero vertices. -/
theorem zeroVertices_iff_D4_leaf
    (q : d.Vertex ≃ Fin 4)
    (hq : d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) q)
    (a : d.Vertex) :
    a ∈ d.zeroVertices ↔ q a ≠ 1 := by
  have hm : a ∉ d.zeroVertices ↔ q a = 1 := by
    simpa [distinguishedVertices, Fin.ext_iff] using hq.2 a
  simpa only [not_not] using not_congr hm

/-- Number the actual zero vertices of centrally marked D4 in leaf order
0, 2, 3. -/
def d4ZeroLeafNumbering
    (q : d.Vertex ≃ Fin 4)
    (hq : d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) q) :
    d.zeroVertices ≃ Fin 3 :=
  (Equiv.subtypeEquiv q (zeroVertices_iff_D4_leaf q hq)).trans
    (finSuccAboveEquiv (1 : Fin 4)).symm

theorem d4ZeroLeafNumbering_ambient
    (q : d.Vertex ≃ Fin 4)
    (hq : d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) q)
    (a : d.zeroVertices) :
    q a.val = (1 : Fin 4).succAbove (d4ZeroLeafNumbering q hq a) := by
  exact (congrArg Subtype.val
    ((finSuccAboveEquiv (1 : Fin 4)).apply_symm_apply
      ((Equiv.subtypeEquiv q (zeroVertices_iff_D4_leaf q hq)) a))).symm

/-- Number the actual kernel's simple vertices in the same leaf order
0, 2, 3, through its actual zero-subdiagram comparison. -/
def AnisotropicKernelIndex.d4LeafNumbering
    (p : d.AnisotropicKernelIndex) (q : d.Vertex ≃ Fin 4)
    (hq : d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) q) :
    p.index.Vertex ≃ Fin 3 :=
  p.comparison.vertexEquiv.trans (d4ZeroLeafNumbering q hq)

theorem AnisotropicKernelIndex.d4LeafNumbering_ambient
    (p : d.AnisotropicKernelIndex) (q : d.Vertex ≃ Fin 4)
    (hq : d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) q)
    (a : p.index.Vertex) :
    q (p.comparison.vertexEquiv a).val =
      (1 : Fin 4).succAbove (p.d4LeafNumbering q hq a) :=
  d4ZeroLeafNumbering_ambient q hq (p.comparison.vertexEquiv a)

/-- Every actual Cartan entry of the D4 kernel is 2 on the diagonal and
zero off it. In particular the three vertices are three isolated A1 components. -/
theorem AnisotropicKernelIndex.cartan_D4_central_mark
    (p : d.AnisotropicKernelIndex) (q : d.Vertex ≃ Fin 4)
    (hq : d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) q)
    (a b : p.index.Vertex) :
    p.index.cartan a b =
      if p.d4LeafNumbering q hq a = p.d4LeafNumbering q hq b then 2 else 0 := by
  rw [← p.comparison.vertexEquiv_cartan a b, hq.1,
    p.d4LeafNumbering_ambient q hq a, p.d4LeafNumbering_ambient q hq b]
  have hmatrix (i j : Fin 3) :
      CartanMatrix.D 4 ((1 : Fin 4).succAbove i) ((1 : Fin 4).succAbove j) =
        if i = j then 2 else 0 := by
    fin_cases i <;> fin_cases j <;> decide
  exact hmatrix _ _

/-- Actual kernel Cartan connectivity is equality for centrally marked D4. -/
theorem AnisotropicKernelIndex.cartanConnected_iff_eq_D4_central_mark
    (p : d.AnisotropicKernelIndex) (q : d.Vertex ≃ Fin 4)
    (hq : d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) q)
    (a b : p.index.Vertex) :
    p.index.CartanConnected a b ↔ a = b := by
  constructor
  · intro h
    induction h with
    | rel x y hxy =>
      have hne : p.d4LeafNumbering q hq x ≠ p.d4LeafNumbering q hq y :=
        fun h => hxy.1 ((p.d4LeafNumbering q hq).injective h)
      exact False.elim (hxy.2 (by rw [p.cartan_D4_central_mark q hq]; simp [hne]))
    | refl => rfl
    | symm _ _ _ hxy => exact hxy.symm
    | trans _ _ _ _ _ hxy hyz => exact hxy.trans hyz
  · rintro rfl
    exact p.index.cartanConnected_refl a

/-- The full star action on actual kernel leaves is the original full star
action on ambient D4 leaves, with every automorphism retained. -/
theorem AnisotropicKernelIndex.d4LeafNumbering_star
    (p : d.AnisotropicKernelIndex) (q : d.Vertex ≃ Fin 4)
    (hq : d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) q)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : p.index.Vertex) :
    (1 : Fin 4).succAbove (p.d4LeafNumbering q hq (p.index.star σ a)) =
      q (d.star σ (p.comparison.vertexEquiv a).val) := by
  rw [← p.d4LeafNumbering_ambient q hq]
  exact congrArg (fun b : d.zeroVertices => q b.val)
    (p.comparison.vertexEquiv_star σ a)

/-- Restriction along the actual kernel torus sends the ambient fundamental
weight at each corresponding leaf to its actual kernel fundamental weight. -/
theorem AnisotropicKernelIndex.weightRestriction_D4_leaf
    (p : d.AnisotropicKernelIndex) (hsc : IsSimplyConnected G)
    (q : d.Vertex ≃ Fin 4)
    (hq : d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) q)
    (i : Fin 3) :
    p.comparison.weightRestriction
        (d.absoluteFundamentalCharacter hsc
          (q.symm ((1 : Fin 4).succAbove i))) =
      p.index.absoluteFundamentalCharacter (p.isSimplyConnected hsc)
        ((p.d4LeafNumbering q hq).symm i) := by
  let b : p.index.Vertex := (p.d4LeafNumbering q hq).symm i
  have hleaf : (p.comparison.vertexEquiv b).val =
      q.symm ((1 : Fin 4).succAbove i) := by
    apply q.injective
    rw [p.d4LeafNumbering_ambient q hq]
    simp only [b, Equiv.apply_symm_apply]
  have hweight := p.comparison.weightRestriction_fundamentalWeight_zero
    (d.pinning_corootSpan_eq_top hsc)
    (p.index.pinning_corootSpan_eq_top (p.isSimplyConnected hsc))
    (p.comparison.vertexEquiv b)
  simpa only [Equiv.symm_apply_apply, absoluteFundamentalCharacter, hleaf] using hweight

/-- The ambient central fundamental weight restricts to zero on the actual
centrally marked D4 kernel torus. -/
theorem AnisotropicKernelIndex.weightRestriction_D4_center
    (p : d.AnisotropicKernelIndex) (hsc : IsSimplyConnected G)
    (q : d.Vertex ≃ Fin 4)
    (hq : d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) q) :
    p.comparison.weightRestriction
      (d.absoluteFundamentalCharacter hsc (q.symm 1)) = 0 := by
  exact p.comparison.weightRestriction_fundamentalWeight_distinguished
    (d.pinning_corootSpan_eq_top hsc)
    (p.index.pinning_corootSpan_eq_top (p.isSimplyConnected hsc))
    (q.symm 1) ((hq.2 _).mpr (by simp))

end Langlands.GroupScheme.TitsIndexData
