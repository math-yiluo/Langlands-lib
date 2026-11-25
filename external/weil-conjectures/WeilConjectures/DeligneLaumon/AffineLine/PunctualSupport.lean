/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.DenseOpen
public import WeilConjectures.DeligneLaumon.AffineLine.Punctual
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.WeilSheaf.UpperStarPointwise

/-!
# Punctual Weil sheaves and dense opens of the affine line

A Weil sheaf on the affine line whose restriction to a nonempty open vanishes is *punctual*: its
support is finite, the complement of a nonempty open of the affine line being a finite set. The
support of a pullback is the preimage of the support.

## Main statements

- `AlgebraicGeometry.WeilSheaf.mem_support_upperStar_iff`: the support of `φ^* F` is the preimage
  of the support of `F`.
- `AlgebraicGeometry.affineLine.finite_setOf_notMem`: a nonempty open of the affine line misses
  only finitely many closed points.
- `AlgebraicGeometry.WeilSheaf.support_finite_of_isZero_upperStar`: a Weil sheaf on the affine
  line vanishing on a nonempty open is punctual.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]

/-- The support of a pullback is the preimage of the support: the stalk of `φ^* F` at a closed
point `y` is the stalk of `F` at `φ(y)`, the two being stalks at the same geometric point. -/
theorem mem_support_upperStar_iff (φ : Y ⟶ X) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l X) (y : Y.finitePoints) :
    y ∈ ((upperStar φ).obj F).support ↔
      (⟨φ.base y.1, Scheme.Hom.map_mem_finitePoints φ y.2⟩ : X.finitePoints) ∈ F.support := by
  refine ⟨mem_support_of_mem_support_upperStar φ F, fun hx ↦ ?_⟩
  have e := asIso (stalkObjHomOfUpperStar φ ((upperStar φ).obj F) (𝟙 _)
    ((Y ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint y))
  have h1 := (nontrivial_stalk_iff_nontrivial_stalkObj F
    ⟨φ.base y.1, Scheme.Hom.map_mem_finitePoints φ y.2⟩
    ((Y ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint y ≫
      Scheme.Hom.geometricFiberMap φ (comp_over φ _)) (by
      rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj, ← Category.assoc]
      exact congrArg φ.base
        (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base _ y))).1 hx
  change Nontrivial ((WeilCoefficients.toModuleCat l).obj (((upperStar φ).obj F).stalkObj
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint y)))
  exact @Equiv.nontrivial _ _ (WeilCoefficients.linearEquivOfIso e).symm.toEquiv h1

end WeilSheaf

/-- A nonempty open of the affine line misses only finitely many closed points: the affine line
is a Noetherian space of dimension one. -/
theorem affineLine.finite_setOf_notMem {k₀ : Type u} [Field k₀] {O : Set (affineLine k₀)}
    (hO : IsOpen O) (hne : O.Nonempty) :
    {x : (affineLine k₀).finitePoints | x.1 ∉ O}.Finite := by
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  have : IsNoetherian (affineLine k₀) :=
    isNoetherian_of_locallyOfFiniteType (affineLine k₀ ↘ Spec (.of k₀))
  have hdim := topologicalKrullDim_le_of_smoothOfRelativeDimension
    (affineLine k₀ ↘ Spec (.of k₀)) 1
  exact (hO.finite_compl_of_topologicalKrullDim_le_one (by exact_mod_cast hdim) hne).preimage
    Subtype.val_injective.injOn

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]

/-- The support of a Weil sheaf `G` on the affine line lies in the union of the closed points
outside a nonempty open `j : U ↪ 𝔸¹` and the image of the support of `j^* G`; in particular it is
finite as soon as that of `j^* G` is. -/
theorem support_finite_of_support_upperStar_finite (j : U ⟶ affineLine k₀) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] [Nonempty U] (G : WeilSheaf k₀ l (affineLine k₀))
    (hG : ((upperStar j).obj G).support.Finite) : G.support.Finite := by
  refine ((affineLine.finite_setOf_notMem j.isOpenEmbedding.isOpen_range
    (Set.range_nonempty _)).union (hG.image fun y ↦
      (⟨j.base y.1, Scheme.Hom.map_mem_finitePoints j y.2⟩ :
        (affineLine k₀).finitePoints))).subset fun x hx ↦ ?_
  by_cases hr : x.1 ∈ Set.range j.base
  · obtain ⟨y, hy⟩ := hr
    have hy' : y ∈ U.finitePoints := Scheme.Hom.mem_finitePoints_of_isOpenImmersion j (hy ▸ x.2)
    refine Or.inr ⟨⟨y, hy'⟩, (mem_support_upperStar_iff j G ⟨y, hy'⟩).2 ?_, ?_⟩
    · convert hx
    · exact Subtype.ext hy
  · exact Or.inl hr

/-- A Weil sheaf on the affine line vanishing on a nonempty open is punctual. -/
theorem support_finite_of_isZero_upperStar (j : U ⟶ affineLine k₀) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] [Nonempty U] (G : WeilSheaf k₀ l (affineLine k₀))
    (hG : IsZero ((upperStar j).obj G)) : G.support.Finite := by
  refine support_finite_of_support_upperStar_finite j G ?_
  rw [support_eq_empty_of_isZero hG]
  exact Set.finite_empty

end WeilSheaf

end AlgebraicGeometry
