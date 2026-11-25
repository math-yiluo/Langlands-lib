/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.AffineSectionZeroAtStage
import WeilConjectures.AlgebraicGeometry.SectionBaseChangeZeroPersists

/-!
# Descent of the vanishing of one module section

Source: Stacks Project, Limits, Tag 01ZR (3), affine part of the first proof;
Algebra, Tags 05N7 (3) and 05LI (1).
(blueprint: lem-pc-fp-section-affine-open-eventually-zero).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A single section that vanishes at the limit vanishes at all sufficiently late stages.
Source: Stacks Project, Limits, Tag 01ZR (3), first proof, affine case;
Algebra, Tags 05N7 (3) and 05LI (1).
(blueprint: lem-pc-fp-section-affine-open-eventually-zero).

Proof: put V_j = p_j⁻¹(U). All these opens and the corresponding limit open are affine,
since the projections are base changes of morphisms of affine schemes. Their rings
are the filtered colimit of the stage rings: restrict to the upper tail of j, use
Spec's preservation of limits, and commute the tensor product with the base-ring
colimit. The affine pullback comparison identifies pullback of the section with
1 tensor the section. Apply the already proved
`TensorProduct.directedColimitBaseChangeElementwise` to the unit tensor of y.
Its eventual-zero clause supplies a stage where the unit tensor is zero. The
linear tensor map of every later ring map preserves zero and unit tensors, so
vanishing holds at every stage above this bound. This works directly for preorder
indices; no antisymmetrization or finite matrix construction is needed.
The canonical pure-tensor formula identifies these tensors with the canonical
units. For any other adjunction on the same functors, uniqueness of left adjoints
gives a natural automorphism of the pullback functor identifying the units. Its
component is an isomorphism, so zero is preserved and reflected. Thus the
statement holds for the arbitrary supplied adjunctions as well.
For the empty open the section module is zero; the same argument includes zero
modules and a singleton index preorder. -/
theorem finitePresentation_section_affine_open_eventually_zero
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (j : I) (hij : i ≤ j)
    (G : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules)
    (hG_fp : G.IsFinitePresentation) (hG_qc : G.IsQuasicoherent)
    (U : Xi.Opens) (hU : IsAffineOpen U)
    (y : Γ(G, (pullback.fst f (Spec.map (R.map (homOfLE hij)))) ⁻¹ᵁ U))
    (adjlim : Scheme.Modules.tensorPullback
      (baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))) ⊣
      Scheme.Modules.pushforward
        (baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))))
    (adjstage : ∀ (k : I) (hjk : j ≤ k),
      let g := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (Over.homMk (Spec.map (R.map (homOfLE hjk)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      Scheme.Modules.tensorPullback g ⊣ Scheme.Modules.pushforward g)
    (hy : (adjlim.unit.app G).val.app
      (op ((pullback.fst f (Spec.map (R.map (homOfLE hij)))) ⁻¹ᵁ U)) y = 0) :
    ∃ (l : I), j ≤ l ∧ ∀ (k : I) (hjk : j ≤ k), l ≤ k →
      ((adjstage k hjk).unit.app G).val.app
        (op ((pullback.fst f (Spec.map (R.map (homOfLE hij)))) ⁻¹ᵁ U)) y = 0 := by
  have hG : G.IsFinitePresentation ∧ G.IsQuasicoherent := ⟨hG_fp, hG_qc⟩
  obtain ⟨l, hjl, hl⟩ := section_affine_open_zero_at_stage
    R c hc i f j hij G hG.2 U hU y adjlim adjstage hy
  refine ⟨l, hjl, ?_⟩
  exact section_baseChange_zero_persists R i f j hij G U y adjstage l hjl hl

end AlgebraicGeometry
