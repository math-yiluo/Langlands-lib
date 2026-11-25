/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardFunctor
import WeilConjectures.AlgebraicGeometry.AffineChartUpperTailLimitComparisons

/-! # The affine chart limit over an upper tail

Source: Stacks Project, Tags 01ZR, 0095, 0097 and 01I6.
(blueprint: new-affine-chart-upper-tail-limit).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The fixed affine chart is the limit of its upper-tail stage charts.
Source: Stacks Project, Limits Tag 01ZR, first proof, affine case.
(blueprint: new-affine-chart-upper-tail-limit).

Proof: Let J be the upper tail above i. On J opposite form the diagram of
Spec(R_j) over Spec(R_i), with transition maps induced by R. Its limit in the over
category is c.pt with structure map c.π_i. Indeed J is final in I: for any k a
common upper bound with i gives an object of J above k, and any two such objects
have a common upper bound. Thus J opposite is initial, so restriction of c is a
limit; the cone lifts to the over category by its equations. Pull back this diagram
along V.X a -> Xi -> Spec(R_i). Over.pullback is a right adjoint and preserves the
limit. The forgetful functor from the over category preserves connected limits;
J is nonempty (it contains i) and directed, hence J opposite is connected.
This gives D and its limiting cone d. Each D_j is affine, because its morphism to
the affine chart V.X a is a base change of a morphism between affine schemes.
Pullback pasting identifies d.pt with Z and D_j with U.X a. It also identifies
the iterated chart Y with Z, by the cone equation at j. The universal property
of the pullbacks gives the two asserted equations: both sides have the same
projections to the original chart and ambient base change, respectively to the
stage chart. Choose these universal-property isomorphisms as z, e and h.
Equivalent preorder indices cause no exception: all identities and compositions
are equations of the induced pullback maps. Empty schemes are treated by the
same universal properties. -/
theorem exists_affine_chart_upper_tail_limit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (V : Xi.OpenCover.{u}) (a : V.I₀) (ha : IsAffine (V.X a)) :
    let W := V.pullback₁ (pullback.fst f (c.π.app (op i)))
    let Z := W.X a
    ∃ (D : ({j : I // i ≤ j})ᵒᵖ ⥤ Scheme.{u}) (d : Cone D),
      Nonempty (IsLimit d) ∧ (∀ j, IsAffine (D.obj j)) ∧
      ∃ z : d.pt ≅ Z, ∀ j : {j : I // i ≤ j},
        let U : (pullback f (Spec.map (R.map (homOfLE j.property)))).OpenCover.{u} :=
          V.pullback₁ (pullback.fst f (Spec.map (R.map (homOfLE j.property))))
        let p := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE j.property))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op j.val)) (c.w (homOfLE j.property).op))
        let Y := (U.pullback₁ p).X a
        ∃ (e : D.obj (op j) ≅ U.X a) (h : Y ≅ Z),
          h.hom ≫ W.f a = (U.pullback₁ p).f a ∧
          h.hom ≫ z.inv ≫ d.π.app (op j) ≫ e.hom = U.pullbackHom p a := by
  let D := upperTailChartDiagram R i (V.f a ≫ f)
  let d := upperTailChartCone R c i (V.f a ≫ f)
  have hd : Nonempty (IsLimit d) := upperTailChartCone_isLimit R c hc i (V.f a ≫ f)
  have haD : ∀ j, IsAffine (D.obj j) := by
    intro j
    let : IsAffine (V.X a) := ha
    change IsAffine (pullback (Spec.map (R.map (homOfLE j.unop.property))) (V.f a ≫ f))
    infer_instance
  obtain ⟨z, hz⟩ := affine_chart_upper_tail_limit_comparisons R c i f V a
  exact ⟨D, d, hd, haD, z, hz⟩

end AlgebraicGeometry
