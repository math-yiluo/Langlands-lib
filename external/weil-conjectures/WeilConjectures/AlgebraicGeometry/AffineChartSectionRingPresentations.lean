/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.AffineChartUpperTailLimitData
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Order.Antisymmetrization
import WeilConjectures.AlgebraicGeometry.AffineChartSectionRingPresentationsTail
import WeilConjectures.AlgebraicGeometry.AffineChartSectionRingPresentationsIso

/-! # Ring presentations of affine upper-tail charts

Source: Stacks Project, Tag 01ZR, affine proof; Tags 0095 and 0096.
(blueprint: lem-pc-affine-chart-section-ring-presentations).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The module-independent ring comparison for the direct and finite-stage charts.
Source: Stacks Project, Tag 01ZR, affine proof; Tags 0095 and 0096.
(blueprint: lem-pc-affine-chart-section-ring-presentations).

Proof: The representative of the class of j is both above and below j.
The two preorder arrows are inverse, hence Spec of the ring transition is an
isomorphism. Its pullback s is an isomorphism as well. Restrict the limiting
spectrum cone to the upper tail and pull back to U(a); upperTailChartCone_isLimit
gives a limit cone. The representative functor from the antisymmetrization is
an equivalence of preorder categories: its inverse is the quotient functor,
and the two natural isomorphisms are the unique arrows between equivalent
representatives. Reindex the cone along this equivalence. Each chart is a
pullback of affine schemes over Spec R(j), and its vertex is a pullback of the
affine cone vertex and U(a), so all are affine. The equivalence between affine
schemes opposite and commutative rings sends this limit to a colimit of F.
Compare this colimit with the chosen colimit to obtain the vertex ring
isomorphism. Pullback pasting identifies the vertex with the direct cover
chart and identifies each stage with its corresponding cover chart. Composing
the section-ring isomorphisms of these pasting maps gives ρ₀ and ρₓ. Comparing
the projections to U(a) gives the two equations on elements b of Γ(U(a)).
The limiting-cone equation at x gives the equality on the iterated chart:
compose both sides with the section maps of its projections; the projections
of the two pasting isomorphisms agree by pullback uniqueness. This is the last
displayed equation. The proof applies to empty affine charts and the zero ring.
No module, quasi-coherence, or finite-presentation assertion is used. -/
theorem affine_chart_section_ring_presentations
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    (a : U.I₀) (ha : IsAffine (U.X a))
    :
    let rep := (OrderEmbedding.ofAntisymmetrization
      (α := {k : I // j ≤ k})).monotone.functor
    let g := U.f a ≫ pullback.snd f (Spec.map (R.map (homOfLE hij)))
    let F := rep ⋙ (upperTailChartDiagram R j g).rightOp ⋙ Scheme.Γ
    let t := toAntisymmetrization (· ≤ ·) (⟨j, le_rfl⟩ : {k : I // j ≤ k})
    let kₜ := rep.obj t
    let s := pullback.snd (Spec.map (R.map (homOfLE kₜ.property))) g
    let r₀ := (colimit.ι F t).hom
    let q₀ := baseChangeMap f
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (c.π.app (op i)))
      (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
    IsIso s ∧ IsAffine ((U.pullback₁ q₀).X a) ∧
    ∃ (ρ₀ : ↑(colimit F) ≃+* Γ((U.pullback₁ q₀).X a, ⊤)),
      (∀ b, ρ₀ (r₀ (s.appTop b)) = (U.pullbackHom q₀ a).appTop b) ∧
      ∀ (x : Antisymmetrization {k : I // j ≤ k} (· ≤ ·)) (htx : t ≤ x),
        let k := (rep.obj x).val
        let hjk := (rep.obj x).property
        let q := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
          (Over.homMk (Spec.map (R.map (homOfLE hjk)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let p := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
        let q₀ := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
        let w : p ≫ q = q₀ := by
          rw [← baseChangeMap_comp]
          congr 1
          ext
          simpa using c.w (homOfLE hjk).op
        let r := (F.map (homOfLE htx)).hom
        let r₁ := (colimit.ι F x).hom
        let Uk : (pullback f (Spec.map
          (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u} := U.pullback₁ q
        let V : (pullback f (c.π.app (op i))).OpenCover.{u} := Uk.pullback₁ p
        let v : V.X a ⟶ (U.pullback₁ q₀).X a := pullback.lift (V.f a)
          (Uk.pullbackHom p a ≫ U.pullbackHom q a)
          (by
            dsimp only [V]
            rw [Category.assoc, U.pullbackHom_map,
              ← Category.assoc, Uk.pullbackHom_map, Category.assoc, w])
        ∃ (ρₓ : ↑(F.obj x) ≃+* Γ((U.pullback₁ q).X a, ⊤)),
          (∀ b, ρₓ (r (s.appTop b)) = (U.pullbackHom q a).appTop b) ∧
          IsAffine (Uk.X a) ∧
          (∀ b, v.appTop (ρ₀ (r₁ b)) = (Uk.pullbackHom p a).appTop (ρₓ b)) := by
  classical
  intro rep g F t kₜ s r₀ q₀
  have hi := affine_chart_section_ring_presentations_iso R j g
  have ht := affine_chart_section_ring_presentations_tail R c hc i f j hij U a ha
  exact ⟨hi, ht⟩

end AlgebraicGeometry
