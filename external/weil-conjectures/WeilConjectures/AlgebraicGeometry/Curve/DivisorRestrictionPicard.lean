/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Curve.Picard
import WeilConjectures.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial
import WeilConjectures.AlgebraicGeometry.Curve.PicRestrictionPointLift

/-! # Divisor restriction across a smooth curve compactification -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Restricting a divisor retains its coefficients and computes Picard pullback.
Source: blueprint, sec-curve-estimates/lem-sc-arbitrary-curve-cd/lem-sc-pic-affine, first paragraph,
restriction and boundary divisors
(blueprint: lem-sc-divisor-restriction-picard).

Proof: the open immersion is injective on points and identifies the local rings. A closed
point of C maps to a closed point of Z because it is rational over the algebraically closed
field and Z is separated over that field. Conversely a closed point of Z in the image has a
closed preimage by continuity and injectivity. Retain just the coefficients at these points;
this constructs a finitely supported divisor R on C. On a retained point the point-lift
comparison identifies the pullback of its point-ideal class with the class on C. On an omitted
point the boundary-triviality comparison gives the identity. Induct on the finite sum of
point divisors, using additivity and integer powers to obtain the Picard equality. If D is
zero, take R zero; if the boundary is empty every coefficient is retained. -/
theorem Scheme.Hom.exists_divisor_restriction_picard
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (c : Compactification f) [IsConnectedCurve c.g]
    [hsm : SmoothOfRelativeDimension 1 c.g]
    [hC : SmoothOfRelativeDimension 1 f] (D : c.Z.Divisor) :
    ∃ R : C.Divisor,
      (@Scheme.Divisor.toPic k _ C ⟨f⟩ hC R).toMul =
        Scheme.Pic.mapHom c.i (@Scheme.Divisor.toPic k _ c.Z ⟨c.g⟩ hsm D).toMul ∧
      ∀ P : closedPoints c.Z, P.val ∈ Set.range c.i.base →
        ∃ Q : closedPoints C, c.i.base Q.val = P.val ∧ D P = R Q := by
  classical
  let : C.Over (Spec (.of k)) := ⟨f⟩
  let : c.Z.Over (Spec (.of k)) := ⟨c.g⟩
  let : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) := by
    change SmoothOfRelativeDimension 1 f
    exact hC
  let : SmoothOfRelativeDimension 1 (c.Z ↘ Spec (.of k)) := by
    change SmoothOfRelativeDimension 1 c.g
    exact hsm
  have hinj := c.i.isOpenEmbedding.injective
  have hpre (P : closedPoints c.Z) (hP : P.val ∈ Set.range c.i.base) :
      ∃ Q : closedPoints C, c.i.base Q.val = P.val := by
    obtain ⟨q, hq⟩ := hP
    have he : c.i.base ⁻¹' ({P.val} : Set c.Z) = {q} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hx ↦ hinj (hx.trans hq.symm), fun hx ↦ hx ▸ hq⟩
    have hc : IsClosed ({q} : Set C) := by
      rw [← he]
      exact P.property.preimage c.i.continuous
    exact ⟨⟨q, hc⟩, hq⟩
  induction D using Finsupp.induction_linear with
  | zero =>
      refine ⟨0, ?_, ?_⟩
      · exact (map_one (Scheme.Pic.mapHom c.i)).symm
      · intro P hP
        obtain ⟨Q, hQ⟩ := hpre P hP
        exact ⟨Q, hQ, by simp⟩
  | @add D₁ D₂ ih₁ ih₂ =>
      obtain ⟨R₁, hR₁, hcoeff₁⟩ := ih₁
      obtain ⟨R₂, hR₂, hcoeff₂⟩ := ih₂
      refine ⟨R₁ + R₂, ?_, ?_⟩
      · simp only [map_add, toMul_add, map_mul]
        rw [hR₁, hR₂]
      · intro P hP
        obtain ⟨Q₁, hQ₁, h₁⟩ := hcoeff₁ P hP
        obtain ⟨Q₂, hQ₂, h₂⟩ := hcoeff₂ P hP
        have hqi : Q₁ = Q₂ := Subtype.ext (hinj (hQ₁.trans hQ₂.symm))
        subst Q₂
        refine ⟨Q₁, hQ₁, ?_⟩
        simp only [Finsupp.add_apply]
        rw [h₁, h₂]
  | single P n =>
      by_cases hP : P.val ∈ Set.range c.i.base
      · obtain ⟨Q, hQ⟩ := hpre P hP
        obtain ⟨P₁, hP₁, hpic⟩ := f.pic_restriction_point_lift c Q
        have he : P₁ = P := Subtype.ext (hP₁.trans hQ)
        subst P₁
        refine ⟨Finsupp.single Q n, ?_, ?_⟩
        · simp only [Scheme.Divisor.toPic_single, toMul_zsmul, toMul_ofMul, map_zpow]
          rw [hpic]
        · intro P' hP'
          obtain ⟨Q', hQ'⟩ := hpre P' hP'
          refine ⟨Q', hQ', ?_⟩
          have heq : P' = P ↔ Q' = Q := by
            constructor
            · intro he
              apply Subtype.ext
              exact hinj (hQ'.trans ((congrArg Subtype.val he).trans hQ.symm))
            · intro he
              apply Subtype.ext
              exact hQ'.symm.trans ((congrArg (fun q : closedPoints C ↦ c.i.base q.val)
                he).trans hQ)
          simp only [Finsupp.single_apply]
          have heq' : P = P' ↔ Q = Q' := by
            exact ⟨fun h ↦ (heq.mp h.symm).symm, fun h ↦ (heq.mpr h.symm).symm⟩
          simp only [heq']
      · refine ⟨0, ?_, ?_⟩
        · simp only [map_zero, toMul_zero, Scheme.Divisor.toPic_single,
            toMul_zsmul, toMul_ofMul, map_zpow]
          rw [f.pic_restriction_boundary_trivial c P hP, one_zpow]
        · intro P' hP'
          obtain ⟨Q', hQ'⟩ := hpre P' hP'
          refine ⟨Q', hQ', ?_⟩
          have he : P' ≠ P := by
            intro he
            apply hP
            exact he ▸ hP'
          simp [he]


end AlgebraicGeometry
