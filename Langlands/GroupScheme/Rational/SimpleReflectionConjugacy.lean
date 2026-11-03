import Langlands.GroupScheme.Rational.StandardRelativeWeylGenerationReduction

/-! # Conjugacy of simple relative reflections and positive root labels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

/-- The actual quotient action carries a relative reflection to the reflection
in the image of its root. -/
theorem IsRelativeReflection.conj {α : characterLattice T} {r : relativeWeylGroup i}
    (h : IsRelativeReflection i α r) (w : relativeWeylGroup i) :
    IsRelativeReflection i (schemeWeylCharacterAction i w α) (w * r * w⁻¹) := by
  obtain ⟨hα, f, hf, hr⟩ := h
  have hβ : schemeWeylCharacterAction i w α ∈ relativeRoots i := by
    rw [← schemeWeylCharacterAction_image_relativeRoots i w]
    exact ⟨α, hα, rfl⟩
  have hvec : relativeWeylAction i w ⟨toRat α, toRat_mem_ratSpan hα⟩ =
      ⟨toRat (schemeWeylCharacterAction i w α), toRat_mem_ratSpan hβ⟩ := by
    apply Subtype.ext
    rw [coe_relativeWeylAction_apply_eq_ratAut, ratAut_toRat]
  let g : Module.Dual ℚ (relativeRootSpan i) :=
    f.comp (relativeWeylAction i w).symm.toLinearMap
  have hg : g ⟨toRat (schemeWeylCharacterAction i w α), toRat_mem_ratSpan hβ⟩ = 2 := by
    change f ((relativeWeylAction i w).symm _) = 2
    rw [← hvec, LinearEquiv.symm_apply_apply]
    exact hf
  refine ⟨hβ, g, hg, ?_⟩
  rw [map_mul, map_mul, map_inv, hr]
  apply LinearEquiv.ext
  intro x
  simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, Module.reflection_apply,
    map_sub, map_smul, LinearEquiv.apply_symm_apply, hvec]
  rfl

variable {ν : cocharacterLattice T} {C : CoxeterMatrix (SimpleRoot i ν)}
  {cs : CoxeterSystem C (relativeWeylGroup i)}

/-- Under positivity of the image root, conjugacy of the simple reflections
forces equality of their actual root labels, including in nonreduced systems. -/
theorem IsRelativeWeylCoxeterRealization.root_eq_of_conj_simple
    (h : IsRelativeWeylCoxeterRealization i ν cs)
    (w : relativeWeylGroup i) (a b : SimpleRoot i ν)
    (hpos : schemeWeylCharacterAction i w a.val ∈ positiveRelativeRoots i ν)
    (heq : w * cs.simple a * w⁻¹ = cs.simple b) :
    schemeWeylCharacterAction i w a.val = b.val := by
  obtain ⟨f, hfa, hsf⟩ := h.1 a
  have hsa : schemeWeylCharacterAction i (cs.simple a) a.val = -a.val := by
    rw [hsf, hfa, two_zsmul]
    abel
  have hneg : schemeWeylCharacterAction i (cs.simple b)
      (schemeWeylCharacterAction i w a.val) =
      -schemeWeylCharacterAction i w a.val := by
    rw [← heq]
    simp only [map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply, hsa, map_neg]
  by_contra hne
  have hdouble : schemeWeylCharacterAction i w a.val = 2 • b.val := by
    by_contra hne2
    have hcontr := (h.2.1 b _ hpos hne hne2).2
    rw [hneg, map_neg, LinearMap.neg_apply] at hcontr
    have := hpos.2
    omega
  have ha : a.val = 2 • schemeWeylCharacterAction i w⁻¹ b.val := by
    have hback := congrArg (schemeWeylCharacterAction i w⁻¹) hdouble
    simpa only [map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply, map_nsmul]
      using hback
  have hroot : schemeWeylCharacterAction i w⁻¹ b.val ∈ relativeRoots i := by
    rw [← schemeWeylCharacterAction_image_relativeRoots i w⁻¹]
    exact ⟨b.val, b.property.1.1, rfl⟩
  have hpositive : schemeWeylCharacterAction i w⁻¹ b.val ∈ positiveRelativeRoots i ν := by
    refine ⟨hroot, ?_⟩
    have hpair := congrArg (fun χ => latticePairing T χ ν) ha
    simp only [two_smul, map_add, LinearMap.add_apply] at hpair
    have := a.property.1.2
    omega
  exact a.property.2 ⟨_, hpositive, _, hpositive, by simpa only [two_smul] using ha⟩

/-- The positive simple-reflection conjugacy criterion for a finite actual
relative Weyl group with a scheme Coxeter realization. -/
theorem IsRelativeWeylCoxeterRealization.conj_simple_iff
    [Finite (relativeWeylGroup i)] (hT : IsSplitTorus T.toGrp)
    (h : IsRelativeWeylCoxeterRealization i ν cs)
    (w : relativeWeylGroup i) (a b : SimpleRoot i ν)
    (hpos : schemeWeylCharacterAction i w a.val ∈ positiveRelativeRoots i ν) :
    w * cs.simple a * w⁻¹ = cs.simple b ↔
      schemeWeylCharacterAction i w a.val = b.val := by
  refine ⟨h.root_eq_of_conj_simple w a b hpos, ?_⟩
  intro hab
  have hr := (h.isRelativeReflection_simple a).conj w
  rw [hab] at hr
  exact h.eq_simple_of_isRelativeReflection hT b hr

end Langlands.GroupScheme
