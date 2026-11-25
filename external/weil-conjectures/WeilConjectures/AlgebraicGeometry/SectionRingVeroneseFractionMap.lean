/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-! # The explicit map from Veronese numerator sections to homogeneous fractions

Source: Stacks Project, Properties, Tag 0B5L and Lemma 01PW(2).
The data are constructed from tensor-power isomorphisms, direct-sum injections and
`HomogeneousLocalization.Away.mk`; no existence witness is used.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory DirectSum

namespace AlgebraicGeometry.Scheme.Modules

/-- The numerator identification in degree `n`. Source: Stacks Project, Properties,
Tag 0B5L, Lemma 01PW(2) (blueprint: def-sc-section-ring-veronese-fraction-map). -/
noncomputable def sectionRingVeroneseNumeratorIso
    (X : Scheme.{u}) (L : X.Modules) (d n : ℕ) :
    L.tensorPow (n • d) ≅ (𝟙_ X.Modules) ⊗ (L.tensorPow d).tensorPow n :=
  eqToIso (congrArg L.tensorPow (by simp [Nat.mul_comm])) ≪≫
    L.tensorPowMulIso d n ≪≫ (λ_ _).symm

/-- Send a homogeneous numerator to its fraction with denominator `s^n`.
Source: Stacks Project, Properties, Tag 0B5L
(blueprint: def-sc-section-ring-veronese-fraction-map). Additivity follows by adding
fractions with the same denominator in the ambient localization. -/
noncomputable def sectionRingVeroneseHomogeneousFraction
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) (n : ℕ) :
    sectionRingGrade L (n • d) →+
      HomogeneousLocalization.Away (sectionRingGrade L) s.val where
  toFun ξ := HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
    ξ.val ξ.property
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
      AddSubgroup.coe_zero]
    exact Localization.mk_zero _
  map_add' ξ η := by
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_add,
      AddSubgroup.coe_add]
    exact (Localization.add_mk_self _ _ _).symm

/-- The reverse numerator identification followed by the graded injection.
Source: Stacks Project, Properties, Tag 0B5L, Lemma 01PW(2)
(blueprint: def-sc-section-ring-veronese-fraction-map). -/
noncomputable def sectionRingVeroneseNumerator
    (X : Scheme.{u}) (L : X.Modules) (d n : ℕ) :
    Γ((𝟙_ X.Modules) ⊗ (L.tensorPow d).tensorPow n, ⊤) →+
      sectionRingGrade L (n • d) :=
  ((DirectSum.of (SectionRingComponent L) (n • d)).rangeRestrict).comp
    ((sectionRingVeroneseNumeratorIso X L d n).inv.app ⊤).hom

/-- The explicit additive map on the direct sum of numerator sections.
Source: Stacks Project, Properties, Tag 0B5L, Lemma 01PW(2)
(blueprint: def-sc-section-ring-veronese-fraction-map). Its `n`-th component is the
fraction with numerator given by the inverse tensor-power identification and denominator `s^n`.
-/
noncomputable def sectionRingVeroneseFractionMap
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) :
    (⨁ n : ℕ, Γ((𝟙_ X.Modules) ⊗ (L.tensorPow d).tensorPow n, ⊤)) →+
      HomogeneousLocalization.Away (sectionRingGrade L) s.val :=
  DirectSum.toAddMonoid fun n ↦
    (sectionRingVeroneseHomogeneousFraction X L d s n).comp
      (sectionRingVeroneseNumerator X L d n)

/-- The numerator identification cancels on a homogeneous component.
Source: Stacks Project, Properties, Lemma 01PW(2)
(blueprint: def-sc-section-ring-veronese-fraction-map).
Use membership in the image of the graded injection, evaluate in its degree, and cancel
an isomorphism with its inverse. -/
theorem sectionRingVeroneseNumerator_cancel
    (X : Scheme.{u}) (L : X.Modules) (d n : ℕ)
    (ξ : sectionRingGrade L (n • d)) :
    sectionRingVeroneseNumerator X L d n
      ((sectionRingVeroneseNumeratorIso X L d n).hom.app ⊤ (ξ.val (n • d))) = ξ := by
  obtain ⟨t, ht⟩ := ξ.property
  apply Subtype.ext
  change DirectSum.of (SectionRingComponent L) (n • d)
    ((sectionRingVeroneseNumeratorIso X L d n).inv.app ⊤
      ((sectionRingVeroneseNumeratorIso X L d n).hom.app ⊤ (ξ.val (n • d)))) = ξ.val
  rw [← ht]
  simp only [DirectSum.of_eq_same]
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.hom_inv_id, Hom.id_app]
  rfl

/-- Every homogeneous fraction is in the image of the explicit direct-sum map.
Source: Stacks Project, Properties, Tag 0B5L
(blueprint: def-sc-section-ring-veronese-fraction-map).
Choose a representative `ξ/s^n` using `Away.mk_surjective`, and use the `n`-th summand
with numerator transported by the tensor-power isomorphism. The preceding cancellation
identity gives its image. This includes degree zero and zero or nilpotent denominators. -/
theorem sectionRingVeroneseFractionMap_surjective
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) :
    Function.Surjective (sectionRingVeroneseFractionMap X L d s) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (sectionRingGrade L) s.property z
  refine ⟨DirectSum.of
    (fun n : ℕ ↦ Γ((𝟙_ X.Modules) ⊗ (L.tensorPow d).tensorPow n, ⊤)) n
    ((sectionRingVeroneseNumeratorIso X L d n).hom.app ⊤ (a (n • d))), ?_⟩
  simp only [sectionRingVeroneseFractionMap, DirectSum.toAddMonoid_of,
    AddMonoidHom.comp_apply]
  rw [sectionRingVeroneseNumerator_cancel X L d n ⟨a, ha⟩]
  rfl

end AlgebraicGeometry.Scheme.Modules
