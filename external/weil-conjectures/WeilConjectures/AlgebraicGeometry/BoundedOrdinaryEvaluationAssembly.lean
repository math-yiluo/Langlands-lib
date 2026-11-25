/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationSourceBiproduct
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationTargetBiproduct
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationDiagonalBlock
import WeilConjectures.Algebra.Homology.HomComplex

/-! # Finite-support assembly of ordinary evaluation

Source: Stacks Project, Tags 08DQ and 08DM, finite total-complex calculation.
(blueprint: lem-pc-bounded-ordinary-evaluation-assembly).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
attribute [local instance] localEvaluationPreadditive

/-- Assemble evaluation from the degree-zero module comparisons.
Source: Stacks Project, Tag 08DQ, proof of `lemma-dual-perfect-complex`, and
Tag 08DM, proof of `lemma-Rhom-strictly-perfect`.
(blueprint: lem-pc-bounded-ordinary-evaluation-assembly).

Proof: the projection from the dual in degree q to Hom(P^(-q),O) is invertible:
all other targets of the degree-zero complex vanish, hence so do their Hom
objects, and the recorded Hom projections exhibit a product. Bounded support
of P makes the dual bounded. In total degree n, discard the zero tensor
summands and the zero Hom factors outside that same finite support. Products
and coproducts over the remaining finite indices agree in this additive
category. Reindex the tensor summands by r=-q and p=r+n. Under these
identifications the displayed component equations give zero off-diagonal
blocks and the canonical module evaluation on each diagonal block. Each such
block is invertible by hblocks, after tensoring the dual projection and
transporting the degree equality. The finite biproduct of their inverses is
an inverse for f.f n. The product and coproduct universal properties verify
both inverse equations. An empty support gives the unique map between zero
objects. No bound on F and no affineness of U enter the argument.
-/
theorem boundedOrdinaryEvaluation_degree (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (P.X r))
    (hblocks : ∀ (r : ℤ) (B : localEvaluationModules X U),
      IsIso (SheafOfModules.moduleDualEvaluation (X.sheaf.over U) (P.X r) B))
    (n : ℤ)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (hf : IsLocalOrdinaryEvaluation X U P F f) : IsIso (f.f n) := by
  classical
  obtain ⟨a, b, hab⟩ := hbounded
  let S : ↥(Finset.Icc a b) → localEvaluationModules X U := fun r ↦
    F.X (r.val + n) ⊗ (localEvaluationDual X U P).X (-r.val)
  let T : ↥(Finset.Icc a b) → localEvaluationModules X U := fun r ↦
    SheafOfModules.homObj (R := X.sheaf.over U) (P.X r.val) (F.X (r.val + n))
  let d : ∀ r, S r ⟶ T r := fun r ↦
    localEvaluationComponent X U P F (r.val + n) (-r.val) n r.val (by omega)
  have hd (r : ↥(Finset.Icc a b)) : IsIso (d r) :=
    ordinaryEvaluation_diagonal_block X U P F n r.val (hblocks r.val _)
  obtain ⟨s, hs⟩ := ordinaryEvaluation_source_biproduct X U P F a b n hab
  obtain ⟨t, ht⟩ := ordinaryEvaluation_target_biproduct X U P F a b n hab
  have heq : s.hom ≫ f.f n ≫ t.hom = (biproduct.mapIso fun r ↦ asIso (d r)).hom := by
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    simp only [Category.assoc]
    rw [ht]
    simp only [← Category.assoc]
    rw [hs]
    simp only [Category.assoc]
    rw [hf]
    by_cases hij : i = j
    · subst j
      simp [biproduct.mapIso_hom, d, S, T]
    · have hne : j.val + -i.val ≠ 0 := by
        intro h
        apply hij
        apply Subtype.ext
        omega
      simp only [localEvaluationComponent, dite_eq_right hne, biproduct.mapIso_hom,
        biproduct.ι_map_assoc, asIso_hom]
      change 0 = d i ≫ biproduct.ι T i ≫ biproduct.π T j
      rw [biproduct.ι_π_ne T hij, comp_zero]
  have hfactor : f.f n = s.inv ≫ (biproduct.mapIso fun r ↦ asIso (d r)).hom ≫ t.inv := by
    rw [← heq]
    simp
  rw [hfactor]
  infer_instance

end AlgebraicGeometry
