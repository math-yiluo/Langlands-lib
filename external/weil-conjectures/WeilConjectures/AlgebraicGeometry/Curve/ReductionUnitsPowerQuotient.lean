/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.ReductionUnitsPowerKernel
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.Curve.ReductionUnitsPowerCokernel

/-! # Successive quotients of the nilpotent-units sheaves

Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-reduction-units-power-quotient)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Consecutive nilpotent-units sheaves have an additive quasi-coherent quotient.
This single-step statement needs neither a global nilpotence exponent nor a
Noetherian hypothesis, and concerns only sheaves on X, before reduction pullback.
Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-reduction-units-power-quotient)

Proof: Let N be the nilradical ideal sheaf and set F=N^(j+1)/N^(j+2). Ideal powers
are quasi-coherent, and so is their quotient. On an affine etale object V over X,
base change identifies restriction to the subscheme cut out by N^(j+1) with
restriction of rings modulo the extended ideal. Thus reductionUnitsPowerKernel X j
is the group 1+N^(j+1) O_V. The assignment 1+a to the class of a defines a map to
sections of F: etale flatness identifies the quotient of extended ideals with
the pullback of F, compatibly with restriction. This is a group homomorphism
because the cross term ab belongs to N^(2j+2), which is contained in N^(j+2).
Its kernel is exactly 1+N^(j+2), with its evident inclusion. On etale affines
every quotient class has a lift a in the ideal, and a is nilpotent because the
extended nilradical is a nil ideal. Consequently 1+a is a unit. This proves
local surjectivity, hence an epimorphism of sheaves. These maps give the short
exact sequence, and sectionwise additive-group universe lift preserves it.
The construction also applies when N=0, when X is empty, and when j=0: then the
cross-term inequality is equality. No choices from this theorem define any data. -/
theorem exists_reduction_units_power_quotient (X : Scheme.{u}) (j : ℕ) :
    ∃ (F : X.Modules) (_ : F.IsQuasicoherent)
      (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
      S.ShortExact ∧ Nonempty (S.X₁ ≅ X.reductionUnitsPowerKernel (j + 1)) ∧
      Nonempty (S.X₂ ≅ X.reductionUnitsPowerKernel j) ∧
      Nonempty (S.X₃ ≅
        ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          (Modules.etaleTensorSectionsSheaf F))) := by
  let F := X.reductionIdealPowerQuotient j
  let f := X.reductionUnitsPowerInclusion j
  let S := ShortComplex.cokernelSequence f
  have hS : S.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact f
      mono_f := by
        change Mono f
        exact mono_reductionUnitsPowerInclusion X j }
  refine ⟨F, inferInstance, S, hS, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, ?_⟩
  exact nonempty_reductionUnitsPowerCokernelIso X j

end AlgebraicGeometry.Scheme
