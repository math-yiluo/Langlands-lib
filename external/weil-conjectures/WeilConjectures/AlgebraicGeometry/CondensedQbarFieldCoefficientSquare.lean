/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation

import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting

/-! # The coefficient square for geometric field evaluation

Source: RefactorInstruction, Section 4, coefficient realization and geometric fibers.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private theorem hom_ext {A B : Ab.{u + 1}} {f g : A ⟶ B}
    (h : ∀ a : A, f.hom a = g.hom a) : f = g :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext h)

/-- The geometric evaluation comparison has the same bounded-coefficient coordinates
on both algebraically closed fields.

Source: RefactorInstruction, Section 4, coefficient realization and geometric fibers
(auxiliary; not a blueprint node).

Proof in words: write q_K for the structural map from the singleton relative profinite
object to the final object, eta_K for the point-adjunction unit on the coefficient
sheaf, and e_K for fieldCoefficientIso. Fix a scalar r and its constant bounded
function a on the singleton. The proved theorem
condensedQbar_field_point_coefficient_value says that eta_K(a) equals restriction
along q_K of e_K inverse(r); it gives the identical statement for K'.

The pullback coefficient morphism alpha is the component of upperStarFromPointComp.
Its defining composition comparison is conjugate to the direct-image fibre-product
comparison. The unit identity for conjugateEquiv, whiskered by the point adjunction,
therefore says that eta_K(a), followed by the restriction comparison and alpha at
the singleton test object, equals eta_K'(a). This is the usual pasting identity for
the units of the three composed adjunctions, with comp_toSpecZ identifying their
common composite. It uses the specified comparisons throughout.

The first identity of geometric_field_proetale_evaluation_coherence moves q_K past
the evaluation comparison. Naturality of alpha then moves q_K' past alpha. Together
with the two normalized values, these equations say that evaluation comparison,
followed by alpha at the terminal object, sends e_K inverse(r) to e_K' inverse(r)
after restriction along q_K'. The structural map q_K' is invertible by
geometric_field_proetale_evaluation, so its restriction map is injective. Cancel it.
Extensionality in r gives the forward coefficient square. Finally postcompose with
the evaluated inverse of alpha and cancel alpha to obtain the displayed equation.
The argument applies to identity embeddings, zero scalars, and transcendental field
extensions; it uses no algebraicity of the embedding. -/
theorem condensedQbar_field_coefficient_square (ℓ : ℕ) [Fact ℓ.Prime]
    (K K' : Type u) [Field K] [IsAlgClosed K] [Field K'] [IsAlgClosed K']
    (i : K →+* K') :
    let f := Spec.map (CommRingCat.ofHom i)
    let A := condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K))
    let E' := sheafToPresheaf (Scheme.ProEt.topology (Spec (.of K'))) Ab.{u + 1} ⋙
      (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of K')))))
    inv (CondensedQbarGeometricEvaluation.fieldCoefficientIso K ℓ).hom.hom ≫
      (geometricFieldEvaluationComparison f Ab).app A =
    inv (CondensedQbarGeometricEvaluation.fieldCoefficientIso K' ℓ).hom.hom ≫
      E'.map (inv (condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) f)) := by
  dsimp only
  apply hom_ext
  intro r
  obtain ⟨r⟩ := r
  have hr : _root_.IsIntegral ℚ_[ℓ] r := Algebra.IsIntegral.isIntegral r
  let S := Profinite.of (ULift.{u, 0} PUnit.{1})
  let a : PadicAlgCl.finiteIntermediateFieldValued ℓ S :=
    ⟨ContinuousMap.const _ r,
      ⟨IntermediateField.adjoin ℚ_[ℓ] {r}, IntermediateField.adjoin.finiteDimensional hr,
        fun _ ↦ IntermediateField.subset_adjoin ℚ_[ℓ] _ (Set.mem_singleton r)⟩⟩
  exact CondensedCoefficientUnit.terminal_transport K K' i
    (Profinite.padicAlgClRingObj ℓ) (ULift.up a)
    ((inv (CondensedQbarGeometricEvaluation.fieldCoefficientIso K ℓ).hom.hom).hom
      (ULift.up r))
    (condensedQbar_field_point_coefficient_value ℓ K a)
    ((inv (CondensedQbarGeometricEvaluation.fieldCoefficientIso K' ℓ).hom.hom).hom
      (ULift.up r))
    (condensedQbar_field_point_coefficient_value ℓ K' a)

end AlgebraicGeometry.ProEtale
