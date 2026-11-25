/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenStructuralComparisonPrefix

/-! Split structural comparison data for finite clopen restriction.

## References

* Stacks Project, Tag 0GMW
* Stacks Project, Tag 0FPQ
-/

@[expose] public noncomputable section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
universe t u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures
namespace AlgebraicGeometry.Scheme.ProEt

/-! Symmetry completion for the clopen structural comparison. -/

/-- Given the normalized prefix comparison, the total tensor comparison satisfies the signed
Koszul symmetry clause on each summand. -/
theorem clopen_structural_comparison_symmetry
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (i : I) (h : (ClopenData.clopenTensorRestriction.{t, u} (j i) R).Braided)
    (b : coefficientTotalTensor.{u, t + 1, t} (topology X) R ⋙
          ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R ≅
        ((ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R).prod
          (ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R)) ⋙
            coefficientTotalTensor.{u, t + 1, t} (topology (Y i))
              ((ClopenData.clopenTensorRings.{t, u} (j i)).obj R))
    (_hp : clopenStructuralPrefix i h b) :
    ∀ (P Q : CochainComplex (ClopenData.clopenTensorModules.{t, u} R) ℤ)
      (p q n : ℤ) (hqp : q + p = n),
        (ClopenData.clopenTensorRestriction.{t, u} (j i) R).map
            ((p * q).negOnePow • ((β_ (P.X p) (Q.X q)).hom ≫
              ClopenData.clopenTotalTensorSummand.{t, u} R Q P q p n hqp)) ≫
            (b.hom.app (Q, P)).f n =
          (p * q).negOnePow •
            ((ClopenData.clopenTensorComparison.{t, u} (j i) R h (P.X p) (Q.X q)).hom ≫
              (β_ ((ClopenData.clopenTensorRestriction.{t, u} (j i) R).obj (P.X p))
                ((ClopenData.clopenTensorRestriction.{t, u} (j i) R).obj (Q.X q))).hom ≫
              ClopenData.clopenTotalTensorSummand.{t, u}
              ((ClopenData.clopenTensorRings.{t, u} (j i)).obj R)
                ((ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R).obj Q)
                ((ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R).obj P)
                q p n hqp) := by
  intro P Q p q n hqp
  let F := (ClopenData.clopenTensorRestriction.{t, u} (j i) R)
  letI : F.Additive := ClopenData.clopenTensorRestrictionAdditive (j i) R
  change F.map ((p * q).negOnePow • ((β_ (P.X p) (Q.X q)).hom ≫
      ClopenData.clopenTotalTensorSummand.{t, u} R Q P q p n hqp)) ≫
      (b.hom.app (Q, P)).f n = _
  have hsum := _hp.2.1 Q P q p n hqp
  have hμ :
      (ClopenData.clopenTensorRestriction.{t, u} (j i) R).map
          ((β_ (P.X p) (Q.X q)).hom) ≫
        (ClopenData.clopenTensorComparison.{t, u} (j i) R h (Q.X q) (P.X p)).hom =
      (ClopenData.clopenTensorComparison.{t, u} (j i) R h (P.X p) (Q.X q)).hom ≫
        (β_ ((ClopenData.clopenTensorRestriction.{t, u} (j i) R).obj (P.X p))
          ((ClopenData.clopenTensorRestriction.{t, u} (j i) R).obj (Q.X q))).hom := by
    letI := h
    apply (cancel_mono (Functor.LaxMonoidal.μ F (Q.X q) (P.X p))).1
    simpa [ClopenData.clopenTensorComparison, Category.assoc] using
      (Functor.LaxBraided.braided (F := F) (P.X p) (Q.X q)).symm
  have hμ' :
      F.map ((β_ (P.X p) (Q.X q)).hom) ≫
          (ClopenData.clopenTensorComparison.{t, u} (j i) R h (Q.X q) (P.X p)).hom =
        (ClopenData.clopenTensorComparison.{t, u} (j i) R h (P.X p) (Q.X q)).hom ≫
          (β_ (F.obj (P.X p)) (F.obj (Q.X q))).hom := hμ
  have hbase0 := congrArg
    (fun f ↦ F.map ((β_ (P.X p) (Q.X q)).hom) ≫ f) hsum
  have hbase := hbase0
  have hμ'_assoc := reassoc_of% hμ'
  rw [hμ'_assoc] at hbase
  rw [Functor.map_units_smul, Functor.map_comp]
  simp only [Linear.units_smul_comp, Category.assoc]
  exact congrArg (fun f ↦ (p * q).negOnePow • f) hbase

end AlgebraicGeometry.Scheme.ProEt
