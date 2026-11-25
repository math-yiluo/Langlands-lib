/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenData.ProEtaleClopenTotalTensorKFlatDetectionData
import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenStructuralComparisonPrefix
import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenStructuralComparisonSymmetry

/-! Split structural comparison data for finite clopen restriction.

## References

* Stacks Project, Tag 0GMW
* Tag 0FPQ
-/

@[expose] public noncomputable section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
universe t u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures
namespace AlgebraicGeometry.Scheme.ProEt

theorem clopen_structural_comparison
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    (∀ i, ∃ (h : (ClopenData.clopenTensorRestriction.{t, u} (j i) R).Braided)
      (b : coefficientTotalTensor.{u, t + 1, t} (topology X) R ⋙
          ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R ≅
        ((ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R).prod
          (ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R)) ⋙
            coefficientTotalTensor.{u, t + 1, t} (topology (Y i))
              ((ClopenData.clopenTensorRings.{t, u} (j i)).obj R)),
      (∀ (F H : ClopenData.clopenTensorModules.{t, u} R) (U : (Y i).ProEt)
        (x : F.val.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale (j i))).obj U)))
        (y : H.val.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale (j i))).obj U))),
        (ClopenData.clopenTensorComparison.{t, u} (j i) R h F H).hom.val.app (op U)
          (ClopenData.clopenTensorPure.{t, u} R F H _ x y) =
        ClopenData.clopenTensorPure.{t, u} ((ClopenData.clopenTensorRings.{t, u} (j i)).obj R)
          ((ClopenData.clopenTensorRestriction.{t, u} (j i) R).obj F)
          ((ClopenData.clopenTensorRestriction.{t, u} (j i) R).obj H) (op U) x y) ∧
      (∀ (P Q : CochainComplex (ClopenData.clopenTensorModules.{t, u} R) ℤ)
        (p q n : ℤ) (hpq : p + q = n),
        (ClopenData.clopenTensorRestriction.{t, u} (j i) R).map
            (ClopenData.clopenTotalTensorSummand.{t, u} R P Q p q n hpq) ≫ (b.hom.app (P, Q)).f n =
          (ClopenData.clopenTensorComparison.{t, u} (j i) R h (P.X p) (Q.X q)).hom ≫
            ClopenData.clopenTotalTensorSummand.{t, u}
              ((ClopenData.clopenTensorRings.{t, u} (j i)).obj R)
              ((ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R).obj P)
              ((ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R).obj Q) p q n hpq) ∧
      (∀ (P Q : CochainComplex (ClopenData.clopenTensorModules.{t, u} R) ℤ)
        (p q n : ℤ) (hpq : p + q = n)
        (hp : (p + 1) + q = n + 1) (hq : p + (q + 1) = n + 1),
        (ClopenData.clopenTensorRestriction.{t, u} (j i) R).map
            (ClopenData.clopenTotalTensorSummand.{t, u} R P Q p q n hpq ≫
              ((coefficientTotalTensor.{u, t + 1, t} (topology X) R).obj
                (P, Q)).d n (n + 1)) ≫
              (b.hom.app (P, Q)).f (n + 1) =
          (ClopenData.clopenTensorComparison.{t, u} (j i) R h (P.X p) (Q.X q)).hom ≫
            (((ClopenData.clopenTensorRestriction.{t, u} (j i) R).map (P.d p (p + 1)) ▷
                (ClopenData.clopenTensorRestriction.{t, u} (j i) R).obj (Q.X q)) ≫
              ClopenData.clopenTotalTensorSummand.{t, u}
              ((ClopenData.clopenTensorRings.{t, u} (j i)).obj R)
                ((ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R).obj P)
                ((ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R).obj Q)
                (p + 1) q (n + 1) hp +
            p.negOnePow •
              (((ClopenData.clopenTensorRestriction.{t, u} (j i) R).obj (P.X p) ◁
                (ClopenData.clopenTensorRestriction.{t, u} (j i) R).map (Q.d q (q + 1))) ≫
              ClopenData.clopenTotalTensorSummand.{t, u}
              ((ClopenData.clopenTensorRings.{t, u} (j i)).obj R)
                ((ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R).obj P)
                ((ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R).obj Q)
                p (q + 1) (n + 1) hq))) ∧
      (∀ (P Q : CochainComplex (ClopenData.clopenTensorModules.{t, u} R) ℤ)
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
                q p n hqp))) := by
  intro i
  obtain ⟨h, b, hp⟩ := clopen_structural_comparison_prefix X I Y j hdisjoint hcover R i
  refine ⟨h, b, hp.1, hp.2.1, hp.2.2, ?_⟩
  exact clopen_structural_comparison_symmetry X I Y j hdisjoint hcover R i h b hp

end AlgebraicGeometry.Scheme.ProEt
