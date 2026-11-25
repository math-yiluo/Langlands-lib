/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenData.ProEtaleClopenTotalTensorKFlatDetectionData
import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenOrdinaryTensorNormalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenStructuralCoproductAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenTotalTensorComparison

/-! Split structural comparison data for finite clopen restriction.

## References

* Stacks Project, Tags 0GMW and 0FPQ
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
attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory

namespace AlgebraicGeometry.Scheme.ProEt

def clopenStructuralPrefix
    {X : Scheme.{t}} {I : Type w} [Finite I] {Y : I → Scheme.{t}}
    {j : ∀ i, Y i ⟶ X} [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    {R : Sheaf (topology X) CommRingCat.{max u (t + 1)}}
    (i : I) (h : (ClopenData.clopenTensorRestriction.{t, u} (j i) R).Braided)
    (b : coefficientTotalTensor.{u, t + 1, t} (topology X) R ⋙
      ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R ≅
      ((ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R).prod
        (ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R)) ⋙
      coefficientTotalTensor.{u, t + 1, t} (topology (Y i))
        ((ClopenData.clopenTensorRings.{t, u} (j i)).obj R)) : Prop :=
  (      (∀ (F H : ClopenData.clopenTensorModules.{t, u} R) (U : (Y i).ProEt)
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
                p (q + 1) (n + 1) hq))))

/-- For each component of a finite clopen partition, restriction is braided and commutes with
the total tensor product of complexes via an isomorphism satisfying the normalized pure-tensor,
summand and differential clauses of `clopenStructuralPrefix`. -/
theorem clopen_structural_comparison_prefix
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    ∀ i, ∃ (h : (ClopenData.clopenTensorRestriction.{t, u} (j i) R).Braided)
      (b : coefficientTotalTensor.{u, t + 1, t} (topology X) R ⋙
          ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R ≅
        ((ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R).prod
          (ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R)) ⋙
            coefficientTotalTensor.{u, t + 1, t} (topology (Y i))
              ((ClopenData.clopenTensorRings.{t, u} (j i)).obj R)),
      clopenStructuralPrefix i h b := by
  intro i
  obtain ⟨h, hpure⟩ := clopen_ordinary_tensor_normalization (j i) R
  let G := ClopenData.clopenTensorRestriction.{t, u} (j i) R
  have hcolim := (clopen_structural_coproduct_adjunction X I Y j hdisjoint hcover R).1 i
  let b := clopenTotalComparison (j i) R h hcolim
  have hsum := clopenTotalComparison_summand (j i) R h hcolim
  refine ⟨h, b, hpure, hsum, ?_⟩
  intro P Q p q n hpq hp hq
  have hc := (b.hom.app (P, Q)).comm n (n + 1)
  change (b.hom.app (P, Q)).f n ≫
      ((coefficientTotalTensor.{u, t + 1, t} (topology (Y i))
        ((ClopenData.clopenTensorRings.{t, u} (j i)).obj R)).obj
        ((ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R).obj P,
          (ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R).obj Q)).d n (n + 1) =
    G.map (((coefficientTotalTensor.{u, t + 1, t} (topology X) R).obj
      (P, Q)).d n (n + 1)) ≫ (b.hom.app (P, Q)).f (n + 1) at hc
  rw [G.map_comp, Category.assoc, ← hc, ← Category.assoc, hsum]
  rw [Category.assoc]
  exact congrArg
    (fun f ↦ (ClopenData.clopenTensorComparison.{t, u} (j i) R h (P.X p) (Q.X q)).hom ≫ f)
    (CochainComplex.ιTensorObj_d
      ((ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R).obj P)
      ((ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R).obj Q)
      p q n (n + 1) hpq rfl)

end AlgebraicGeometry.Scheme.ProEt
