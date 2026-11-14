import Langlands.GroupScheme.GaloisCocycleFiniteRecovery
import Langlands.GroupScheme.IntegralModel.InnerSemilinearCoherence
import Langlands.GroupScheme.IntegralModel.SemilinearCoefficientDescent

/-! # Recovery of inner-twisted semilinear maps from finite coefficients -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.IntegralModel

open GaloisPointComparison Descent

/-- The original-group projection determines a section of a pulled-back group. -/
theorem baseChangedPoint_ext {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)
    (x y : Over.mk (𝟙 T) ⟶ ((GroupScheme.baseChange b).obj G).X)
    (hxy : x.left ≫ pullback.fst G.X.hom b = y.left ≫ pullback.fst G.X.hom b) :
    x = y := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact hxy
  · exact (Over.w x).trans (Over.w y).symm

/-- Inner conjugation is natural with the named rational-point map. -/
theorem innerIso_hom_comp_rational {K : Type u} [Field K]
    {H J : GroupScheme (Spec (CommRingCat.of K))}
    (j : H ⟶ J) (p : rationalPoints H) :
    (H.innerIso p).hom ≫ j = j ≫ (J.innerIso (rationalPoints.map j p)).hom := by
  rw [rationalPoints.map_apply]
  exact innerIso_hom_comp j p

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  (h : baseMap L M ≫ baseMap k L = baseMap k M)

omit [IsScalarTower k L M] in
/-- Projection of the transported pulled-back section to the original group. -/
theorem pullbackComparison_baseChangeBasePoint_fst
    (x : rationalPoints (baseChanged k L G)) :
    (rationalPoints.map
        (pullbackComparison (baseMap k L) (baseMap L M) (baseMap k M) h G).hom
        (baseChangeBasePoint (baseMap L M) (baseChanged k L G) x)).left ≫
        pullback.fst G.X.hom (baseMap k M) =
      baseMap L M ≫ (x.left ≫ pullback.fst G.X.hom (baseMap k L)) := by
  rw [rationalPoints.map_apply, Over.comp_left, Category.assoc,
    pullbackComparison_hom_fst, ← Category.assoc, baseChangeBasePoint_fst,
    Category.assoc]

/-- Transport through the actual field-tower comparison is relative extension
of the original rational point. -/
theorem pullbackComparison_baseChangeBasePoint
    (x : rationalPoints (baseChanged k L G)) :
    rationalPoints.map
        (pullbackComparison (baseMap k L) (baseMap L M) (baseMap k M) h G).hom
        (baseChangeBasePoint (baseMap L M) (baseChanged k L G) x) =
      relativeRationalExtend k L M G x := by
  apply baseChangedPoint_ext (baseMap k M) G
  exact (pullbackComparison_baseChangeBasePoint_fst k L M G h x).trans
    (relativeRationalExtend_fst k L M G x).symm

variable (σ : L ≃ₐ[k] L) (τ : M ≃ₐ[k] M)
  (hsq : galoisBaseMap k M τ ≫ baseMap L M = baseMap L M ≫ galoisBaseMap k L σ)
  (x : rationalPoints (baseChanged k L G))

/-- The exact generic compatibility square for inner-twisted coefficient maps,
with the upstairs conjugator supplied by actual rational extension. -/
theorem pullbackComparison_innerGaloisDescentIso :
    (GroupScheme.baseChange (galoisBaseMap k M τ)).map
        (pullbackComparison (baseMap k L) (baseMap L M) (baseMap k M) h G).hom ≫
          (innerGaloisDescentIso k G τ (relativeRationalExtend k L M G x)).hom =
      (squareComparison (baseMap L M) (galoisBaseMap k M τ) (galoisBaseMap k L σ)
        (baseMap L M) hsq (baseChanged k L G)).hom ≫
          (GroupScheme.baseChange (baseMap L M)).map (innerGaloisDescentIso k G σ x).hom ≫
            (pullbackComparison (baseMap k L) (baseMap L M) (baseMap k M) h G).hom := by
  simp only [innerGaloisDescentIso, Iso.trans_hom, Functor.map_comp, Category.assoc]
  rw [baseChange_innerIso_hom]
  rw [innerIso_hom_comp_rational
    (pullbackComparison (baseMap k L) (baseMap L M) (baseMap k M) h G).hom]
  rw [pullbackComparison_baseChangeBasePoint]
  rw [← Category.assoc]
  have ht := pullbackComparison_semilinear (baseMap k L) (baseMap L M) (baseMap k M) h
    (galoisBaseMap k L σ) (galoisBaseMap_over k L σ)
    (galoisBaseMap k M τ) (galoisBaseMap_over k M τ) hsq G
  rw [galoisDescentIso_hom_eq, galoisDescentIso_hom_eq]
  simpa only [Category.assoc] using congrArg
    (fun f => f ≫ ((baseChanged k M G).innerIso (relativeRationalExtend k L M G x)).hom) ht

section IntegralCoefficients

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
  [Algebra R L] [IsFractionRing R L] [Algebra A M] [IsFractionRing A M]
  [Algebra R A] [Algebra R M] [IsScalarTower R A M] [IsScalarTower R L M]
  [Flat (Spec.algebraMap R A)] [Surjective (Spec.algebraMap R A)]
  (N : IntegralModel R L (baseChanged k L G))
  (P : IntegralModel A M (baseChanged k M G))
  (e : (N.baseChange A M).Iso P
    (pullbackComparison (baseMap k L) (baseMap L M) (baseMap k M) h G))
  (a : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R))
  (a' : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A))
  (hvc : galoisBaseMap k L σ ≫ Spec.algebraMap R L = Spec.algebraMap R L ≫ a)
  (hvq : galoisBaseMap k M τ ≫ Spec.algebraMap A M = Spec.algebraMap A M ≫ a')
  (ha : a' ≫ Spec.algebraMap R A = Spec.algebraMap R A ≫ a)
  (φ : (P.twist a' (galoisBaseMap k M τ) hvq).Iso P
    (innerGaloisDescentIso k G τ (relativeRationalExtend k L M G x)))

/-- An actual upstairs inner-twisted map descends to the recovered coefficient
model when its conjugator is the extension of the specified downstairs point. -/
def innerSemilinearIsoFromCoefficients :
    (N.twist a (galoisBaseMap k L σ) hvc).Iso N (innerGaloisDescentIso k G σ x) :=
  semilinearIsoFromCoefficients N A M a (galoisBaseMap k L σ) hvc
    a' (galoisBaseMap k M τ) hvq ha hsq P
    (pullbackComparison (baseMap k L) (baseMap L M) (baseMap k M) h G) e
    (innerGaloisDescentIso k G σ x)
    (innerGaloisDescentIso k G τ (relativeRationalExtend k L M G x)) φ
    (pullbackComparison_innerGaloisDescentIso k L M G h σ τ hsq x)

/-- Pullback recovers the actual upstairs conjugate through the model comparison. -/
theorem baseChange_innerSemilinearIsoFromCoefficients :
    (GroupScheme.baseChange (Spec.algebraMap R A)).mapIso
        (innerSemilinearIsoFromCoefficients k L M G h σ τ hsq x
          R A N P e a a' hvc hvq ha φ).iso =
      (coefficientSemilinearIso N A M a (galoisBaseMap k L σ) hvc
        a' (galoisBaseMap k M τ) hvq ha hsq P
        (pullbackComparison (baseMap k L) (baseMap L M) (baseMap k M) h G) e
        (innerGaloisDescentIso k G τ (relativeRationalExtend k L M G x)) φ).iso :=
  baseChange_semilinearIsoFromCoefficients N A M a (galoisBaseMap k L σ) hvc
    a' (galoisBaseMap k M τ) hvq ha hsq P
    (pullbackComparison (baseMap k L) (baseMap L M) (baseMap k M) h G) e
    (innerGaloisDescentIso k G σ x)
    (innerGaloisDescentIso k G τ (relativeRationalExtend k L M G x)) φ
    (pullbackComparison_innerGaloisDescentIso k L M G h σ τ hsq x)

/-- The recovered map has exactly the prescribed inner-twisted generic fibre. -/
theorem innerSemilinearIsoFromCoefficients_generic :
    N.GenericSemilinearCompatible a (galoisBaseMap k L σ) hvc
      (innerSemilinearIsoFromCoefficients k L M G h σ τ hsq x
        R A N P e a a' hvc hvq ha φ).iso (innerGaloisDescentIso k G σ x) :=
  Hom.twist_generic_comm N _ _ _
    (innerSemilinearIsoFromCoefficients k L M G h σ τ hsq x
      R A N P e a a' hvc hvq ha φ).toHom

end IntegralCoefficients

end Langlands.GroupScheme.IntegralModel
