/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenRingedModuleGluing
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.ClopenData.ProEtaleClopenTotalTensorKFlatDetectionData
import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenFlatDetection
import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenKFlatDetection
import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenStructuralData

/-! # Tensor restriction and flatness on finite clopen pro-etale partitions

All abbreviations below expose the recorded sectionwise restriction and tensor constructions.
The zero insertion in the last clause is characterized by its restrictions: the identity at
its own component and zero elsewhere. This covers every zero insertion supplied by gluing.

## References

* Stacks Project, Tag 0GMW and its bilinear universal property
* Stacks 03D7
* Stacks 04TR
* Stacks 06YN
* Stacks 0FPQ
* Stacks Project, Tag 0GMW and the following bilinear universal property
* Tag 03ER (3)
-/

@[expose] public noncomputable section

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory

namespace AlgebraicGeometry.Scheme.ProEt

/-- The recorded module category, in the fixed universe containing the small site. -/
abbrev clopenTensorModules {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :=
  ClopenData.clopenTensorModules R

/-- Commutative-ring restriction along the same composition functor as ring restriction. -/
abbrev clopenTensorRings {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j] :=
  ClopenData.clopenTensorRings j

/-- The dependency's actual restriction, with its sectionwise module actions unchanged. -/
abbrev clopenTensorRestriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    clopenTensorModules.{t, u} R ⥤
      clopenTensorModules.{t, u} ((clopenTensorRings.{t, u} j).obj R) :=
  ClopenData.clopenTensorRestriction j R

/-- The recorded additivity instance, exposed for degreewise restriction. -/
instance clopenTensorRestrictionAdditive {X Y : Scheme.{t}} (j : Y ⟶ X)
    [IsOpenImmersion j] (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    (clopenTensorRestriction.{t, u} j R).Additive :=
  ClopenData.clopenTensorRestrictionAdditive j R

/-- Degreewise restriction of unbounded cochain complexes. -/
abbrev clopenTensorComplexRestriction {X Y : Scheme.{t}} (j : Y ⟶ X)
    [IsOpenImmersion j] (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :=
  ClopenData.clopenTensorComplexRestriction j R

/-- The tensor comparison `j^*(F ⊗ H) ≅ j^*F ⊗ j^*H` of a braided clopen restriction functor,
given by the inverse tensorator. -/
def clopenTensorComparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (clopenTensorRestriction.{t, u} j R).Braided) (F H : clopenTensorModules.{t, u} R) :
    (clopenTensorRestriction.{t, u} j R).obj (F ⊗ H) ≅
      (clopenTensorRestriction.{t, u} j R).obj F ⊗ (clopenTensorRestriction.{t, u} j R).obj H :=
  ClopenData.clopenTensorComparison j R h F H

/-- Restriction of the module tensor unit is the component ring module. -/
def clopenTensorUnitComparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (clopenTensorRestriction.{t, u} j R).Braided) :
    (clopenTensorRestriction.{t, u} j R).obj (𝟙_ (clopenTensorModules.{t, u} R)) ≅
      𝟙_ (clopenTensorModules.{t, u} ((clopenTensorRings.{t, u} j).obj R)) :=
  ClopenData.clopenTensorUnitComparison j R h

/-- A local pure tensor, using the existing sheafification unit and tensor comparison. -/
def clopenTensorPure {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (F H : clopenTensorModules.{t, u} R) (U : X.ProEtᵒᵖ)
    (x : F.val.obj U) (y : H.val.obj U) : (F ⊗ H).val.obj U :=
  ClopenData.clopenTensorPure R F H U x y

/-- The actual total-tensor summand inclusion, with its total bifunctor explicit. -/
def clopenTotalTensorSummand {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (P Q : CochainComplex (clopenTensorModules.{t, u} R) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    P.X p ⊗ Q.X q ⟶
      ((coefficientTotalTensor.{u, t + 1, t} (topology X) R).obj (P, Q)).X n :=
  ClopenData.clopenTotalTensorSummand R P Q p q n hpq

/-- Pure-tensor normalized ordinary and total comparisons, signed differential and symmetry,
coproduct preservation, the zero-insertion adjunction, and flat/K-flat detection. -/
theorem clopen_total_tensor_kflat_detection
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    (∀ F : clopenTensorModules.{t, u} R,
      SheafOfModules.IsFlatOnSite (J := topology X) (R := R) F ↔
        ∀ i, SheafOfModules.IsFlatOnSite (J := topology (Y i))
          (R := (clopenTensorRings.{t, u} (j i)).obj R)
          ((clopenTensorRestriction.{t, u} (j i) R).obj F)) ∧
    (∀ P : CochainComplex (clopenTensorModules.{t, u} R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) P ↔
        ∀ i, CochainComplex.IsKFlatIndependentCoefficients (J := topology (Y i))
          (R := (clopenTensorRings.{t, u} (j i)).obj R)
          ((clopenTensorComplexRestriction.{t, u} (j i) R).obj P)) ∧
    (∀ i, ∃ (h : (clopenTensorRestriction.{t, u} (j i) R).Braided)
      (b : coefficientTotalTensor.{u, t + 1, t} (topology X) R ⋙
          clopenTensorComplexRestriction.{t, u} (j i) R ≅
        ((clopenTensorComplexRestriction.{t, u} (j i) R).prod
          (clopenTensorComplexRestriction.{t, u} (j i) R)) ⋙
            coefficientTotalTensor.{u, t + 1, t} (topology (Y i))
              ((clopenTensorRings.{t, u} (j i)).obj R)),
      (∀ (F H : clopenTensorModules.{t, u} R) (U : (Y i).ProEt)
        (x : F.val.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale (j i))).obj U)))
        (y : H.val.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale (j i))).obj U))),
        (clopenTensorComparison.{t, u} (j i) R h F H).hom.val.app (op U)
          (clopenTensorPure.{t, u} R F H _ x y) =
        clopenTensorPure.{t, u} ((clopenTensorRings.{t, u} (j i)).obj R)
          ((clopenTensorRestriction.{t, u} (j i) R).obj F)
          ((clopenTensorRestriction.{t, u} (j i) R).obj H) (op U) x y) ∧
      (∀ (P Q : CochainComplex (clopenTensorModules.{t, u} R) ℤ)
        (p q n : ℤ) (hpq : p + q = n),
        (clopenTensorRestriction.{t, u} (j i) R).map
            (clopenTotalTensorSummand.{t, u} R P Q p q n hpq) ≫ (b.hom.app (P, Q)).f n =
          (clopenTensorComparison.{t, u} (j i) R h (P.X p) (Q.X q)).hom ≫
            clopenTotalTensorSummand.{t, u} ((clopenTensorRings.{t, u} (j i)).obj R)
              ((clopenTensorComplexRestriction.{t, u} (j i) R).obj P)
              ((clopenTensorComplexRestriction.{t, u} (j i) R).obj Q) p q n hpq) ∧
      (∀ (P Q : CochainComplex (clopenTensorModules.{t, u} R) ℤ)
        (p q n : ℤ) (hpq : p + q = n)
        (hp : (p + 1) + q = n + 1) (hq : p + (q + 1) = n + 1),
        (clopenTensorRestriction.{t, u} (j i) R).map
            (clopenTotalTensorSummand.{t, u} R P Q p q n hpq ≫
              ((coefficientTotalTensor.{u, t + 1, t} (topology X) R).obj
                (P, Q)).d n (n + 1)) ≫
              (b.hom.app (P, Q)).f (n + 1) =
          (clopenTensorComparison.{t, u} (j i) R h (P.X p) (Q.X q)).hom ≫
            (((clopenTensorRestriction.{t, u} (j i) R).map (P.d p (p + 1)) ▷
                (clopenTensorRestriction.{t, u} (j i) R).obj (Q.X q)) ≫
              clopenTotalTensorSummand.{t, u} ((clopenTensorRings.{t, u} (j i)).obj R)
                ((clopenTensorComplexRestriction.{t, u} (j i) R).obj P)
                ((clopenTensorComplexRestriction.{t, u} (j i) R).obj Q) (p + 1) q (n + 1) hp +
            p.negOnePow •
              (((clopenTensorRestriction.{t, u} (j i) R).obj (P.X p) ◁
                (clopenTensorRestriction.{t, u} (j i) R).map (Q.d q (q + 1))) ≫
              clopenTotalTensorSummand.{t, u} ((clopenTensorRings.{t, u} (j i)).obj R)
                ((clopenTensorComplexRestriction.{t, u} (j i) R).obj P)
                ((clopenTensorComplexRestriction.{t, u} (j i) R).obj Q) p (q + 1) (n + 1) hq))) ∧
      (∀ (P Q : CochainComplex (clopenTensorModules.{t, u} R) ℤ)
        (p q n : ℤ) (hqp : q + p = n),
        (clopenTensorRestriction.{t, u} (j i) R).map
            ((p * q).negOnePow • ((β_ (P.X p) (Q.X q)).hom ≫
              clopenTotalTensorSummand.{t, u} R Q P q p n hqp)) ≫
            (b.hom.app (Q, P)).f n =
          (p * q).negOnePow •
            ((clopenTensorComparison.{t, u} (j i) R h (P.X p) (Q.X q)).hom ≫
              (β_ ((clopenTensorRestriction.{t, u} (j i) R).obj (P.X p))
                ((clopenTensorRestriction.{t, u} (j i) R).obj (Q.X q))).hom ≫
              clopenTotalTensorSummand.{t, u} ((clopenTensorRings.{t, u} (j i)).obj R)
                ((clopenTensorComplexRestriction.{t, u} (j i) R).obj Q)
                ((clopenTensorComplexRestriction.{t, u} (j i) R).obj P) q p n hqp))) ∧
    (∀ i (K : Type (max u (t + 1))),
      PreservesColimitsOfShape (Discrete K) (clopenTensorRestriction.{t, u} (j i) R)) ∧
    (∀ i (e : clopenTensorModules.{t, u} ((clopenTensorRings.{t, u} (j i)).obj R) ⥤
        clopenTensorModules.{t, u} R),
      Nonempty (e ⋙ clopenTensorRestriction.{t, u} (j i) R ≅ 𝟭 _) →
      (∀ k, k ≠ i → ∀ N, IsZero ((e ⋙ clopenTensorRestriction.{t, u} (j k) R).obj N)) →
      Nonempty (clopenTensorRestriction.{t, u} (j i) R ⊣ e)) := by
  obtain ⟨hcomparison, hcoproduct, hadjunction⟩ :=
    clopen_structural_data X I Y j hdisjoint hcover R
  exact ⟨clopen_flat_detection X I Y j hdisjoint hcover R,
    clopen_kflat_detection X I Y j hdisjoint hcover R,
    hcomparison, hcoproduct, hadjunction⟩

end AlgebraicGeometry.Scheme.ProEt
