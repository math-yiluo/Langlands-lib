/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicRestrictedTower
public import WeilConjectures.AlgebraicGeometry.Source.SourceIsomorphismNormalizedPresheafEvaluation
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleUniversalNormalization
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import all WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering

/-! # Descent of the finite levels before constructing Isom sheaves

## References

* Stacks Tags 099Z, 09B1, 099Y, 09BV and 06YY
* Stacks Tags 03CY and 0H7J
* Stacks Tags 031C, 03CY and 05RU
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard

/-- Completion quotient coefficients, indexed by positive exponents. -/
abbrev lisseTowerEtaleRing {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :=
  AdicCompletion d.ideal A ⧸
    (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)

/-- The consecutive quotient homomorphism. -/
def lisseTowerEtaleQuotient {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    lisseTowerEtaleRing d (n + 1) →+* lisseTowerEtaleRing d n :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right
    (I := d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) (Nat.le_succ (n + 1)))

/-- Forget quotient coefficients to the completion. -/
abbrev lisseTowerAlgebraForget {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :=
  (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
    (Ideal.Quotient.mk ((d.ideal.map
      (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)))).mapDerivedCategory

/-- The algebraic arrow after forgetting scalars, with the specified compositors. -/
def lisseTowerAlgebraArrow {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ)
    {E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1)))}
    {E' : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))}
    (k : E ⟶ (normalizationModuleRestrict (lisseTowerEtaleQuotient d n)).obj E') :
    (lisseTowerAlgebraForget d (n + 1)).obj E ⟶
      (lisseTowerAlgebraForget d n).obj E' :=
  (lisseTowerAlgebraForget d (n + 1)).map k ≫
    (Functor.mapDerivedCategoryCompIso
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n))
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
        (Ideal.Quotient.mk ((d.ideal.map
          (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 2))))).hom.app E' ≫
    (Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp'.{u + 1}
      (Ideal.Quotient.mk ((d.ideal.map
        (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 2)))
      (lisseTowerEtaleQuotient d n)
      (Ideal.Quotient.mk ((d.ideal.map
        (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)))
      (Ideal.Quotient.factor_comp_mk _).symm)).inv.app E'

attribute [local irreducible] pbcDerivedRestrict
  constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow etaleIsomorphismNormalizationArrow
  lisseTowerAlgebraArrow

/-- Raw etale descent data. The source arrows are not supplied: the model comparison
respects *every* algebraic arrow. There are no Isom-sheaf reduction maps or evaluations. -/
structure LisseTowerEtaleDescent
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower X d) (U : Y.ProEt)
    (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))) where
  D : ∀ n : ℕ, DerivedCategory
    (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
  boundedD : ∀ n : ℕ, ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q → IsZero
    ((DerivedCategory.homologyFunctor _ q).obj (D n))
  lisseD : ∀ (n : ℕ) (q : ℤ), IsFiniteLocallyConstantSheaf
    ((DerivedCategory.homologyFunctor _ q).obj (D n))
  stalk : ∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ U.left), Nonempty ((pointSmallEtale x).sheafFiber.obj
      (derivedLocalIsomorphismSheaf
        ((normalizationConstant U.left.smallEtaleTopology).obj (K n)) (D n)))
  delta : ∀ n : ℕ, D (n + 1) ⟶
    (normalizationRestrict U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)).obj (D n)
  local_delta_universal : ∀ (n : ℕ) (V : U.left.Etale),
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk
      (etaleIsomorphismNormalizationArrow U.left (lisseTowerEtaleQuotient d n) (delta n) V)))
  local_constant_universal : ∀ (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))))
    (E' : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (k : E ⟶ (normalizationModuleRestrict (lisseTowerEtaleQuotient d n)).obj E'),
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk k)) →
    ∀ V : U.left.Etale, Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk
      (etaleIsomorphismNormalizationArrow U.left (lisseTowerEtaleQuotient d n)
        (normalizationConstantArrow U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)
          k) V)))
  restriction_square : ∀ (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))))
    (E' : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (k : E ⟶ (normalizationModuleRestrict (lisseTowerEtaleQuotient d n)).obj E')
    (V Z : U.left.Etale) (f : V ⟶ Z)
    (e : (localIsomorphismRestriction U.left (lisseTowerEtaleRing d (n + 1)) Z).obj
        ((normalizationConstant U.left.smallEtaleTopology).obj E) ≅
      (localIsomorphismRestriction U.left (lisseTowerEtaleRing d (n + 1)) Z).obj (D (n + 1)))
    (e' : (localIsomorphismRestriction U.left (lisseTowerEtaleRing d n) Z).obj
        ((normalizationConstant U.left.smallEtaleTopology).obj E') ≅
      (localIsomorphismRestriction U.left (lisseTowerEtaleRing d n) Z).obj (D n)),
    e.hom ≫ etaleIsomorphismNormalizationArrow U.left (lisseTowerEtaleQuotient d n)
        (delta n) Z =
      etaleIsomorphismNormalizationArrow U.left (lisseTowerEtaleQuotient d n)
        (normalizationConstantArrow U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)
          k) Z ≫ (normalizationRestrict Z.left.smallEtaleTopology
            (lisseTowerEtaleQuotient d n)).map e'.hom →
    (localIsomorphismMap ((normalizationConstant U.left.smallEtaleTopology).obj E)
      (D (n + 1)) f e).hom ≫ etaleIsomorphismNormalizationArrow U.left
        (lisseTowerEtaleQuotient d n) (delta n) V =
      etaleIsomorphismNormalizationArrow U.left (lisseTowerEtaleQuotient d n)
        (normalizationConstantArrow U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)
          k) V ≫ (normalizationRestrict V.left.smallEtaleTopology
            (lisseTowerEtaleQuotient d n)).map
              (localIsomorphismMap ((normalizationConstant U.left.smallEtaleTopology).obj E')
                (D n) f e').hom
  realization : ∀ (V : U.left.ProEt) (W : Y.ProEt),
    (W ⟶ ProEt.mk (V.hom ≫ U.hom)) → ∀ n : ℕ,
    DerivedCategory (Sheaf (ProEt.topology V.left)
      (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))) ⥤
      DerivedCategory (pbcModules W.left
        ((adicTowerInverseImage (W.hom ≫ g)).obj ((pbcAdicRings X d).obj (op n))))
  model : ∀ (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))),
    (realization V W f n).obj ((localProEtaleComparison V.hom
      (lisseTowerEtaleRing d n)).obj
        ((normalizationConstant U.left.smallEtaleTopology).obj E)) ≅
      (constantAdicQuotientRealization (W.hom ≫ g) d n).obj E
  actual : ∀ (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) (n : ℕ),
    (realization V W f n).obj
      ((localProEtaleComparison V.hom (lisseTowerEtaleRing d n)).obj (D n)) ≅
      (adicTowerPullback (W.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj (M.level n)
  scalar : ∀ (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) (n : ℕ),
    normalizationRestrict (ProEt.topology V.left) (lisseTowerEtaleQuotient d n) ⋙
        realization V W f (n + 1) ⋙
          pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d (n + 1)) ≅
      realization V W f n ⋙ pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d n)
  actual_normalized : ∀ (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) (n : ℕ),
    let H (k : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d k)
    (H (n + 1)).map ((realization V W f (n + 1)).map
      (localProEtaleNormalization V.hom (lisseTowerEtaleQuotient d n) (delta n))) ≫
      (scalar V W f n).hom.app
        ((localProEtaleComparison V.hom (lisseTowerEtaleRing d n)).obj (D n)) ≫
      (H n).map (actual V W f n).hom =
    (H (n + 1)).map (actual V W f (n + 1)).hom ≫
      constantAdicRestrictedStep (W.hom ≫ g) d M n
  model_normalized : ∀ (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))))
    (E' : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (k : E ⟶ (normalizationModuleRestrict (lisseTowerEtaleQuotient d n)).obj E'),
    let H (j : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d j)
    let c (j : ℕ) (N : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d j))) :=
      (H j).mapIso (model V W f j N) ≪≫
        ((constantAdicQuotientRightIso (W.hom ≫ g) d j).app N).symm
    (H (n + 1)).map ((realization V W f (n + 1)).map
      (localProEtaleNormalization V.hom (lisseTowerEtaleQuotient d n)
        (normalizationConstantArrow U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)
          k))) ≫
      (scalar V W f n).hom.app ((localProEtaleComparison V.hom
        (lisseTowerEtaleRing d n)).obj
          ((normalizationConstant U.left.smallEtaleTopology).obj E')) ≫ (c n E').hom =
      (c (n + 1) E).hom ≫
        (constantAdicFiniteRealization (W.hom ≫ g) d).map (lisseTowerAlgebraArrow d n k)

/-- The normalization and realization part of descent, relative to already descended
etale levels. There are no local marking, finiteness or stalk fields in this record. -/
structure LisseTowerEtaleNormalization
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower X d) (U : Y.ProEt)
    (D : ∀ n : ℕ, DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))) where
  delta : ∀ n : ℕ, D (n + 1) ⟶
    (normalizationRestrict U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)).obj (D n)
  local_delta : ∀ n : ℕ, EtaleUniversalNormalization U.left
    (lisseTowerEtaleQuotient d n) (delta n)
  local_constant_universal : ∀ (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))))
    (E' : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (k : E ⟶ (normalizationModuleRestrict (lisseTowerEtaleQuotient d n)).obj E'),
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk k)) →
    ∀ V : U.left.Etale, Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk
      (etaleIsomorphismNormalizationArrow U.left (lisseTowerEtaleQuotient d n)
        (normalizationConstantArrow U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)
          k) V)))
  constant_coherence : ∀ (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))))
    (E' : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (k : E ⟶ (normalizationModuleRestrict (lisseTowerEtaleQuotient d n)).obj E')
    {V Z : U.left.Etale} (f : V ⟶ Z),
    (localIsomorphismRestrictionComp U.left (lisseTowerEtaleRing d (n + 1)) f).inv.app
        ((normalizationConstant U.left.smallEtaleTopology).obj E) ≫
      etaleIsomorphismNormalizationArrow U.left (lisseTowerEtaleQuotient d n)
        (normalizationConstantArrow U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)
          k) V =
    (Etale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1)))
        f.left).mapDerivedCategory.map
      (etaleIsomorphismNormalizationArrow U.left (lisseTowerEtaleQuotient d n)
        (normalizationConstantArrow U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)
          k) Z) ≫
      (etaleNormalizationCoefficients f.left (lisseTowerEtaleQuotient d n)).hom.app
        ((localIsomorphismRestriction U.left (lisseTowerEtaleRing d n) Z).obj
          ((normalizationConstant U.left.smallEtaleTopology).obj E')) ≫
      (normalizationRestrict V.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)).map
        ((localIsomorphismRestrictionComp U.left (lisseTowerEtaleRing d n) f).inv.app
          ((normalizationConstant U.left.smallEtaleTopology).obj E'))
  realization : ∀ (V : U.left.ProEt) (W : Y.ProEt),
    (W ⟶ ProEt.mk (V.hom ≫ U.hom)) → ∀ n : ℕ,
    DerivedCategory (Sheaf (ProEt.topology V.left)
      (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))) ⥤
      DerivedCategory (pbcModules W.left
        ((adicTowerInverseImage (W.hom ≫ g)).obj ((pbcAdicRings X d).obj (op n))))
  model : ∀ (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))),
    (realization V W f n).obj ((localProEtaleComparison V.hom
      (lisseTowerEtaleRing d n)).obj
        ((normalizationConstant U.left.smallEtaleTopology).obj E)) ≅
      (constantAdicQuotientRealization (W.hom ≫ g) d n).obj E
  actual : ∀ (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) (n : ℕ),
    (realization V W f n).obj
      ((localProEtaleComparison V.hom (lisseTowerEtaleRing d n)).obj (D n)) ≅
      (adicTowerPullback (W.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj (M.level n)
  scalar : ∀ (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) (n : ℕ),
    normalizationRestrict (ProEt.topology V.left) (lisseTowerEtaleQuotient d n) ⋙
        realization V W f (n + 1) ⋙
          pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d (n + 1)) ≅
      realization V W f n ⋙ pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d n)
  actual_normalized : ∀ (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) (n : ℕ),
    let H (k : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d k)
    (H (n + 1)).map ((realization V W f (n + 1)).map
      (localProEtaleNormalization V.hom (lisseTowerEtaleQuotient d n) (delta n))) ≫
      (scalar V W f n).hom.app
        ((localProEtaleComparison V.hom (lisseTowerEtaleRing d n)).obj (D n)) ≫
      (H n).map (actual V W f n).hom =
    (H (n + 1)).map (actual V W f (n + 1)).hom ≫
      constantAdicRestrictedStep (W.hom ≫ g) d M n
  model_normalized : ∀ (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))))
    (E' : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (k : E ⟶ (normalizationModuleRestrict (lisseTowerEtaleQuotient d n)).obj E'),
    let H (j : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d j)
    let c (j : ℕ) (N : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d j))) :=
      (H j).mapIso (model V W f j N) ≪≫
        ((constantAdicQuotientRightIso (W.hom ≫ g) d j).app N).symm
    (H (n + 1)).map ((realization V W f (n + 1)).map
      (localProEtaleNormalization V.hom (lisseTowerEtaleQuotient d n)
        (normalizationConstantArrow U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)
          k))) ≫
      (scalar V W f n).hom.app ((localProEtaleComparison V.hom
        (lisseTowerEtaleRing d n)).obj
          ((normalizationConstant U.left.smallEtaleTopology).obj E')) ≫ (c n E').hom =
      (c (n + 1) E).hom ≫
        (constantAdicFiniteRealization (W.hom ≫ g) d).map (lisseTowerAlgebraArrow d n k)

/-- Inverse image preserves constant coefficient rings by the constant-section map. -/
theorem lisseTowerFiniteConstantInverseImage_isIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] :
    IsIso (proEtaleConstantInverseImageMap g CommRingCat.{u + 1} (CommRingCat.of B)) := by
  let G := proEtaleBaseChange g
  let hX : IsTerminal (⊤_ X.ProEt) := terminalIsTerminal
  let hY := hX.isTerminalObj G _
  let aX := constantSheafAdj (ProEt.topology X) CommRingCat.{u + 1} hX
  let adj := proEtaleSheafAdjunction g CommRingCat.{u + 1}
  let a := (aX.comp adj).ofNatIsoRight (Iso.refl _)
  let b := constantSheafAdj (ProEt.topology Y) CommRingCat.{u + 1} hY
  let e := a.leftAdjointUniq b
  have he : proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
      (CommRingCat.of B) = e.hom.app (CommRingCat.of B) := by
    apply (a.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    simp only [a, Adjunction.homEquiv_ofNatIsoRight_apply, Iso.refl_hom,
      NatTrans.id_app, Category.comp_id, Adjunction.comp_homEquiv]
    dsimp [proEtaleConstantInverseImageMap]
    rw [← Adjunction.homEquiv_counit]
    dsimp only [adj]
    rw [Equiv.apply_symm_apply]
    dsimp only [proEtaleConstantDirectImageMap, aX, constantSheafAdj]
    rw [Adjunction.comp_homEquiv]
    change (constantPresheafAdj CommRingCat.{u + 1} hX).homEquiv _ _
      (((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
        _ _)
        (((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
          _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    rfl
  rw [he]
  infer_instance

/-- The canonical identification of the actual pulled finite ring with constant scalars. -/
def lisseTowerFiniteCoefficientIso {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (adicTowerInverseImage f).obj ((pbcAdicRings X d).obj (op n)) ≅
      adicLisseConstantRing Z (A ⧸ d.ideal ^ (n + 1)) := by
  have := lisseTowerFiniteConstantInverseImage_isIso f (A ⧸ d.ideal ^ (n + 1))
  exact (adicTowerInverseImage f).mapIso (pbcLevelConstantComparison X d n).symm ≪≫
    asIso (proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
      (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))))

/-- Constant scalar sections of the actual inverse-image finite ring. -/
def lisseTowerFiniteScalarMap {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (Functor.const Z.ProEtᵒᵖ).obj (RingCat.of (A ⧸ d.ideal ^ (n + 1))) ⟶
      ((adicLisseForget Z).obj
        ((adicTowerInverseImage f).obj ((pbcAdicRings X d).obj (op n)))).obj :=
  adicLisseConstantUnit Z (A ⧸ d.ideal ^ (n + 1)) ≫
    ((adicLisseForget Z).map (lisseTowerFiniteCoefficientIso f d n).inv).hom

instance lisseTowerFiniteScalarMap_injective {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    Presheaf.IsLocallyInjective (ProEt.topology Z) (lisseTowerFiniteScalarMap f d n) := by
  unfold lisseTowerFiniteScalarMap
  infer_instance

instance lisseTowerFiniteScalarMap_surjective {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    Presheaf.IsLocallySurjective (ProEt.topology Z) (lisseTowerFiniteScalarMap f d n) := by
  unfold lisseTowerFiniteScalarMap
  infer_instance

/-- Realize fixed finite scalars by the specified associated-module-sheaf construction. -/
def lisseTowerFiniteSheafRealization {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1))) ⥤
      pbcModules Z ((adicTowerInverseImage f).obj ((pbcAdicRings X d).obj (op n))) :=
  sheafToPresheaf _ _ ⋙
    ProEtale.finiteCoefficientModulePresheaf Z.ProEt (A ⧸ d.ideal ^ (n + 1)) ⋙
    PresheafOfModules.sheafification (lisseTowerFiniteScalarMap f d n)

instance lisseTowerFiniteSheafRealization_isEquivalence {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (lisseTowerFiniteSheafRealization f d n).IsEquivalence := by
  exact ProEtale.coefficientRealization_isEquivalence (ProEt.topology Z)
    (A ⧸ d.ideal ^ (n + 1)) _ (lisseTowerFiniteScalarMap f d n)

instance lisseTowerFiniteSheafRealization_additive {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (lisseTowerFiniteSheafRealization f d n).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The fixed realization used in the single-level descent statement. It is constructed
from restriction of algebraic scalars and module sheafification, without an existence
choice of functors or module objects. -/
def lisseTowerFixedRealization {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    DerivedCategory (Sheaf (ProEt.topology Z)
      (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))) ⥤
      DerivedCategory (pbcModules Z
        ((adicTowerInverseImage f).obj ((pbcAdicRings X d).obj (op n)))) :=
  normalizationRestrict (ProEt.topology Z) (constantAdicQuotientMap d.ideal n) ⋙
    (lisseTowerFiniteSheafRealization f d n).mapDerivedCategory

/-- Completion quotients retain the finiteness of the original positive quotients. -/
instance lisseTowerEtaleRing_finite {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) : Finite (lisseTowerEtaleRing d n) := by
  have := d.quotientFinite n
  exact Finite.of_surjective (constantAdicQuotientMap d.ideal n)
    (quotient_map_bijective d.ideal d.finitelyGenerated n).surjective

/-- The explicitly constructed fixed realization is an equivalence at the base scheme. -/
instance lisseTowerFixedRealization_isEquivalence {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (lisseTowerFixedRealization f d n).IsEquivalence := by
  let e := RingEquiv.ofBijective (constantAdicQuotientMap d.ideal n)
    (quotient_map_bijective d.ideal d.finitelyGenerated n)
  have : (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (constantAdicQuotientMap d.ideal n)).IsEquivalence :=
    inferInstanceAs (ModuleCat.restrictScalars e.toRingHom).IsEquivalence
  have : (sheafCompose (ProEt.topology Z)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
        (constantAdicQuotientMap d.ideal n))).IsEquivalence :=
    isEquivalence_sheafCompose_of_isEquivalence _ _
  unfold lisseTowerFixedRealization normalizationRestrict
  infer_instance

end AlgebraicGeometry.Scheme
