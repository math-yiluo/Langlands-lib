/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientTransitionUniversal
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientStrictRealization
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicMarkedOrigin
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientTransition
import WeilConjectures.CategoryTheory.DerivedCategory.AsFunctorLocalization
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryStrictSquare
import WeilConjectures.CategoryTheory.Comma.StructuredArrowUniversalIso
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients

/-! # The normalized tower in pro-etale quotient coordinates

Source: Stacks Project, Tags 06YY and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-quotient-coordinate-tower)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective


/-- The strict finite quotient tower in fixed-scalar chart coordinates. There are consecutive
semilinear arrows `δ n` between the ordinary fixed-scalar coordinates, whose localizations on
K-flat complexes are universal for derived restriction of scalars, and which are carried by the
explicit scalar realizations to the strict ordinary tensor tower restricted to every `W`,
compatibly with the ordinary scalar compositor and the inverse-image comparison.

Source: Stacks Project, Tag 09C6, the quotient arrows; Tag 06YY, tensor balancing;
Tags 03CY and 03DA.

Proof: combine the ordinary quotient arrows with their universality and realization. -/
theorem finitePerfectAdic_quotient_strict_tower
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (V : X.Etale) :
    ∃ δ : ∀ n : ℕ, finitePerfectAdicQuotientStrictCoordinates X d φ V (n + 1) ⟶
        finitePerfectAdicQuotientStrictCoordinates X d φ V n ⋙
          finitePerfectAdicStepRestrict X d V n,
      (∀ (n : ℕ) (P : CochainComplex (CompletedAdicModules X d) ℤ),
        CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing X d) P →
        Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk
          (finitePerfectAdicStrictLocalizedArrow X d φ V n (δ n) P)))) ∧
      ∀ (U : V.left.ProEt) (W : X.ProEt) (f : W ⟶ finitePerfectAdicChartObject V U),
        ∃ B : ∀ n : ℕ, finitePerfectAdicQuotientStrictCoordinates X d φ V n ⋙
            ProEtale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))
              U.hom ⋙ finitePerfectAdicScalarModules X d V U W f n ≅
            completedAdicOrdinaryTower X d ⋙
              (CategoryTheory.evaluation ℕᵒᵖ (CompletedAdicModules X d)).obj (op n) ⋙
              SheafOfModules.overFunctor (completedAdicRing X d) W,
          ∀ (n : ℕ) (N : CompletedAdicModules X d),
            (finitePerfectAdicScalarModules X d V U W f (n + 1)).map
                ((ProEtale.upperStar
                  (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1)))) U.hom).map
                    ((δ n).app N) ≫
                  (finitePerfectAdicPullbackRestrictIso U.hom (RingHom.ulift.{t + 1, t + 1}
                    (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).hom.app
                    ((finitePerfectAdicQuotientStrictCoordinates X d φ V n).obj N)) ≫
              (finitePerfectAdicScalarModulesCoherence X d V U W f n).hom.app
                ((ProEtale.upperStar
                  (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) U.hom).obj
                    ((finitePerfectAdicQuotientStrictCoordinates X d φ V n).obj N)) ≫
              (B n).hom.app N =
            (B (n + 1)).hom.app N ≫
              (SheafOfModules.overFunctor (completedAdicRing X d) W).map
                (((completedAdicOrdinaryTower X d).obj N).map (homOfLE (Nat.le_succ n)).op) := by
  choose δ hδ using finitePerfectAdic_quotient_transition_exists X d φ hcompat V
  exact ⟨δ, fun n P hP ↦ finitePerfectAdic_quotient_transition_universal X d φ hφ hcompat V n
    (δ n) (hδ n) P hP, finitePerfectAdic_quotient_strict_realization X d φ hφ hcompat V δ hδ⟩

/-- The actual quotient coordinates admit normalized consecutive arrows and a joint
scalar realization of the strict completed quotient tower. No etale origins are chosen.

Source: Stacks Project, Tag 09C6, the actual quotient arrows K_(n+1) to K_n;
Tag 06YY, computation and balancing of derived scalar extension; Tags 03CY and 05RU.
(blueprint: lem-weil-pbc-finite-perfect-adic-quotient-coordinate-tower).

Proof: take one flat-term K-flat representative P of M. At level n use its ordinary
sheafified tensor with the completed finite quotient ring. The section map
b tensor x maps to q(b) tensor x gives the consecutive semilinear arrow. The
scalar-extension adjunct is the balancing isomorphism, with inverse sending
b tensor x to b tensor (1 tensor x). Transport these quotient-linear objects and
arrows through phi and the fixed constant-scalar encoding, then restrict to V.
The coefficient encoding is an exact equivalence and inverse image commutes with
derived scalar extension, so the transported arrows are universal.

For each U,W,f, restrict this same representative, transport along the slice
equivalence, and use the counit of associated module sheafification. These maps
identify the scalar realizations with the restrictions of the same strict ordinary
tensor tower. On underlying abelian sheaves, the canonical scalar compositor is
fixed by the sheafification unit; both composites send b tensor x to q(b) tensor x.
Thus the consecutive square commutes before localization, not merely on objects.
The derived counits are invertible on P. Their naturality and the counit identifying
the specified strict representative of completedAdicReduction carry the entire
square to the displayed RestrictedTower, simultaneously at all levels. Independence
of P follows from the universal localization comparisons, which commute with these
actual chain maps. The argument includes the empty chart and the zero ring, and
uses no boundedness or finiteness condition on the cohomology of M. -/
theorem finitePerfectAdic_quotient_coordinate_tower
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale) :
    ∃ dJ : ∀ n : ℕ, finitePerfectAdicQuotientCoordinates X d φ M V (n + 1) ⟶
      (normalizationRestrict (ProEt.topology V.left)
        (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).obj
          (finitePerfectAdicQuotientCoordinates X d φ M V n),
      (∀ n : ℕ, Nonempty (StructuredArrow.IsUniversal
      (StructuredArrow.mk (dJ n)))) ∧
    ∃ actualJ : ∀ (U : V.left.ProEt) (W : X.ProEt)
        (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
      (finitePerfectAdicScalarRealization X d V U W f n).obj
        ((ProEtale.upperStar
          (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) U.hom).mapDerivedCategory.obj
            (finitePerfectAdicQuotientCoordinates X d φ M V n)) ≅
      (finitePerfectAdicRestrictedTower X d W
        ((completedAdicReduction X d).obj M)).obj (op n),
      ∀ (U : V.left.ProEt) (W : X.ProEt)
        (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
      (finitePerfectAdicScalarRealization X d V U W f (n + 1)).map
        ((ProEtale.upperStar
          (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1))))
            U.hom).mapDerivedCategory.map
            (dJ n) ≫
          (localIsomorphismProEtaleCoefficients U.hom
            (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).hom.app
              (finitePerfectAdicQuotientCoordinates X d φ M V n)) ≫
        (finitePerfectAdicScalarCoherence X d V U W f n).hom.app
          ((ProEtale.upperStar
            (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))
              U.hom).mapDerivedCategory.obj
                (finitePerfectAdicQuotientCoordinates X d φ M V n)) ≫
          (actualJ U W f n).hom =
        (actualJ U W f (n + 1)).hom ≫
          (finitePerfectAdicRestrictedTower X d W
            ((completedAdicReduction X d).obj M)).map
              (homOfLE (Nat.le_succ n)).op := by
  classical
  obtain ⟨δ, hδ, hB⟩ := finitePerfectAdic_quotient_strict_tower X d φ hφ hcompat V
  -- a K-flat representative of `M`
  obtain ⟨P, s, hP, -, hs, -⟩ := CochainComplex.exists_isKFlatResolutionGeneral
    (R := completedAdicCommRing X d) (DerivedCategory.Q.objPreimage M)
  have hPi : CochainComplex.IsKFlatIndependentCoefficients (R := completedAdicCommRing X d) P :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mpr hP
  have : IsIso (DerivedCategory.Q.map s) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hs
  let eP : (DerivedCategory.Q (C := CompletedAdicModules X d)).obj P ≅ M :=
    asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso M
  -- the quotient coordinates are computed by the strict coordinates of `P`
  have hJ (n : ℕ) : Nonempty (finitePerfectAdicQuotientCoordinates X d φ M V n ≅
      DerivedCategory.Q.obj (((finitePerfectAdicQuotientStrictCoordinates X d φ V
        n).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
    obtain ⟨e⟩ := completedAdicDerivedChange_kFlat_iso X (completedAdicCommProjection X d n) P hPi
    let SR := finiteCoefficientSliceRestriction X (A ⧸ d.ideal ^ (n + 1))
      (completedAdicFiniteCommRing X d n) (φ n) V
    exact ⟨SR.mapDerivedCategory.mapIso
      ((completedAdicQuotientReduction X d n).mapIso eP.symm ≪≫ e) ≪≫
      SR.mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
        (F := completedAdicChange X (completedAdicCommProjection X d n)) (G := SR)
        (Iso.refl _) (ComplexShape.up ℤ)).app P)⟩
  let εJ (n : ℕ) := (hJ n).some
  -- the reduction tower is computed by the strict tower of `P`
  have hT : Nonempty (DerivedCategory.Q.obj
      (DerivedCategory.Q.objPreimage ((completedAdicReduction X d).obj M)) ≅
      DerivedCategory.Q.obj (((completedAdicOrdinaryTower X d).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)) := by
    have := (completedAdicReductionData X d).complexCounit_isIso P hP
    exact ⟨DerivedCategory.Q.objObjPreimageIso _ ≪≫
      (completedAdicReduction X d).mapIso eP.symm ≪≫
      asIso ((completedAdicReductionData X d).complexCounit P)⟩
  let εT := hT.some
  refine ⟨fun n ↦ (εJ (n + 1)).hom ≫ Functor.strictSquareArrow
      (finitePerfectAdicQuotientStrictCoordinates X d φ V (n + 1))
      (finitePerfectAdicQuotientStrictCoordinates X d φ V n)
      (finitePerfectAdicStepRestrict X d V n) (δ n) P ≫
    (normalizationRestrict (ProEt.topology V.left) (RingHom.ulift.{t + 1, t + 1}
      (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).map (εJ n).inv, fun n ↦ ?_, ?_⟩
  · obtain ⟨h⟩ := hδ n P hP
    exact StructuredArrow.IsUniversal.nonempty_iso_comp (εJ (n + 1)) _ (εJ n).symm h
  choose B hBsq using hB
  have hτ (n : ℕ) : (completedAdicOrdinaryTower X d ⋙
      (CategoryTheory.evaluation ℕᵒᵖ (CompletedAdicModules X d)).obj (op n)).Additive :=
    inferInstance
  have hO₁ : ∀ W : X.ProEt, (SheafOfModules.overFunctor (completedAdicRing X d) W).Additive :=
    fun W ↦ (ringedOverFunctor_exactGeneral (completedAdicRing X d) W).1
  have hO₂ : ∀ W : X.ProEt,
      PreservesFiniteLimits (SheafOfModules.overFunctor (completedAdicRing X d) W) :=
    fun W ↦ (ringedOverFunctor_exactGeneral (completedAdicRing X d) W).2.1
  have hO₃ : ∀ W : X.ProEt,
      PreservesFiniteColimits (SheafOfModules.overFunctor (completedAdicRing X d) W) :=
    fun W ↦ (ringedOverFunctor_exactGeneral (completedAdicRing X d) W).2.2
  have hS₁ : ∀ (U : V.left.ProEt) (W : X.ProEt) (f : W ⟶ finitePerfectAdicChartObject V U)
      (n : ℕ), (finitePerfectAdicScalarModules X d V U W f n).Additive :=
    fun U W f n ↦ (finitePerfectAdicScalarModules_exact X d V U W f n).1
  have hS₂ : ∀ (U : V.left.ProEt) (W : X.ProEt) (f : W ⟶ finitePerfectAdicChartObject V U)
      (n : ℕ), PreservesFiniteLimits (finitePerfectAdicScalarModules X d V U W f n) :=
    fun U W f n ↦ (finitePerfectAdicScalarModules_exact X d V U W f n).2.1
  have hS₃ : ∀ (U : V.left.ProEt) (W : X.ProEt) (f : W ⟶ finitePerfectAdicChartObject V U)
      (n : ℕ), PreservesFiniteColimits (finitePerfectAdicScalarModules X d V U W f n) :=
    fun U W f n ↦ (finitePerfectAdicScalarModules_exact X d V U W f n).2.2
  let RT (W : X.ProEt) :=
    Functor.isoWhiskerRight (HomologicalComplex.asFunctorCompQIsoOfIso εT)
      (ringedDerivedRestrictionGeneral.{t + 1, t, t + 1, t + 1} (completedAdicRing X d) W)
  refine ⟨fun U W f n ↦ (finitePerfectAdicScalarRealization X d V U W f n).mapIso
      ((ProEtale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))
        U.hom).mapDerivedCategory.mapIso (εJ n)) ≪≫
      Functor.strictSquareRealization
        (τ := completedAdicOrdinaryTower X d ⋙
          (CategoryTheory.evaluation ℕᵒᵖ (CompletedAdicModules X d)).obj (op n))
        (o := SheafOfModules.overFunctor (completedAdicRing X d) W) (B U W f n) P ≪≫
        ((RT W).app (op n)).symm, ?_⟩
  intro U W f n
  let u₁ := ProEtale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1))))
    U.hom
  let u₀ := ProEtale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))
    U.hom
  let r' := sheafCompose (ProEt.topology U.left)
    (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1}
      (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1))))
  have hsq := Functor.strictSquare_localized
    (τ₁ := completedAdicOrdinaryTower X d ⋙
      (CategoryTheory.evaluation ℕᵒᵖ (CompletedAdicModules X d)).obj (op (n + 1)))
    (τ₀ := completedAdicOrdinaryTower X d ⋙
      (CategoryTheory.evaluation ℕᵒᵖ (CompletedAdicModules X d)).obj (op n))
    (r := finitePerfectAdicStepRestrict X d V n) (u₁ := u₁) (u₀ := u₀) (r' := r')
    (o := SheafOfModules.overFunctor (completedAdicRing X d) W)
    (δ n) (finitePerfectAdicPullbackRestrictIso U.hom
      (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1))))
    (finitePerfectAdicScalarModulesCoherence X d V U W f n) (B U W f (n + 1)) (B U W f n)
    (Functor.whiskerLeft (completedAdicOrdinaryTower X d)
      ((CategoryTheory.evaluation ℕᵒᵖ (CompletedAdicModules X d)).map
        (homOfLE (Nat.le_succ n)).op)) (hBsq U W f n)
    (localIsomorphismProEtaleCoefficients U.hom
      (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))) rfl
    (finitePerfectAdicScalarCoherence X d V U W f n) rfl P
  exact Functor.strictSquare_transport
    (localIsomorphismProEtaleCoefficients U.hom
      (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1))))
    (finitePerfectAdicScalarCoherence X d V U W f n) (εJ (n + 1)) (εJ n) _ _ _ _
    ((RT W).app (op (n + 1))).symm ((RT W).app (op n)).symm _ hsq
    ((RT W).inv.naturality (homOfLE (Nat.le_succ n)).op)



end AlgebraicGeometry.Scheme
