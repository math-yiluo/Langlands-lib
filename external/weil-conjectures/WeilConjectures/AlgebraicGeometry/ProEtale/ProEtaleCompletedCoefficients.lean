/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompletedCoefficientData
public import Mathlib.Topology.Category.Profinite.AsLimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import Mathlib.NumberTheory.Padics.RingHoms
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleNormalizedIntegralTower
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompletedRationalization
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import WeilConjectures.CategoryTheory.Mon.FilteredRingObjectCoconeColimit
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.EssentiallySmall
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import Mathlib.Topology.Algebra.Ring.Compact
import WeilConjectures.NumberTheory.Padics.IntegersAlgebra

/-!
# Comparison of pulled-back condensed coefficients with completed coefficients

The integral comparison is stated as a limit universal property, with its reductions
normalized on constant sections. Rationalization is stated as the sequential module
colimit together with the ring-localization universal property. These formulations
specify the canonical comparisons without choosing new models for the coefficients.
Rationalization naturality retains the underlying bundled ring comparison; its additive
component is identity followed by the inverse-image compositor.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

private noncomputable def sfb_padic_quotient_equiv (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    ℤ_[ℓ] ⧸ Ideal.span ({(ℓ : ℤ_[ℓ])} : Set ℤ_[ℓ]) ^ n ≃+* ZMod (ℓ ^ n) :=
  (Ideal.quotEquivOfEq (by
    rw [Ideal.span_singleton_pow, PadicInt.ker_toZModPow])).trans
    (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (PadicInt.toZModPow n)))

private theorem sfb_padic_quotient_equiv_mk (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (x : ℤ_[ℓ]) :
    sfb_padic_quotient_equiv ℓ n (Ideal.Quotient.mk _ x) = PadicInt.toZModPow n x := by
  simp only [sfb_padic_quotient_equiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

private theorem sfb_padic_quotient_tower (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ e : sfbCoefficientQuotientTower ℤ_[ℓ]
        (Ideal.span ({(ℓ : ℤ_[ℓ])} : Set ℤ_[ℓ])) ≅ sfbZModCoefficientTower.{u} ℓ,
      ∀ (n : ℕ) (x : ℤ_[ℓ]),
        (e.hom.app (op n)).hom (ULift.up (Ideal.Quotient.mk
          (Ideal.span ({(ℓ : ℤ_[ℓ])} : Set ℤ_[ℓ]) ^ n) x)) =
            ULift.up (PadicInt.toZModPow n x) := by
  let e (n : ℕ) := ((ULift.ringEquiv.trans (sfb_padic_quotient_equiv ℓ n)).trans
    ULift.ringEquiv.symm).toRingCatIso
  let α : sfbCoefficientQuotientTower ℤ_[ℓ]
        (Ideal.span ({(ℓ : ℤ_[ℓ])} : Set ℤ_[ℓ])) ⟶ sfbZModCoefficientTower.{u} ℓ :=
    NatTrans.ofOpSequence (fun n ↦ (e n).hom) (fun n ↦ by
      simp only [sfbCoefficientQuotientTower, sfbZModCoefficientTower,
        Functor.ofOpSequence_map_homOfLE_succ]
      ext x
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective x.down
      cases x
      dsimp at hy ⊢
      subst hy
      change ULift.up (sfb_padic_quotient_equiv ℓ n (Ideal.Quotient.mk _ y)) =
        ULift.up (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) _
          (sfb_padic_quotient_equiv ℓ (n + 1) (Ideal.Quotient.mk _ y)))
      rw [sfb_padic_quotient_equiv_mk, sfb_padic_quotient_equiv_mk]
      exact congrArg ULift.up
        (congrArg (fun h : ℤ_[ℓ] →+* ZMod (ℓ ^ n) ↦ h y)
          (PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n))).symm)
  refine ⟨NatIso.ofComponents (fun n ↦ e n.unop) (fun f ↦ α.naturality f), ?_⟩
  intro n x
  exact congrArg ULift.up (sfb_padic_quotient_equiv_mk ℓ n x)

private theorem sfb_comparison_naturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (τ : F ⋙ G ⟶ H)
    {A B : C} (a : A ⟶ B) :
    G.map (F.map a) ≫ τ.app B = τ.app A ≫ H.map a :=
  τ.naturality a

private theorem sfb_comparison_change_inclusion
    (ℓ : ℕ) (R K : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (I : Ideal R)
    {i j : ∀ X : Scheme.{u},
      coefficientRing X (Mon.mk (Profinite.continuousMapRingObj R)) ⟶
        coefficientRing X (Mon.mk (Profinite.continuousMapRingObj K))}
    (hi : ∀ X, i X = j X) (h : SfbCompletedCoefficientComparison ℓ R K I i) :
    SfbCompletedCoefficientComparison ℓ R K I j :=
  (congrArg (SfbCompletedCoefficientComparison ℓ R K I) (funext hi)) ▸ h

private theorem sfb_comparison_of_parts (ℓ : ℕ) (R K : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] (I : Ideal R)
    (i : ∀ X : Scheme.{u}, coefficientRing X (Mon.mk (Profinite.continuousMapRingObj R)) ⟶
      coefficientRing X (Mon.mk (Profinite.continuousMapRingObj K)))
    (hIntegral :
  ∃ ρ : (Functor.const ℕᵒᵖ).obj (Mon.mk (Profinite.continuousMapRingObj.{u} R)) ⟶
      sfbCoefficientQuotientTower R I ⋙ sfbPointConstantRing,
    (∀ n : ℕ, sfbConstantToContinuous R ≫ (ρ.app (op n)).hom =
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
        (AddCommGrpCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((Ideal.Quotient.mk (I ^ n)).comp ULift.ringEquiv.toRingHom)).toAddMonoidHom)) ∧
    (∀ X : Scheme.{u},
      Nonempty (IsLimit ((upperStarFromPoint X).mapMon.mapCone
        (Cone.mk (Mon.mk (Profinite.continuousMapRingObj R)) ρ))) ∧
      Nonempty ((sfbCoefficientQuotientTower R I ⋙ sfbPointConstantRing ⋙
        (upperStarFromPoint X).mapMon) ≅
          (sfbCoefficientQuotientTower R I ⋙ sfbConstantRing X))) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
      Nonempty (IsLimit ((upperStar Ab.{u + 1} f).mapMon.mapCone
        ((upperStarFromPoint Y).mapMon.mapCone
          (Cone.mk (Mon.mk (Profinite.continuousMapRingObj R)) ρ))))) )
    (hRational :
  ∃ ι : ∀ X : Scheme.{u}, sfbRationalizationSequence ℓ R X ⟶
        (Functor.const ℕ).obj (sfbRationalCoefficientModule R K i X),
      (∀ X : Scheme.{u},
        ((ι X).app 0).hom = (i X).hom ∧
        Nonempty (IsColimit (Cocone.mk (sfbRationalCoefficientModule R K i X) (ι X))) ∧
        IsIso (ℓ • 𝟙 (condensedRingObj (Profinite.continuousMapRingObj K) X))) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (m : ℕ),
        (upperStar Ab.{u + 1} f).map (((ι Y).app m).hom) ≫
            ((coefficientPullbackIso f
            (Mon.mk (Profinite.continuousMapRingObj K))).hom).hom =
          ((coefficientPullbackIso f
            (Mon.mk (Profinite.continuousMapRingObj R))).hom).hom ≫
            ((ι X).app m).hom) ∧
      (∀ (X : Scheme.{u}) (B : Mon (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})),
        IsIso (ℓ • 𝟙 B.X) →
        ∀ a : coefficientRing X (Mon.mk (Profinite.continuousMapRingObj R)) ⟶ B,
          ∃! b : coefficientRing X (Mon.mk (Profinite.continuousMapRingObj K)) ⟶ B,
            i X ≫ b = a)) :
    SfbCompletedCoefficientComparison ℓ R K I i := by
  obtain ⟨ρ, hρ, hlim, hbase⟩ := hIntegral
  exact ⟨ρ, hρ, hlim, hbase, hRational⟩

private theorem sfb_finite_completed (ℓ : ℕ) [Fact ℓ.Prime] :
    ∀ (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E),
      IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span ({π} : Set _) →
      SfbCompletedCoefficientComparison.{u} ℓ (PadicAlgCl.integers ℓ E) E
        (Ideal.span ({π} : Set _))
        (fun X ↦ Mon.ofHom (padicIntegersToPadicSubfield X ℓ E)) := by
  classical
  intro E π hπ
  let R := PadicAlgCl.integers ℓ E
  let iSource (X : Scheme.{u}) := completedCoefficientMap X
    (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing ℓ E)
  apply sfb_comparison_change_inclusion ℓ R E (Ideal.span {π}) (i := iSource)
  · intro X
    apply Mon.Hom.ext
    rfl
  · refine sfb_comparison_of_parts ℓ R E (Ideal.span {π}) iSource ?_ ?_
    · let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
      let : NormedAlgebra ℚ_[ℓ] E.1 :=
        { norm_smul_le c x := by
            change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
              ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
            rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
              PadicAlgCl.norm_extends] }
      let : CompactSpace R := PadicAlgCl.compactSpace_integers ℓ E.1
      let : ∀ n : ℕ, Finite (R ⧸ Ideal.span {π} ^ n) := fun n ↦ by
        rw [← hπ]
        infer_instance
      let : ∀ n : ℕ, DiscreteTopology (R ⧸ Ideal.span {π} ^ n) := fun n ↦ by
        apply QuotientAddGroup.discreteTopology
        rw [← hπ]
        exact IsLocalRing.isOpen_maximalIdeal_pow R n
      have hsep (x y : R) (h : ∀ n : ℕ,
          Ideal.Quotient.mk (Ideal.span {π} ^ n) x =
            Ideal.Quotient.mk (Ideal.span {π} ^ n) y) : x = y := by
        apply (IsHausdorff.eq_iff_smodEq (I := IsLocalRing.maximalIdeal R)).mpr
        intro n
        have hn := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (h n)
        simpa only [← hπ, Ideal.smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] using hn
      exact sfb_normalized_integral_quotient_cone.{u} R (Ideal.span {π}) hsep
    · exact sfb_rational_comparison_from_completed ℓ R E
        (PadicAlgCl.integers ℓ E).subtype continuous_subtype_val
        (completedCondensedRational.{u} ℓ E)

private theorem sfb_padic_completed (ℓ : ℕ) [Fact ℓ.Prime] :
    SfbCompletedCoefficientComparison.{u} ℓ ℤ_[ℓ] ℚ_[ℓ]
      (Ideal.span ({(ℓ : ℤ_[ℓ])} : Set ℤ_[ℓ]))
      (sfbCoefficientInclusion ℤ_[ℓ] ℚ_[ℓ] PadicInt.Coe.ringHom
        continuous_subtype_val) := by
  classical
  let I : Ideal ℤ_[ℓ] := Ideal.span {(ℓ : ℤ_[ℓ])}
  let : ∀ n : ℕ, Finite (ℤ_[ℓ] ⧸ I ^ n) := fun n ↦
    Finite.of_equiv (ZMod (ℓ ^ n)) (sfb_padic_quotient_equiv ℓ n).symm.toEquiv
  let : ∀ n : ℕ, DiscreteTopology (ℤ_[ℓ] ⧸ I ^ n) := fun n ↦ by
    apply QuotientAddGroup.discreteTopology
    change IsOpen (X := ℤ_[ℓ]) ↑(Ideal.span {(ℓ : ℤ_[ℓ])} ^ n)
    rw [← PadicInt.maximalIdeal_eq_span_p]
    exact IsLocalRing.isOpen_maximalIdeal_pow ℤ_[ℓ] n
  have hsep (x y : ℤ_[ℓ]) (h : ∀ n : ℕ,
      Ideal.Quotient.mk (I ^ n) x = Ideal.Quotient.mk (I ^ n) y) : x = y := by
    dsimp only [I] at h
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    simpa only [sfb_padic_quotient_equiv_mk] using
      congrArg (sfb_padic_quotient_equiv ℓ n) (h n)
  let iSource (X : Scheme.{u}) := completedCoefficientMap X
    (Profinite.padicIntCondensedRingToPadicCondensedRing ℓ)
  apply sfb_comparison_change_inclusion ℓ ℤ_[ℓ] ℚ_[ℓ] I (i := iSource)
  · intro X
    apply Mon.Hom.ext
    rfl
  · refine sfb_comparison_of_parts ℓ ℤ_[ℓ] ℚ_[ℓ] I iSource ?_ ?_
    · exact sfb_normalized_integral_quotient_cone.{u} ℤ_[ℓ] I hsep
    · exact sfb_rational_comparison_from_completed ℓ ℤ_[ℓ] ℚ_[ℓ]
        PadicInt.Coe.ringHom continuous_subtype_val
        (completedCondensedPadicRational.{u} ℓ)

/-- The three completed-coefficient comparisons, their inverse-image compatibility, and
specialization to `ℤ_ℓ` and `ℚ_ℓ`.
-/
theorem sfb_completed_coefficients (ℓ : ℕ) [Fact ℓ.Prime] :
    (∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (π : PadicAlgCl.integers ℓ E),
      IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span ({π} : Set _) →
      SfbCompletedCoefficientComparison.{u} ℓ (PadicAlgCl.integers ℓ E) E
        (Ideal.span ({π} : Set _))
        (fun X ↦ Mon.ofHom (padicIntegersToPadicSubfield X ℓ E))) ∧
    SfbCompletedCoefficientComparison.{u} ℓ ℤ_[ℓ] ℚ_[ℓ]
      (Ideal.span ({(ℓ : ℤ_[ℓ])} : Set ℤ_[ℓ]))
      (sfbCoefficientInclusion ℤ_[ℓ] ℚ_[ℓ] PadicInt.Coe.ringHom
        continuous_subtype_val) ∧
    (∃ e : sfbCoefficientQuotientTower ℤ_[ℓ]
        (Ideal.span ({(ℓ : ℤ_[ℓ])} : Set ℤ_[ℓ])) ≅ sfbZModCoefficientTower.{u} ℓ,
      ∀ (n : ℕ) (x : ℤ_[ℓ]),
        (e.hom.app (op n)).hom (ULift.up (Ideal.Quotient.mk
          (Ideal.span ({(ℓ : ℤ_[ℓ])} : Set ℤ_[ℓ]) ^ n) x)) =
            ULift.up (PadicInt.toZModPow n x)) ∧
    (∀ X : Scheme.{u}, Nonempty (IsColimit
      ((upperStarFromPoint X).mapMon.mapCocone (sfbFiniteSubfieldRingCocone ℓ)))) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y), Nonempty (IsColimit
      ((upperStar Ab.{u + 1} f).mapMon.mapCocone
        ((upperStarFromPoint Y).mapMon.mapCocone (sfbFiniteSubfieldRingCocone ℓ))))) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (E : PadicAlgCl.FiniteIntermediateField ℓ),
      (upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl Y ℓ E) ≫
          condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) f =
        condensedPullbackHom (Profinite.continuousMapRingObj E) f ≫
          padicSubfieldRingObjToPadicAlgCl X ℓ E) := by
  classical
  refine ⟨sfb_finite_completed ℓ, sfb_padic_completed ℓ,
    sfb_padic_quotient_tower ℓ, ?_, ?_, ?_⟩
  · intro X
    apply (Mon.filtered_cocone_isColimit
      ((upperStarFromPoint X).mapMon.mapCocone (sfbFiniteSubfieldRingCocone ℓ)) ?_).1
    change IsColimit (padicAlgClRingObjCocone X ℓ)
    exact isColimitPadicAlgClRingObjCocone X ℓ
  · intro X Y f
    apply (Mon.filtered_cocone_isColimit
      ((upperStar Ab.{u + 1} f).mapMon.mapCocone
        ((upperStarFromPoint Y).mapMon.mapCocone (sfbFiniteSubfieldRingCocone ℓ))) ?_).1
    change IsColimit ((upperStar Ab.{u + 1} f).mapCocone (padicAlgClRingObjCocone Y ℓ))
    exact isColimitOfPreserves (upperStar Ab.{u + 1} f)
      (isColimitPadicAlgClRingObjCocone Y ℓ)
  · intro X Y f E
    exact sfb_comparison_naturality (upperStarFromPoint Y) (upperStar Ab.{u + 1} f)
      (upperStarFromPoint X) (upperStarFromPointComp f).hom
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)

end AlgebraicGeometry.ProEtale
