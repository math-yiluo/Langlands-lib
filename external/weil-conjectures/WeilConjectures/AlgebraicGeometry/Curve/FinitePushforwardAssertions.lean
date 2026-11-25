/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CurveCoefficientPair
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.AlgebraicGeometry.Curve.FinitePushforwardCoefficientControl
import WeilConjectures.AlgebraicGeometry.Curve.FinitePushforwardCohomologyComparison
import WeilConjectures.AlgebraicGeometry.Curve.FinitePushforwardPullbackComparison
/-!
# Finite pushforward of the eight curve assertions

Source: Stacks Project, Etale Cohomology, Lemma 0A5D (59.83.5).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem finite_lowerStar_torsion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : X.IsTorsionAbelianSheaf F) :
    Y.IsTorsionAbelianSheaf ((Etale.lowerStar AddCommGrpCat.{u + 1} f).obj F) := by
  classical
  apply (Scheme.isTorsionAbelianSheaf_characterizations _).2.mpr
  intro Ω inst inst' y
  let T := Scheme.Hom.GeometricFiber f y
  let M := fun t : T ↦
    ((Scheme.pointSmallEtale t.1).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F
  let e := Etale.stalkIsoPi AddCommGrpCat.{u + 1} f y F
  let φ : ((Scheme.pointSmallEtale y).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((Etale.lowerStar AddCommGrpCat.{u + 1} f).obj F) →+ (∀ t : T, M t) :=
    { toFun := fun x t ↦ Etale.stalkRestrict AddCommGrpCat.{u + 1} f y t F x
      map_zero' := by funext t; exact map_zero _
      map_add' := by intro x z; funext t; exact map_add _ _ _ }
  have hφ : Function.Injective φ := by
    intro x z hxz
    apply (ConcreteCategory.bijective_of_isIso e.hom).1
    apply CategoryTheory.Limits.Concrete.limit_ext
    intro t
    change (e.hom ≫ CategoryTheory.Limits.Pi.π M t.as) x =
      (e.hom ≫ CategoryTheory.Limits.Pi.π M t.as) z
    dsimp only [e]
    rw [Etale.stalkIsoPi_hom]
    erw [CategoryTheory.Limits.Pi.lift_comp_π]
    exact congrFun hxz t.as
  intro x
  apply hφ.isOfFinAddOrder_iff.mp
  apply IsOfFinAddOrder.pi
  intro t
  exact (Scheme.isTorsionAbelianSheaf_characterizations F).2.mp hF Ω t.1 (φ x t)

/-- Finite pushforward preserves torsion and transfers each of the eight curve assertions
separately, and therefore their conjunction. Source: Stacks Project, Lemma 0A5D,
Section 03SB.

Abelian sheaves are viewed as modules over `ULift ℤ` through the inverse of the standard
forgetful equivalence, followed by restriction along `ULift.ringEquiv`. This is only a
change of coefficient category, and imposes no extra structure on the abelian sheaf.

Proof (the node's eight steps):
1. The finite stalk formula (lemma-weil-pbc-finite-stalk-formula) expresses a stalk of the
pushforward as a finite product of torsion stalks. The torsion characterizations
(definition-torsion-sheaves--3) then give torsion of the pushforward.
2. Each source stalk is a direct factor of the pushforward stalk over its image. Thus
p-primary torsion and torsion prime to the characteristic descend from the pushforward.
3. The finite cohomology edge map (lemma-finite-morphisms-cohomology--2) is an
isomorphism in every degree, identifying vanishing and finiteness on the two schemes.
4. Transfer C1 by this identification. For C2, affineness of Y implies affineness of X;
for C3 use step 2. These use lem-weil-pbc-finite-morphism-permanence.
5. Constructibility descends from the pushforward by
lem-weil-pbc-finite-pushforward-constructible-descent. Combine this with steps 2 and 3
for C4; for C5 also use that finite over proper is proper.
6. For C6 and C7, form the base-change square for an algebraically closed field extension.
Finite exchange (lemma-weil-pbc-finite-exchange) and the finite edge maps are isomorphisms.
Their compatibility (lem-weil-pbc-edge-map-base-change) identifies the two pullback maps.
Pasting identifies the source base change with its field extension; composition
(proposition-cohomology-p-1-over-henselian--1 and lem-weil-pbc-inverse-image-composition)
transfers bijectivity. Apply step 2 for C6 and properness permanence for C7.
7. For an open immersion into Y, its pullback into X is open and the induced finite
morphism has the same exchange and edge isomorphisms. Compatibility gives a commuting
restriction square; lift the corresponding class by C8 on X and transport it back by
the inverse edge map. Injectivity of the comparison proves that it restricts to the
given class on the open of Y.
8. The eight separate implications give the implication between their conjunctions,
using theorem-cohomology-curves. Together with step 1 this proves both clauses. -/
theorem IsCurve.finite_pushforward_assertions {k : Type u} [Field k] [IsAlgClosed k]
    (P : CurveCoefficientPair k) {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [IsCurve g] (f : P.C ⟶ Y) [IsFinite f]
    (hf : f ≫ g = P.toSpec) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let FX := (sheafCompose P.C.smallEtaleTopology E).obj P.F
    let G := (Etale.lowerStar AddCommGrpCat.{u + 1} f).obj P.F
    let FY := (sheafCompose Y.smallEtaleTopology E).obj G
    Y.IsTorsionAbelianSheaf G ∧
      (IsCurve.VanishingAboveTwo (ULift.{u + 1} ℤ) FX →
        IsCurve.VanishingAboveTwo (ULift.{u + 1} ℤ) FY) ∧
      (IsCurve.VanishingAboveOneOfIsAffine (ULift.{u + 1} ℤ) FX →
        IsCurve.VanishingAboveOneOfIsAffine (ULift.{u + 1} ℤ) FY) ∧
      (IsCurve.VanishingAboveOneOfIsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) FX k →
        IsCurve.VanishingAboveOneOfIsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) FY k) ∧
      (IsCurve.FiniteOfInvertibleOrder (ULift.{u + 1} ℤ) FX k →
        IsCurve.FiniteOfInvertibleOrder (ULift.{u + 1} ℤ) FY k) ∧
      (IsCurve.FiniteOfIsProper (ULift.{u + 1} ℤ) P.toSpec FX →
        IsCurve.FiniteOfIsProper (ULift.{u + 1} ℤ) g FY) ∧
      (IsCurve.BaseChangeOfInvertibleOrder (ULift.{u + 1} ℤ) P.toSpec FX →
        IsCurve.BaseChangeOfInvertibleOrder (ULift.{u + 1} ℤ) g FY) ∧
      (IsCurve.BaseChangeOfIsProper (ULift.{u + 1} ℤ) P.toSpec FX →
        IsCurve.BaseChangeOfIsProper (ULift.{u + 1} ℤ) g FY) ∧
      (IsCurve.SurjectiveRestrictionTwo (ULift.{u + 1} ℤ) FX →
        IsCurve.SurjectiveRestrictionTwo (ULift.{u + 1} ℤ) FY) ∧
      (IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec FX →
        IsCurve.Assertions (ULift.{u + 1} ℤ) g FY) := by
  classical
  dsimp only
  let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
  let FX := (sheafCompose P.C.smallEtaleTopology E).obj P.F
  let G := (Etale.lowerStar AddCommGrpCat.{u + 1} f).obj P.F
  let FY := (sheafCompose Y.smallEtaleTopology E).obj G
  obtain ⟨hprimary, hconstructible, hinvertible⟩ :=
    IsCurve.finite_pushforward_coefficient_control P g f hf
  have hT := finite_lowerStar_torsion f P.F 
    ((Scheme.isTorsionAbelianSheaf_characterizations
      P.F).1.mpr P.isTorsion)
  have hcoh := IsCurve.finite_pushforward_cohomology_comparison P g f hf
  have hproper [IsProper g] : IsProper P.toSpec := by
    rw [← hf]
    infer_instance
  have h₁ : IsCurve.VanishingAboveTwo (ULift.{u + 1} ℤ) FX →
      IsCurve.VanishingAboveTwo (ULift.{u + 1} ℤ) FY := by
    intro h q hq
    obtain ⟨e⟩ := hcoh q
    have := h q hq
    exact e.injective.subsingleton
  have h₂ : IsCurve.VanishingAboveOneOfIsAffine (ULift.{u + 1} ℤ) FX →
      IsCurve.VanishingAboveOneOfIsAffine (ULift.{u + 1} ℤ) FY := by
    intro h inst q hq
    have : IsAffine P.C := isAffine_of_isAffineHom f
    obtain ⟨e⟩ := hcoh q
    have := h q hq
    exact e.injective.subsingleton
  have h₃ : IsCurve.VanishingAboveOneOfIsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) FX k →
      IsCurve.VanishingAboveOneOfIsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) FY k := by
    intro h p inst inst' ht q hq
    obtain ⟨e⟩ := hcoh q
    have := h p (hprimary p ht) q hq
    exact e.injective.subsingleton
  have h₄ : IsCurve.FiniteOfInvertibleOrder (ULift.{u + 1} ℤ) FX k →
      IsCurve.FiniteOfInvertibleOrder (ULift.{u + 1} ℤ) FY k := by
    intro h inst inst' q
    have := hconstructible (inferInstance : Scheme.IsConstructibleSheaf FY)
    have := hinvertible
      (inferInstance : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) FY)
    have := h q
    obtain ⟨e⟩ := hcoh q
    exact Finite.of_injective e e.injective
  have h₅ : IsCurve.FiniteOfIsProper (ULift.{u + 1} ℤ) P.toSpec FX →
      IsCurve.FiniteOfIsProper (ULift.{u + 1} ℤ) g FY := by
    intro h inst inst' q
    have := hproper
    have := hconstructible (inferInstance : Scheme.IsConstructibleSheaf FY)
    have := h q
    obtain ⟨e⟩ := hcoh q
    exact Finite.of_injective e e.injective
  have h₆ : IsCurve.BaseChangeOfInvertibleOrder (ULift.{u + 1} ℤ) P.toSpec FX →
      IsCurve.BaseChangeOfInvertibleOrder (ULift.{u + 1} ℤ) g FY := by
    intro h inst k' inst' inst'' Y' ι g' a sq q
    have := hinvertible
      (inferInstance : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) FY)
    let b := Limits.pullback.fst f a
    let f' := Limits.pullback.snd f a
    have sq' : IsPullback b f' f a := IsPullback.of_hasPullback f a
    have sqX : IsPullback b (f' ≫ g') P.toSpec ι := by
      rw [← hf]
      exact sq'.paste_vert sq
    exact (IsCurve.finite_pushforward_pullback_comparison P g f hf sq' q).1.mpr (h k' sqX q)
  have h₇ : IsCurve.BaseChangeOfIsProper (ULift.{u + 1} ℤ) P.toSpec FX →
      IsCurve.BaseChangeOfIsProper (ULift.{u + 1} ℤ) g FY := by
    intro h inst k' inst' inst'' Y' ι g' a sq q
    have := hproper
    let b := Limits.pullback.fst f a
    let f' := Limits.pullback.snd f a
    have sq' : IsPullback b f' f a := IsPullback.of_hasPullback f a
    have sqX : IsPullback b (f' ≫ g') P.toSpec ι := by
      rw [← hf]
      exact sq'.paste_vert sq
    exact (IsCurve.finite_pushforward_pullback_comparison P g f hf sq' q).1.mpr (h k' sqX q)
  have h₈ : IsCurve.SurjectiveRestrictionTwo (ULift.{u + 1} ℤ) FX →
      IsCurve.SurjectiveRestrictionTwo (ULift.{u + 1} ℤ) FY := by
    intro h W a inst
    let b := Limits.pullback.fst f a
    let f' := Limits.pullback.snd f a
    have sq' : IsPullback b f' f a := IsPullback.of_hasPullback f a
    have : IsOpenImmersion b := inferInstance
    exact (IsCurve.finite_pushforward_pullback_comparison P g f hf sq' 2).2.mpr (h b)
  refine ⟨hT, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, ?_⟩
  intro h
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ :=
    (IsCurve.assertions_iff (ULift.{u + 1} ℤ) P.toSpec FX).mp h
  exact (IsCurve.assertions_iff (ULift.{u + 1} ℤ) g FY).mpr
    ⟨h₁ a₁, h₂ a₂, h₃ a₃, h₄ a₄, h₅ a₅, h₆ a₆, h₇ a₇, h₈ a₈⟩

end AlgebraicGeometry
