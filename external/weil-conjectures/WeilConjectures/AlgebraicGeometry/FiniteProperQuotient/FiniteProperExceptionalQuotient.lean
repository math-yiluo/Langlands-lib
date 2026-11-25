/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.NumberTheory.Padics.OrdinaryExceptionalCtfPreservation
public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension
import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientProjectionDataSupplement

import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientPullbackComparisonSupplement
import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientPullbackShifts
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientScalarUnits
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint

/-! # Finite proper exceptional inverse image and quotient coefficients

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-coefficients-constructible/sec-n-brown/sk-thm-existence/
lem-sfb-dc-proper-pushforward-left-adjoint-e.proof.md, sentences 2--3;
Zheng, Propositions 2.29(2) and 3.16(2).
(blueprint: lem-sfb-finite-proper-exceptional-quotient)

Indices `n : ℕ` denote the positive exponents `n + 1`. All categories are ordinary
unbounded small-etale derived categories. Only their ctf object predicates are restricted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteProperQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual quotient by the indicated power of ell, rather than a uniformizer power.
Source: blueprint finite torsion levels
(blueprint: lem-sfb-finite-proper-exceptional-quotient). -/
abbrev Ring (n : ℕ) :=
  Padic.coefficientExtensionEllQuotient l E (n + 1)

/-- The quotient homomorphism induced by the identity of the ring of integers.
Source: blueprint reduction sentence
(blueprint: lem-sfb-finite-proper-exceptional-quotient). -/
def quotient {m n : ℕ} (h : n ≤ m) : Ring l E m →+* Ring l E n :=
  Ideal.Quotient.factor
    (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.add_le_add_right h 1)))

/-- Derived quotient tensor on the ambient ordinary etale category.
Source: blueprint reduction sentence; Stacks 06YY
(blueprint: lem-sfb-finite-proper-exceptional-quotient). -/
abbrev Q (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :=
  scalarExtension (quotient l E h) T

/-- The ordinary, unbounded derived direct image with this finite coefficient ring.
Source: blueprint torsion-level Rp_*
(blueprint: lem-sfb-finite-proper-exceptional-quotient). -/
abbrev F {Z Y : Scheme.{u}} (p : Z ⟶ Y) (n : ℕ) :=
  R(lowerStar (ModuleCat.{u + 1} (Ring l E n)) p)

/-- The existing bounded constructible finite-Tor predicate. For the Noetherian schemes
of this theorem, its finite stratification condition is equivalent to affine-local
constructibility. Source: Stacks 03RW(3), 09AL and blueprint ctf clause
(blueprint: lem-sfb-finite-proper-exceptional-quotient). -/
abbrev Ctf (T : Scheme.{u}) (n : ℕ) :=
  DerivedCategory.boundedConstructibleFiniteTor (Ring l E n) T

/-- Canonical tensor reassociation: conjugate the sectionwise restriction comparison.
Source: Stacks 06YY, successive quotient normalization
(blueprint: lem-sfb-finite-proper-exceptional-quotient). -/
def reassoc (T : Scheme.{u}) {m n t : ℕ} (h : n ≤ m) (ht : t ≤ n) :
    Q l E T h ⋙ Q l E T ht ≅ Q l E T (ht.trans h) :=
  Adjunction.leftAdjointCompIso
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology (quotient l E h)))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology (quotient l E ht)))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology (quotient l E (ht.trans h))))
    (Sheaf.derivedRestrictScalarsCompIso T.smallEtaleTopology
      (RingHom.ext fun x ↦ Quotient.inductionOn x fun _ ↦ rfl))

/-- The sectionwise identity restriction at an equal-index quotient.
Source: Stacks 03EK, identity coefficient change
(blueprint: lem-sfb-finite-proper-exceptional-quotient). -/
def restrictionSelf (T : Scheme.{u}) (n : ℕ) :
    Sheaf.restrictScalars T.smallEtaleTopology (quotient l E (le_refl n)) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun M ↦ (fullyFaithfulSheafToPresheaf T.smallEtaleTopology _).preimageIso
      (Functor.isoWhiskerLeft M.obj
        (ModuleCat.restrictScalarsId' (quotient l E (le_refl n))
          (RingHom.ext fun x ↦ Quotient.inductionOn x fun _ ↦ rfl))))
    (fun {_ _} f ↦ by ext U x; rfl)

/-- The tensor identity comparison, fixed by the scalar adjunction.
Source: Stacks 06YY, identity coefficient change
(blueprint: lem-sfb-finite-proper-exceptional-quotient). -/
def selfReduction (T : Scheme.{u}) (n : ℕ) : Q l E T (le_refl n) ≅ 𝟭 _ :=
  ((conjugateIsoEquiv
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology (quotient l E (le_refl n))))
    (Adjunction.id : 𝟭 (DerivedCategoryModule (Ring l E n) T) ⊣ 𝟭 _)).symm
      (Functor.mapDerivedCategoryNatIso (restrictionSelf l E T n) ≪≫
        Functor.mapDerivedCategoryIdIso _)).symm

variable {Z Y : Scheme.{u}} (p : Z ⟶ Y)
  (G : ∀ n : ℕ, DerivedCategoryModule (Ring l E n) Y ⥤
    DerivedCategoryModule (Ring l E n) Z)
  (adj : ∀ n : ℕ, F l E p n ⊣ G n)

/-- The right-adjoint mate of the inverse of the canonical proper comparison.
Source: blueprint quotient mate, counit transpose; Mathlib mateEquiv
(blueprint: lem-sfb-finite-proper-exceptional-quotient). -/
def b {m n : ℕ} (h : n ≤ m)
    (q : F l E p m ⋙ Q l E Y h ≅ Q l E Z h ⋙ F l E p n) :
    G m ⋙ Q l E Z h ⟶ Q l E Y h ⋙ G n :=
  (mateEquiv (adj m) (adj n) (.mk _ _ _ _ q.inv))

include G adj in
/-- Ordinary proper exceptional inverse images preserve ctf and have coherent quotient mates.
Source: blueprint proof sentences 2--3; Zheng 2.29(2), 3.16(2)
(blueprint: lem-sfb-finite-proper-exceptional-quotient).

Proof: (1) proper compact supports are ordinary Rp_*. Apply the ordinary-etale
exceptional ctf preservation theorem to each chosen adjunction, over the arbitrary field.
(2) Proper finite coefficient extension makes scalarMate invertible; its normalization is
its inverse-image counit transpose. (3) Take the mate of its inverse. Ordinary exceptional
change of rings gives invertibility on ctf (Zheng 2.29(2), after conservative restriction
of scalars), and mateEquiv_counit gives precisely the stated counit equation. Applying
unit_mateEquiv and then the image of q gives the unit equation. (4) The normalized
successive quotient tensor comparison and the coefficient projection cocycle identify
the pasted q square with q for the composite quotient. Mate pasting gives the displayed
b equation. The identity coefficient comparison and its tensor unitor give the last
formula. None of these steps assumes flat quotient coefficients or finite cd of k.

The proof dependencies are lem-sfb-ordinary-exceptional-ctf-preservation and
theorem-existence-exceptional-inverse-image--1 in step 1;
lem-asd-proper-finite-coefficient-extension in step 2; def-sf-etale-exceptional-quotient-mate,
lem-sfb-ordinary-exceptional-change-of-rings and lem-pur-mate-unit-compatibility in step 3;
lem-sfb-successive-derived-quotient-normalization,
lem-pur-ringed-coefficient-projection-cocycle, lem-weil-pbc-mate-pasting and
def-weil-pbc-adjunction-mate in step 4. -/
theorem finite_proper_exceptional_quotient
    (p₀ : ℕ) [Fact p₀.Prime] (k : Type u) [Field k] [CharP k p₀] (_hl : l ≠ p₀)
    [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [p.IsOver (Spec (.of k))] [IsProper p] :
    (∀ (n : ℕ) (L : DerivedCategoryModule (Ring l E n) Y),
      Ctf l E Y n L → Ctf l E Z n ((G n).obj L)) ∧
    ∃ q : ∀ {m n : ℕ} (h : n ≤ m),
        F l E p m ⋙ Q l E Y h ≅ Q l E Z h ⋙ F l E p n,
      (∀ {m n : ℕ} (h : n ≤ m), (q h).hom = scalarMate (quotient l E h) p) ∧
      (∀ {m n : ℕ} (h : n ≤ m) (L : DerivedCategoryModule (Ring l E m) Y),
        Ctf l E Y m L → IsIso ((b l E p G adj h (q h)).app L)) ∧
      (∀ {m n : ℕ} (h : n ≤ m) (L : DerivedCategoryModule (Ring l E m) Y),
        Ctf l E Y m L →
        (q h).hom.app ((G m).obj L) ≫
          (F l E p n).map ((b l E p G adj h (q h)).app L) ≫
          (adj n).counit.app ((Q l E Y h).obj L) =
        (Q l E Y h).map ((adj m).counit.app L)) ∧
      (∀ {m n : ℕ} (h : n ≤ m) (K : DerivedCategoryModule (Ring l E m) Z),
        Ctf l E Z m K → Ctf l E Y m ((F l E p m).obj K) →
        (Q l E Z h).map ((adj m).unit.app K) ≫
          (b l E p G adj h (q h)).app ((F l E p m).obj K) ≫
          (G n).map ((q h).hom.app K) = (adj n).unit.app ((Q l E Z h).obj K)) ∧
      (∀ {m n t : ℕ} (h : n ≤ m) (ht : t ≤ n)
          (L : DerivedCategoryModule (Ring l E m) Y), Ctf l E Y m L →
        (Q l E Z ht).map ((b l E p G adj h (q h)).app L) ≫
          (b l E p G adj ht (q ht)).app ((Q l E Y h).obj L) ≫
          (G t).map ((reassoc l E Y h ht).hom.app L) =
        (reassoc l E Z h ht).hom.app ((G m).obj L) ≫
          (b l E p G adj (ht.trans h) (q (ht.trans h))).app L) ∧
      (∀ (n : ℕ) (L : DerivedCategoryModule (Ring l E n) Y), Ctf l E Y n L →
        (b l E p G adj (le_refl n) (q (le_refl n))).app L ≫
          (G n).map ((selfReduction l E Y n).hom.app L) =
        (selfReduction l E Z n).hom.app ((G n).obj L)) := by
  sorry

end AlgebraicGeometry.Etale.FiniteProperQuotient
