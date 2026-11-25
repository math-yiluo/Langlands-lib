/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Isomorphism.IsomorphismFieldTransportClauses
import WeilConjectures.PoincareDuality.Isomorphism.IsomorphismFieldTransportFiniteStage
import WeilConjectures.PoincareDuality.Isomorphism.IsomorphismFieldTransportRationalScalar
import WeilConjectures.PoincareDuality.Isomorphism.IsomorphismFieldTransportCommonStage
import WeilConjectures.PoincareDuality.Isomorphism.IsomorphismScalarComparisonAgreement
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Exact isomorphism transport at integral and field coefficient stages

Source: main-20261015, sec-poincare-duality/sk-lem-finite,
prop-weil-operations.proof.md, sentence 1, through prose-10-20,
first paragraph (blueprint: lem-pod-isomorphism-field-transport).

All functors, coefficient maps, scalar comparisons and quotient Hom constructors
below are the published constructions. The clause records specify comparisons,
rather than selecting arbitrary inverse equivalences.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option linter.privateModule false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (ofHom inclusion)

private theorem transport_stalkUnits
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (W : Scheme.{u}) [W.Over (Spec (.of D.k))] :
    ∀ w : W, IsUnit (l : W.presheaf.stalk w) := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  have hu : IsUnit (l : D.k₀) := (CharP.isUnit_natCast_iff D.prime).2 (by
    intro hdiv
    exact hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 hdiv).symm)
  have hk : IsUnit (l : D.k) := by
    simpa only [map_natCast] using hu.map (algebraMap D.k₀ D.k)
  intro w
  simpa only [map_natCast] using hk.map
    (StructureSheaf.toStalk (CommRingCat.of D.k) ((W ↘ Spec (.of D.k)) w) ≫
      (W ↘ Spec (.of D.k)).stalkMap w).hom

private theorem transport_scalarLaw
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    isomorphismFieldTransportScalarLaw l E L ι g := by
  obtain ⟨D, _⟩ := integralPullbackComparisonRealization l E L ι
  intro K
  have h := (pullbackIdentities_scalarExtension l E L ι D).2 g K
  rw [isomorphismScalarComparisonAgreement l E L ι D (inv g),
    isomorphismScalarComparisonAgreement l E L ι D g] at h
  exact heq_of_eq h

/-- Exact inverse transport through the completed integral, raw rational and common-stage
categories, with both normalized inverse comparisons and their scalar equations.
Source: main-20261015, sec-poincare-duality/sk-lem-finite,
prop-weil-operations.proof.md sentence 1 through prose-10-20 paragraph 1
(blueprint: lem-pod-isomorphism-field-transport).

Proof: the finite-field cardinality gives characteristic p on k₀. Since l is a
prime distinct from p, it is a unit in k₀, in k and in every stalk of X and Y.
Map these stalk units to their residue fields and use their canonical invertibility
data. Apply isomorphismFieldTransportFiniteStage to g and inv g at each finite E.
For the integral scalar equations choose a normalized comparison system, use
pullbackIdentities_scalarExtension, and replace its two scalar comparisons by the
specified tensor/completion comparisons using isomorphismScalarComparisonAgreement.
The changed auxiliary completeness proofs are proof irrelevant. Choose the finite
stages at the small coefficient models and apply isomorphismFieldTransportRationalScalar
to their integral scalar equations. Finally apply isomorphismFieldTransportCommonStage
after obtaining noetherian and finite-dimension bounds from finite type,
to the two families and both scalar equations. Repeat with inv g, constructing its
normalized opposite family directly at inv (inv g). These three lemmas separate
the finite-stage construction,
localization of a scalar equation, and descent of the resulting family; they do not
change the specified functors, comparisons, or the categories in the conclusion.
-/
theorem isomorphismFieldTransport
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (g : X ⟶ Y) [IsIso g] :
    ∃ (iX : ∀ x : X, Invertible (l : X.residueField x))
      (iY : ∀ y : Y, Invertible (l : Y.residueField y)),
      (fun [_iX : ∀ x : X, Invertible (l : X.residueField x)]
        [_iY : ∀ y : Y, Invertible (l : Y.residueField y)] ↦
        ∃ (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
          (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)),
          (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
            Nonempty (IsomorphismFieldTransportStage l E g hX hY) ∧
            Nonempty (IsomorphismFieldTransportStage l E (inv g) hY hX)) ∧
          (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
            (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
            (ι : E →ₐ[ℚ_[l]] L),
            isomorphismFieldTransportScalarLaw l E L ι g ∧
            isomorphismFieldTransportScalarLaw l E L ι (inv g)) ∧
          ∃ (S : ∀ E : Index l Ω,
              IsomorphismFieldTransportStage l (Coefficient.{u} l Ω E) g hX hY)
            (R : ∀ E : Index l Ω,
              IsomorphismFieldTransportStage l (Coefficient.{u} l Ω E) (inv g) hY hX),
            (∀ (E L : Index l Ω) (h : E ≤ L),
              isomorphismFieldTransportRationalScalarLaw l
                (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
                (coefficientInclusion l Ω E L h) g hX hY (S E) (S L) ∧
              isomorphismFieldTransportRationalScalarLaw l
                (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
                (coefficientInclusion l Ω E L h) (inv g) hY hX (R E) (R L)) ∧
            Nonempty (IsomorphismFieldTransportCommon l Ω g hX hY S) ∧
            Nonempty (IsomorphismFieldTransportCommon l Ω (inv g) hY hX R))
        (_iX := iX) (_iY := iY) := by
  classical
  let hX := transport_stalkUnits D l _hl X
  let hY := transport_stalkUnits D l _hl Y
  let iX : ∀ x : X, Invertible (l : X.residueField x) :=
    fun x ↦ (show IsUnit (l : X.residueField x) by
      simpa only [map_natCast] using (hX x).map (X.residue x).hom).invertible
  let iY : ∀ y : Y, Invertible (l : Y.residueField y) :=
    fun y ↦ (show IsUnit (l : Y.residueField y) by
      simpa only [map_natCast] using (hY y).map (Y.residue y).hom).invertible
  refine ⟨iX, iY, ?_⟩
  let := iX
  let := iY
  refine ⟨hX, hY, ?_, ?_, ?_⟩
  · intro E _ _ _
    exact ⟨isomorphismFieldTransportFiniteStage l E g hX hY,
      isomorphismFieldTransportFiniteStage l E (inv g) hY hX⟩
  · intro E _ _ _ L _ _ _ ι
    exact ⟨transport_scalarLaw l E L ι g, transport_scalarLaw l E L ι (inv g)⟩
  · have : IsLocallyNoetherian X :=
      LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
    have : IsNoetherian X := {}
    have : IsLocallyNoetherian Y :=
      LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of D.k))
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
    have : IsNoetherian Y := {}
    obtain ⟨dX, hdX⟩ := exists_topologicalKrullDim_le (X ↘ Spec (.of D.k))
    obtain ⟨dY, hdY⟩ := exists_topologicalKrullDim_le (Y ↘ Spec (.of D.k))
    let S : ∀ E : Index l Ω,
        IsomorphismFieldTransportStage l (Coefficient.{u} l Ω E) g hX hY :=
      fun E ↦ Classical.choice
        (isomorphismFieldTransportFiniteStage l (Coefficient.{u} l Ω E) g hX hY)
    let R : ∀ E : Index l Ω,
        IsomorphismFieldTransportStage l (Coefficient.{u} l Ω E) (inv g) hY hX :=
      fun E ↦ Classical.choice
        (isomorphismFieldTransportFiniteStage l (Coefficient.{u} l Ω E) (inv g) hY hX)
    have hS (E L : Index l Ω) (h : E ≤ L) :=
      isomorphismFieldTransportRationalScalar l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) g hX hY
        (S E) (S L) (transport_scalarLaw l _ _ _ g)
    have hR (E L : Index l Ω) (h : E ≤ L) :=
      isomorphismFieldTransportRationalScalar l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) (inv g) hY hX
        (R E) (R L) (transport_scalarLaw l _ _ _ (inv g))
    refine ⟨S, R, fun E L h ↦ ⟨hS E L h, hR E L h⟩,
      isomorphismFieldTransportCommonStage l Ω g ⟨dX, hdX⟩ ⟨dY, hdY⟩ hX hY S R hS hR, ?_⟩
    let Sop : ∀ E : Index l Ω,
        IsomorphismFieldTransportStage l (Coefficient.{u} l Ω E) (inv (inv g)) hX hY :=
      fun E ↦ Classical.choice
        (isomorphismFieldTransportFiniteStage l (Coefficient.{u} l Ω E) (inv (inv g)) hX hY)
    have hSop (E L : Index l Ω) (h : E ≤ L) :=
      isomorphismFieldTransportRationalScalar l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) (inv (inv g)) hX hY
        (Sop E) (Sop L) (transport_scalarLaw l _ _ _ (inv (inv g)))
    exact isomorphismFieldTransportCommonStage l Ω (inv g) ⟨dY, hdY⟩ ⟨dX, hdX⟩
      hY hX R Sop hR hSop

end WeilConjectures
