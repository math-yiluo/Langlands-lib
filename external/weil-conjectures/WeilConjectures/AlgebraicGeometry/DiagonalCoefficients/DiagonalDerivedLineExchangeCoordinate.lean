/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientPullbackEndpoints
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientMaps
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Integral.DiagonalIntegralLineSplitMono
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Integral.DiagonalIntegralLinePullIso
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalSectionUnitSplitMono
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalUnitExchangeSplitMono
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalExchangeLineCoordinates

/-! # The degree-minus-two coordinate of integral-line exchange -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem transport_composite
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : C ⥤ D) {R R₀ : A ⥤ C} {S S₀ : B ⥤ D} (i : R ≅ R₀) (j : S ≅ S₀)
    {M : C} {N : A} {P Q : B} (u : M ⟶ R₀.obj N)
    (e : F.obj (R₀.obj N) ⟶ S₀.obj P) (d : P ⟶ Q) :
    F.map (u ≫ i.inv.app N) ≫
        (F.map (i.hom.app N) ≫ e ≫ j.inv.app P) ≫ S.map d =
      (F.map u ≫ e ≫ S₀.map d) ≫ j.inv.app Q := by
  simp only [F.map_comp, Category.assoc]
  rw [← F.map_comp_assoc (i.inv.app N), Iso.inv_hom_id_app,
    F.map_id, Category.id_comp]
  rw [← j.inv.naturality d]

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor CondensedRing.upperStar CondensedRing.lowerStar

/-- The actual integral Tate line in degree minus two.
(blueprint: lem-diagonal-derived-line-exchange-coordinate). -/
abbrev diagonalShiftedIntegralLine (l : ℕ) [Fact l.Prime] (S : Scheme.{u}) :=
  ((DerivedCategory.singleFunctor (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) S)
    0).obj (zlLine l S))⟦(2 : ℤ)⟧

private theorem lineShift_le (l : ℕ) [Fact l.Prime] (S : Scheme.{u}) :
    (diagonalShiftedIntegralLine l S).IsLE (-2) :=
  DerivedCategory.TStructure.t.isLE_shift _ 0 2 (-2) (by decide)

private theorem pull_line_iso (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)] :
    Nonempty ((derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).obj
      (diagonalShiftedIntegralLine l S) ≅ diagonalShiftedIntegralLine l X) := by
  obtain ⟨e⟩ := diagonalIntegralLine_pullIso l f
  exact ⟨((derivedUpper _ f).commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      (singlePullback _ f (zlLine l S) ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso e)⟩

-- Compare the independently normalized derived functor endpoints.
/-- For vertical morphisms admitting sections, exchange on integral Tate lines
has invertible first coordinate in every split unit/Chern decomposition.

Source: the unit component of diagonal coefficients (3)
(blueprint: lem-diagonal-derived-line-exchange-coordinate).

Proof: form the canonical twisted adjunction unit using an inverse-image
isomorphism of integral Tate lines. A section splits this unit. Its composite
with exchange is another split unit, by the mate identity, without any choice
of trivializations. Transport both along the prescribed canonical functor
equalities. Degree minus two to degree zero maps vanish by the standard
t-structure. The rank-one coordinate criterion therefore makes both the unit
coordinate and the exchange coordinate invertible. -/
theorem diagonalDerivedLineExchange_coordinate (l : ℕ) [Fact l.Prime]
    {X S X' S' : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)]
    [∀ x : X', Invertible (l : X'.residueField x)]
    [∀ x : S', Invertible (l : S'.residueField x)]
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
    (s' : S' ⟶ X') (hs' : s' ≫ f' = 𝟙 S')
    (D : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f))
    (D' : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f'))
    (canonical : D.R = derivedLower (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (canonical' : D'.R = derivedLower (Profinite.continuousMapRingObj.{u} ℤ_[l]) f')
    (line : PullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) hX
      (zlLine l X) (zlLine l X') (spIntegralComparison hX l (bottomField l)))
    (v : diagonalShiftedIntegralLine l S ⟶ D.R.obj (diagonalShiftedIntegralLine l X))
    (b : unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) S ⟶
      D.R.obj (diagonalShiftedIntegralLine l X))
    (v' : diagonalShiftedIntegralLine l S' ⟶ D'.R.obj (diagonalShiftedIntegralLine l X'))
    (b' : unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) S' ⟶
      D'.R.obj (diagonalShiftedIntegralLine l X'))
    [IsIso (biprod.desc v b)] [IsIso (biprod.desc v' b')]
    (τ : D.R.obj (diagonalShiftedIntegralLine l X) ⟶
      unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) S)
    (τ' : D'.R.obj (diagonalShiftedIntegralLine l X') ⟶
      unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) S')
    (hv : v ≫ τ = 0) (hb : b ≫ τ = 𝟙 _)
    (hv' : v' ≫ τ' = 0) (hb' : b' ≫ τ' = 𝟙 _) :
    IsIso ((derivedUpper _ hS).map v ≫
      modelExchange _ f f' hX hS h D D' canonical canonical' (diagonalShiftedIntegralLine l X) ≫
      D'.R.map line.shift ≫ inv (biprod.desc v' b') ≫ biprod.fst) := by
  let Λ := Profinite.continuousMapRingObj.{u} ℤ_[l]
  let F := derivedUpper Λ hS
  obtain ⟨e⟩ := pull_line_iso l f
  obtain ⟨i⟩ := pull_line_iso l hS
  let a := CondensedRing.derivedUpperStarLowerStarAdjunction Λ f
  let u₀ : diagonalShiftedIntegralLine l S ⟶
      (derivedLower Λ f).obj (diagonalShiftedIntegralLine l X) :=
    a.unit.app (diagonalShiftedIntegralLine l S) ≫ (derivedLower Λ f).map e.hom
  let u : diagonalShiftedIntegralLine l S ⟶
      D.R.obj (diagonalShiftedIntegralLine l X) :=
    u₀ ≫ (eqToIso canonical).inv.app (diagonalShiftedIntegralLine l X)
  have : IsSplitMono u₀ := diagonalSectionUnit_splitMono Λ f s hs _ _ e
  have : IsSplitMono u := inferInstance
  let E := modelExchange Λ f f' hX hS h D D' canonical canonical'
    (diagonalShiftedIntegralLine l X) ≫
    D'.R.map line.shift
  have : IsIso line.shift := by unfold PullEndpoint.shift PullEndpoint.derived; infer_instance
  let d := asIso line.shift
  have hs₀ := diagonalUnitExchange_splitMono Λ f f' hX hS h s' hs' _ _ _ e d
  let z := F.map u₀ ≫ (derivedExchange Λ f f' hX hS h).app (diagonalShiftedIntegralLine l X) ≫
    (derivedLower Λ f').map line.shift
  have : IsSplitMono z := hs₀
  have hz : F.map u ≫ E = z ≫ (eqToIso canonical').inv.app (diagonalShiftedIntegralLine l X') := by
    exact transport_composite F (eqToIso canonical) (eqToIso canonical') u₀
      ((derivedExchange Λ f f' hX hS h).app (diagonalShiftedIntegralLine l X)) line.shift
  have : IsSplitMono (F.map u ≫ E) := by rw [hz]; infer_instance
  have : (diagonalShiftedIntegralLine l S).IsLE (-2) := lineShift_le l S
  have hu : u ≫ τ = 0 := DerivedCategory.TStructure.t.zero _ (-2) 0 (by decide)
  have : (diagonalShiftedIntegralLine l S').IsLE (-2) := lineShift_le l S'
  have : (F.obj (diagonalShiftedIntegralLine l S)).IsLE (-2) :=
    DerivedCategory.TStructure.t.isLE_of_iso i.symm (-2)
  have hz' : F.map v ≫ E ≫ τ' = 0 :=
    DerivedCategory.TStructure.t.zero _ (-2) 0 (by decide)
  simpa only [E, Category.assoc] using
    exchangeLineCoordinate_isIso F v b v' b' τ τ' hv hb hv' hb' u hu E hz' i
      (fun q hq ↦ diagonalIntegralLine_splitMono_isIso l S q)
      (fun q hq ↦ diagonalIntegralLine_splitMono_isIso l S' q)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
