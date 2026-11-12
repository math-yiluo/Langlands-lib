import Langlands.Geometry.Building.FullValidity.Assignment

/-! # Replacing supplied KP data through building equivalences -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace KPBuildingDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- A comparison of the reduced buildings of two data for the same group. Both
oriented affine-chart clauses are supplied, and equivariance uses the identity
on the actual rational-point group. No validity axiom is included. -/
structure BuildingEquivalence (D E : KPBuildingDatum G) where
  equiv : D.base.ReducedBuilding ≃ E.base.ReducedBuilding
  isBuildingIso : ValuationBuildingData.IsBuildingIso
    D.base.toValuationBuildingData E.base.toValuationBuildingData equiv
  isBuildingIso_symm : ValuationBuildingData.IsBuildingIso
    E.base.toValuationBuildingData D.base.toValuationBuildingData equiv.symm
  equivariant : ∀ (g : rationalPoints G) (y : D.base.ReducedBuilding),
    equiv (g • y) = g • equiv y

namespace BuildingEquivalence

variable {D E : KPBuildingDatum G}

/-- The identity comparison. -/
def refl (D : KPBuildingDatum G) : BuildingEquivalence D D where
  equiv := Equiv.refl _
  isBuildingIso := ValuationBuildingData.isBuildingIso_refl _
  isBuildingIso_symm := ValuationBuildingData.isBuildingIso_refl _
  equivariant _ _ := rfl

/-- Forward identity-equivariance. -/
theorem isEquivariant (e : BuildingEquivalence D E) :
    ValuationBuildingData.IsEquivariantBuildingIso
      D.base.toValuationBuildingData E.base.toValuationBuildingData
      (MonoidHom.id _) e.equiv :=
  ⟨e.isBuildingIso, e.equivariant⟩

/-- Inverse identity-equivariance follows by injectivity. -/
theorem isEquivariant_symm (e : BuildingEquivalence D E) :
    ValuationBuildingData.IsEquivariantBuildingIso
      E.base.toValuationBuildingData D.base.toValuationBuildingData
      (MonoidHom.id _) e.equiv.symm := by
  refine ⟨e.isBuildingIso_symm, fun g y => ?_⟩
  apply e.equiv.injective
  rw [e.equiv.apply_symm_apply, e.equivariant, e.equiv.apply_symm_apply]
  rfl

end BuildingEquivalence
end KPBuildingDatum

namespace KPBuildingAssignment

/-- Every comparison of the original assignment survives pointwise replacement
by group-valid data with an identity-equivariant building equivalence. -/
theorem isValid_of_buildingEquivalences (B B' : KPBuildingAssignment.{u})
    (hB : B.IsValid)
    (hgroup : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
      [IsAffineHom G.X.hom] (hG : IsConnectedReductive G),
        (B'.datum F G hG).SatisfiesGroupAxioms)
    (e : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
      [IsAffineHom G.X.hom] (hG : IsConnectedReductive G),
        KPBuildingDatum.BuildingEquivalence (B.datum F G hG) (B'.datum F G hG)) :
    B'.IsValid := by
  intro F _ _ _ _ G _ hG
  apply isAvailableFor_iff.mpr
  refine ⟨hgroup F G hG, ?_, ?_, ?_, ?_⟩
  · intro H _ hH f hf
    obtain ⟨Φ, hΦ⟩ := (hB F G hG).existenceOfBuilding.centralQuotients H hH f hf
    refine ⟨((e F G hG).equiv.symm.trans Φ).trans (e F H hH).equiv, ?_⟩
    simpa only [MonoidHom.id_comp, MonoidHom.comp_id] using
      ((e F G hG).isEquivariant_symm.trans hΦ).trans (e F H hH).isEquivariant
  · intro H _ hH d hd
    obtain ⟨Φ, hΦ⟩ := (hB F G hG).existenceOfBuilding.derivedSubgroups H hH d hd
    refine ⟨((e F H hH).equiv.symm.trans Φ).trans (e F G hG).equiv, ?_⟩
    simpa only [MonoidHom.id_comp, MonoidHom.comp_id] using
      ((e F H hH).isEquivariant_symm.trans hΦ).trans (e F G hG).isEquivariant
  · intro Gder H _ hH d π hπ
    obtain ⟨Φ, hΦ⟩ :=
      (hB F G hG).existenceOfBuilding.simplyConnectedCovers Gder H hH d π hπ
    refine ⟨((e F H hH).equiv.symm.trans Φ).trans (e F G hG).equiv, ?_⟩
    simpa only [MonoidHom.id_comp, MonoidHom.comp_id] using
      ((e F H hH).isEquivariant_symm.trans hΦ).trans (e F G hG).isEquivariant
  · intro F₂ _ _ _ _ σ hσ H _ hH f
    obtain ⟨Φ, hΦ⟩ := (hB F G hG).isomorphismCompatibility F₂ σ hσ H hH f
    refine ⟨((e F G hG).equiv.symm.trans Φ).trans (e F₂ H hH).equiv, ?_⟩
    simpa only [MonoidHom.id_comp, MonoidHom.comp_id] using
      ((e F G hG).isEquivariant_symm.trans hΦ).trans (e F₂ H hH).isEquivariant

/-- The complete input of a datum in a KP assignment, bundled so that a single
entry can be replaced by dependent function update. -/
structure DatumIndex where
  F : Type u
  field : Field F
  valuation : ValuativeRel F
  topology : TopologicalSpace F
  localField : @IsNonarchimedeanLocalField F field valuation topology
  G : GroupScheme (Spec (CommRingCat.of F))
  affine : IsAffineHom G.X.hom
  reductive : IsConnectedReductive G

attribute [instance] DatumIndex.field DatumIndex.valuation DatumIndex.topology
  DatumIndex.localField DatumIndex.affine

/-- Evaluate an assignment on the bundled input. -/
def datumAt (B : KPBuildingAssignment.{u}) (p : DatumIndex.{u}) : KPBuildingDatum p.G :=
  B.datum p.F p.G p.reductive

/-- An assignment from a dependent choice of data on bundled inputs. -/
def ofData (D : ∀ p : DatumIndex.{u}, KPBuildingDatum p.G) : KPBuildingAssignment.{u} where
  datum F _ _ _ _ G _ hG := D ⟨F, ‹Field F›, ‹ValuativeRel F›, ‹TopologicalSpace F›,
    ‹IsNonarchimedeanLocalField F›, G, ‹IsAffineHom G.X.hom›, hG⟩

/-- Replace exactly one bundled input, retaining the supplied data elsewhere. -/
def replaceDatum (B : KPBuildingAssignment.{u}) (p : DatumIndex.{u})
    (D : KPBuildingDatum p.G) : KPBuildingAssignment.{u} := by
  classical
  exact ofData (Function.update B.datumAt p D)

@[simp] theorem datumAt_ofData (D : ∀ p : DatumIndex.{u}, KPBuildingDatum p.G)
    (p : DatumIndex.{u}) : (ofData D).datumAt p = D p := by
  cases p
  rfl

@[simp] theorem datumAt_replaceDatum (B : KPBuildingAssignment.{u}) (p : DatumIndex.{u})
    (D : KPBuildingDatum p.G) : (B.replaceDatum p D).datumAt p = D := by
  classical
  simp [replaceDatum]

/-- Replacement retains every unequal bundled input. -/
theorem datumAt_replaceDatum_of_ne (B : KPBuildingAssignment.{u})
    (p q : DatumIndex.{u}) (D : KPBuildingDatum p.G) (h : q ≠ p) :
    (B.replaceDatum p D).datumAt q = B.datumAt q := by
  classical
  simp [replaceDatum, Function.update_of_ne h]

/-- A pointwise family of group-valid data and building equivalences determines
a fully valid assignment, including all cross-group comparisons. -/
theorem ofData_isValid (B : KPBuildingAssignment.{u}) (hB : B.IsValid)
    (D : ∀ p : DatumIndex.{u}, KPBuildingDatum p.G)
    (hgroup : ∀ p, (D p).SatisfiesGroupAxioms)
    (e : ∀ p, KPBuildingDatum.BuildingEquivalence (B.datumAt p) (D p)) :
    (ofData D).IsValid := by
  apply isValid_of_buildingEquivalences B _ hB
  · intro F _ _ _ _ G _ hG
    exact hgroup ⟨F, ‹Field F›, ‹ValuativeRel F›, ‹TopologicalSpace F›,
      ‹IsNonarchimedeanLocalField F›, G, ‹IsAffineHom G.X.hom›, hG⟩
  · intro F _ _ _ _ G _ hG
    exact e ⟨F, ‹Field F›, ‹ValuativeRel F›, ‹TopologicalSpace F›,
      ‹IsNonarchimedeanLocalField F›, G, ‹IsAffineHom G.X.hom›, hG⟩

/-- Replacing one datum preserves corrected KP validity when the new datum
satisfies all group axioms and its building is identity-equivariantly equivalent
to the old one in both geometric directions. -/
theorem replaceDatum_isValid (B : KPBuildingAssignment.{u}) (hB : B.IsValid)
    (p : DatumIndex.{u}) (D : KPBuildingDatum p.G) (hD : D.SatisfiesGroupAxioms)
    (e : KPBuildingDatum.BuildingEquivalence (B.datumAt p) D) :
    (B.replaceDatum p D).IsValid := by
  classical
  apply ofData_isValid B hB
  · intro q
    by_cases h : q = p
    · subst q
      simpa only [Function.update_self] using hD
    · simpa only [Function.update_of_ne h, datumAt] using (hB q.F q.G q.reductive).groupAxioms
  · intro q
    by_cases h : q = p
    · subst q
      simpa only [Function.update_self] using e
    · simpa only [Function.update_of_ne h] using
        KPBuildingDatum.BuildingEquivalence.refl (B.datumAt q)

end KPBuildingAssignment
end Langlands.Geometry.Building
