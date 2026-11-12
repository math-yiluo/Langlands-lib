import Langlands.ClassFieldTheory.Local.UpperReciprocityReduction
import Langlands.ClassFieldTheory.Local.NormUnitImageCardinality
import Langlands.LocalFactor.Ramification.Herbrand.TowerProof

/-! # From numerical norm filtrations to literal finite reciprocity images -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace Langlands.LocalClassField

universe u

/-- Numerical norm filtration in the base universe determines every finite
real unit image of a geometric reciprocity candidate. -/
theorem finiteReciprocityRealUnitImages_of_normCardinality
    (hnorm : FiniteAbelianNormUnitImageCardinality.{u,u}) :
    FiniteReciprocityRealUnitImages.{u} := by
  intro p hp F T
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  intro r hr L S
  letI : Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (Algebra F.Carrier L.field)
  letI : IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)
  letI : IsAbelianGalois F.Carrier L.field := ⟨⟩
  letI : IsAbelianGalois F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (IsAbelianGalois F.Carrier L.field)
  intro v hv
  let H : Subgroup L.galoisGroup :=
    Ramification.Padic.upperRamificationGroup S F.Carrier v
  let E0 : IntermediateField F.Carrier L.field := IntermediateField.fixedField H
  let E1 : IntermediateField F.Carrier (AlgebraicClosure F.Carrier) :=
    IntermediateField.lift E0
  letI : FiniteDimensional F.Carrier E1 :=
    Module.Finite.equiv (IntermediateField.liftAlgEquiv E0).toLinearEquiv
  letI : IsAbelianGalois F.Carrier E1 :=
    IsAbelianGalois.of_algHom (IntermediateField.liftAlgEquiv E0).symm.toAlgHom
  let E : LocalFiniteAbelianExtension F :=
    ⟨{ toIntermediateField := E1 }, inferInstanceAs (IsMulCommutative Gal(E1/F.Carrier))⟩
  have hEL : E.field ≤ L.field := IntermediateField.lift_le E0
  letI : Algebra E.field L.field := (Subsemiring.inclusion hEL).toAlgebra
  letI : IsScalarTower F.Carrier E.field L.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra F.Carrier (E.asPadicField (p := p)).Carrier :=
    inferInstanceAs (Algebra F.Carrier E.field)
  letI : Algebra (E.asPadicField (p := p)).Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (Algebra E.field L.field)
  letI : IsScalarTower (Padic p) F.Carrier (E.asPadicField (p := p)).Carrier :=
    inferInstanceAs (IsScalarTower (Padic p) F.Carrier E.field)
  letI : IsScalarTower F.Carrier (E.asPadicField (p := p)).Carrier
      (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (IsScalarTower F.Carrier E.field L.field)
  letI : IsAbelianGalois F.Carrier (E.asPadicField (p := p)).Carrier :=
    inferInstanceAs (IsAbelianGalois F.Carrier E1)
  letI : IsGalois (E.asPadicField (p := p)).Carrier (L.asPadicField (p := p)).Carrier :=
    IsGalois.tower_top_of_isGalois F.Carrier
      (E.asPadicField (p := p)).Carrier (L.asPadicField (p := p)).Carrier
  let R := (E.asPadicField (p := p)).canonicalTopologicalData
  have hker : (E.restrictionOfLE L hEL).toMonoidHom.ker = H := by
    ext σ
    rw [MonoidHom.mem_ker]
    constructor
    · intro hσ
      have hfix : σ ∈ E0.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        have h := AlgEquiv.restrictNormal_commutes σ E.field
          ⟨x.1, (IntermediateField.mem_lift x).mpr hx⟩
        change (E.restrictionOfLE L hEL) σ = 1 at hσ
        change algebraMap E.field L.field (((E.restrictionOfLE L hEL) σ)
          ⟨x.1, (IntermediateField.mem_lift x).mpr hx⟩) = _ at h
        rw [hσ] at h
        exact h.symm
      rwa [IntermediateField.fixingSubgroup_fixedField] at hfix
    · intro hσ
      apply AlgEquiv.ext
      intro x
      apply (algebraMap E.field L.field).injective
      have h := AlgEquiv.restrictNormal_commutes σ E.field x
      have hx : (algebraMap E.field L.field x) ∈ E0 := by
        exact (IntermediateField.mem_lift
          (algebraMap E.field L.field x)).mp x.2
      have hfix : σ ∈ E0.fixingSubgroup := by
        rwa [IntermediateField.fixingSubgroup_fixedField]
      rw [(IntermediateField.mem_fixingSubgroup_iff E0 σ).mp hfix _ hx] at h
      exact h
  have hupperE : Ramification.Padic.upperRamificationGroup R F.Carrier v = ⊥ := by
    have hmap := Ramification.HerbrandBridge.upperRestrictionCompatibility F
      (L.asPadicField (p := p)) (E.asPadicField (p := p)) S R v (by linarith)
    change H.map (E.restrictionOfLE L hEL).toMonoidHom = _ at hmap
    rw [← hmap, Subgroup.map_eq_bot_iff, hker]
  have hunitE : T.unitFiltration ⌈v⌉₊ ≤ normSubgroup F.Carrier E.field := by
    have hc := hnorm p F (E.asPadicField (p := p)) T R v hv
    rw [hupperE, Subgroup.card_bot] at hc
    have hbot := Subgroup.eq_bot_of_card_eq _ hc
    rw [Subgroup.map_eq_bot_iff] at hbot
    change T.unitFiltration ⌈v⌉₊ ≤
      (QuotientGroup.mk' (normSubgroup F.Carrier E.field)).ker at hbot
    rwa [QuotientGroup.ker_mk'] at hbot
  have hle : (T.unitFiltration ⌈v⌉₊).map (finiteFamilyOfHom r L).toMonoidHom ≤ H := by
    rintro σ ⟨a, ha, rfl⟩
    rw [← hker, MonoidHom.mem_ker]
    have haE : (finiteFamilyOfHom r E) a = 1 := by
      change a ∈ (finiteFamilyOfHom r E).toMonoidHom.ker
      rw [(hr.1.2.1 E).1]
      exact hunitE ha
    have hcompat := DFunLike.congr_fun (hr.1.2.2 E L hEL) a
    exact hcompat.trans haE
  apply Subgroup.eq_of_le_of_card_ge hle
  let e := finiteNormResidueEquiv L (finiteFamilyOfHom r L) (hr.1.2.1 L)
  have he : e.toMonoidHom.comp (normQuotientProjection F.Carrier L.field) =
      (finiteFamilyOfHom r L).toMonoidHom := by
    ext a
    rfl
  have hc : Nat.card ((T.unitFiltration ⌈v⌉₊).map
      (finiteFamilyOfHom r L).toMonoidHom) = Nat.card H := by
    calc
      _ = Nat.card (((T.unitFiltration ⌈v⌉₊).map
          (normQuotientProjection F.Carrier L.field)).map e.toMonoidHom) := by
        rw [Subgroup.map_map, he]
      _ = Nat.card ((T.unitFiltration ⌈v⌉₊).map
          (normQuotientProjection F.Carrier L.field)) :=
        Subgroup.card_map_of_injective e.injective
      _ = Nat.card H := hnorm p F (L.asPadicField (p := p)) T S v hv
  exact hc.ge

/-- All finite upper reciprocity conclusions reduce to numerical norm
filtration, without assuming any reciprocity candidate as input. -/
theorem finiteUpperReciprocityTheorems_of_normCardinality
    (hnorm : FiniteAbelianNormUnitImageCardinality.{u,u}) :
    FiniteUpperReciprocityTheorems.{u} :=
  finiteUpperReciprocityTheorems_of_realImages
    (finiteReciprocityRealUnitImages_of_normCardinality hnorm)

end Langlands.LocalClassField
