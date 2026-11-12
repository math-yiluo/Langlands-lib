import Langlands.ClassFieldTheory.Local.ProfiniteReciprocityExistenceProof
import Langlands.ClassFieldTheory.Local.ProfiniteReciprocityCompletionProof
import Langlands.ClassFieldTheory.Local.WeilReciprocityUniquenessProof
import Langlands.Correspondence.BaseGeometricResidue
import Langlands.ClassFieldTheory.Local.UnitFiltrationStructuralProof
import Langlands.ClassFieldTheory.Local.WeilReciprocityExistenceAssembly

/-! # Existence of actual geometric local Weil reciprocity -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.LocalClassField

universe u

namespace WeilReciprocityExistence

open IsLocalRing Weil.Local ReciprocitySystemUniqueness
open Langlands.ClassFieldTheory.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

local instance : NontriviallyNormedField F.Carrier := F.canonicalNormedField
local instance : NormedAlgebra (Padic p) F.Carrier := F.canonicalNormedAlgebra
local instance : IsUltrametricDist F.Carrier :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := Padic p) (L := F.Carrier))
local instance : ProperSpace F.Carrier := FiniteDimensional.proper (Padic p) F.Carrier

set_option maxHeartbeats 600000 in
theorem restriction_congruence_of_residue_eq (L : LocalFiniteAbelianExtension F)
    (S : (L.asPadicField (p := p)).TopologicalData)
    (σ τ : Field.absoluteGaloisGroup F.Carrier)
    (h : localResidueMap F σ = localResidueMap F τ)
    (x : L.field) (hx : S.discreteValuation x ≤ 1) :
    S.discreteValuation (L.restriction σ x - L.restriction τ x) < 1 := by
  let : Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (Algebra F.Carrier L.field)
  let : IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)
  let : FiniteDimensional F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (FiniteDimensional F.Carrier L.field)
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := LocalGalois.localNormedField F.Carrier
  let := LocalGalois.localNormedField_ultrametric F.Carrier
  let := LocalGalois.localNormedField_complete F.Carrier
  let e := Correspondence.GeometricResidue.finiteSpectralIntegerEquiv F
    (L.asPadicField (p := p)) S
  let xS : S.Integers := ⟨x, S.mem_integers_iff_discreteValuation_le_one x |>.mpr hx⟩
  let z := e.symm xS
  let j : ResidueField (LocalGalois.extensionIntegers F.Carrier L.field) →+*
      AlgebraicClosure (localResidueField F) :=
    (LocalGalois.localResidueClosureEquiv F.Carrier).toRingHom.comp
      (LocalGalois.residueInclusion F.Carrier (AlgebraicClosure F.Carrier)
        L.field.toIntermediateField).toRingHom
  have hr :
      LocalGalois.residueHom F.Carrier L.field (L.restriction σ) (residue _ z) =
      LocalGalois.residueHom F.Carrier L.field (L.restriction τ) (residue _ z) := by
    apply j.injective
    have hs := LocalGalois.absoluteResidueHom_restrict
      F.Carrier L.field.toIntermediateField σ (residue _ z)
    have ht := LocalGalois.absoluteResidueHom_restrict
      F.Carrier L.field.toIntermediateField τ (residue _ z)
    change AlgEquiv.toAlgHom (localResidueMap F σ) (j (residue _ z)) =
      j (LocalGalois.residueHom F.Carrier L.field (L.restriction σ) (residue _ z)) at hs
    change AlgEquiv.toAlgHom (localResidueMap F τ) (j (residue _ z)) =
      j (LocalGalois.residueHom F.Carrier L.field (L.restriction τ) (residue _ z)) at ht
    exact hs.symm.trans
      ((congrArg (fun g => AlgEquiv.toAlgHom g (j (residue _ z))) h).trans ht)
  have he := congrArg (ResidueField.mapEquiv e) hr
  exact (NYLL.suppliedResidueCongruence (L.asPadicField (p := p)) S _ _).mp he

theorem restriction_eq_of_residue_eq (L : LocalFiniteAbelianExtension F)
    (hL : F.canonicalTopologicalData.ramificationIndex =
      (L.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex)
    (σ τ : Field.absoluteGaloisGroup F.Carrier)
    (h : localResidueMap F σ = localResidueMap F τ) :
    L.restriction σ = L.restriction τ := by
  let : Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (Algebra F.Carrier L.field)
  let : IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)
  let : FiniteDimensional F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (FiniteDimensional F.Carrier L.field)
  let : IsGalois F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (IsGalois F.Carrier L.field)
  apply ArithmeticCoordinate.residueHom_injective F (L.asPadicField (p := p)) hL
  ext y
  obtain ⟨x, rfl⟩ := residue_surjective y
  let ec := ArithmeticCoordinate.extensionIntegerEquiv F (L.asPadicField (p := p))
  apply (ResidueField.mapEquiv ec).injective
  apply (NYLL.suppliedResidueCongruence (L.asPadicField (p := p))
    (L.asPadicField (p := p)).canonicalTopologicalData _ _).mpr
  exact restriction_congruence_of_residue_eq F L _ σ τ h x.val
    (FiniteArtinSystemUniqueness.discreteValuation_le_one _ _ (ec x))

theorem restriction_projection (L : LocalFiniteAbelianExtension F)
    (hL : F.canonicalTopologicalData.ramificationIndex =
      (L.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex)
    (w : localWeilGroup F) :
    L.restriction (localProjection F w) =
      L.restriction (localProjection F (localGeometricFrobenius F)) ^
        localDegreeInt F w := by
  rw [← map_zpow, ← map_zpow]
  apply restriction_eq_of_residue_eq F L hL
  simp only [map_zpow]
  rw [localGeometricFrobenius_residue, localResidueMap_projection]

theorem geometric_coordinate_projection (L : LocalFiniteAbelianExtension F)
    (hL : F.canonicalTopologicalData.ramificationIndex =
      (L.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex)
    {N : ℕ} [NeZero N]
    (χ : L.galoisGroup ≃* Multiplicative (ZMod N))
    (hχ : IsArithmeticUnramifiedCoordinate F L.field χ)
    (w : localWeilGroup F) :
    (χ (L.restriction (localProjection F w)))⁻¹ =
      Multiplicative.ofAdd ((localDegreeInt F w : ℤ) : ZMod N) := by
  let : Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (Algebra F.Carrier L.field)
  let : IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)
  let : FiniteDimensional F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (FiniteDimensional F.Carrier L.field)
  have hΦ := FiniteArtinSystemUniqueness.inverse_coordinate_eq_one F
    (L.asPadicField (p := p)) F.canonicalTopologicalData χ hχ
    (L.restriction (localProjection F (localGeometricFrobenius F)))
    (Correspondence.GeometricResidue.finite_inverse_power_congruence F L
      (L.asPadicField (p := p)).canonicalTopologicalData _
      (localGeometricFrobenius_residue F))
  rw [restriction_projection F L hL, map_zpow, ← inv_zpow]
  erw [hΦ]
  change Multiplicative.ofAdd ((localDegreeInt F w) • (1 : ZMod N)) = _
  simp

theorem degreeMod_eq_coordinate (L : LocalFiniteAbelianExtension F)
    (hL : F.canonicalTopologicalData.ramificationIndex =
      (L.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex)
    {N : ℕ} [NeZero N]
    (χ : L.galoisGroup ≃* Multiplicative (ZMod N))
    (hχ : IsArithmeticUnramifiedCoordinate F L.field χ)
    (g : Field.absoluteGaloisGroupAbelianization F.Carrier) :
    WeilReciprocityUniqueness.degreeMod F N g =
      (χ (L.abelianRestriction g))⁻¹ := by
  induction g using QuotientGroup.induction_on with
  | H σ =>
    have he := (localProjection_denseRange F).equalizer
      ((profiniteIntegerMod N).continuous.comp (localResidueDegree F).continuous)
      ((continuous_of_discreteTopology (f := χ)).comp L.restriction.continuous |>.inv)
      (funext fun w => by
        change profiniteIntegerMod N (localResidueDegree F (localProjection F w)) = _
        rw [show localResidueDegree F (localProjection F w) =
          Weil.frobenius (localDegree F w) from w.property]
        exact (geometric_coordinate_projection F L hL χ hχ w).symm)
    exact congrFun he σ

theorem coordinate_reciprocity (T : F.TopologicalData)
    (r : letI := T.topology
      F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier)
    (hr : GeometricProfiniteReciprocityRelation F T r)
    (L : LocalFiniteAbelianExtension F) {N : ℕ} [NeZero N]
    (χ : L.galoisGroup ≃* Multiplicative (ZMod N))
    (hχ : IsArithmeticUnramifiedCoordinate F L.field χ)
    (a : F.Carrierˣ) :
    (χ (L.abelianRestriction (r a)))⁻¹ =
      Multiplicative.ofAdd ((T.ord (a : F.Carrier) : ℤ) : ZMod N) := by
  let : Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (Algebra F.Carrier L.field)
  let : IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)
  let : FiniteDimensional F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (FiniteDimensional F.Carrier L.field)
  let := T.topology
  let π := LocalFactor.PadicAbelian.uniformizerUnit T
  have hπ : T.ord (π : F.Carrier) = 1 :=
    LocalFactor.PadicAbelian.uniformizerUnit_ord T
  let c : Field.absoluteGaloisGroupAbelianization F.Carrier →* Multiplicative (ZMod N) :=
    { toFun g := (χ (L.abelianRestriction g))⁻¹
      map_one' := by simp
      map_mul' x y := by
        simp only [map_mul, mul_inv_rev]
        exact mul_comm _ _ }
  have hone (b : F.Carrierˣ) (hb : T.ord (b : F.Carrier) = 1) :
      c (r b) = Multiplicative.ofAdd 1 :=
    FiniteArtinSystemUniqueness.inverse_coordinate_eq_one F
      (L.asPadicField (p := p)) T χ hχ (finiteFamilyOfHom r L b)
      (hr.2 L (L.asPadicField (p := p)).canonicalTopologicalData b hb)
  let k : ℤ := 1 - T.ord (a : F.Carrier)
  have hak : T.ord ((a * π ^ k : F.Carrierˣ) : F.Carrier) = 1 := by
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val,
      T.ord_mul a.ne_zero (zpow_ne_zero k π.ne_zero), T.ord_zpow, hπ, mul_one]
    dsimp only [k]
    omega
  have hc := hone (a * π ^ k) hak
  rw [map_mul, map_zpow, map_mul, map_zpow, hone π hπ] at hc
  change c (r a) = _
  apply mul_right_cancel (b := (Multiplicative.ofAdd (1 : ZMod N)) ^ k)
  rw [hc]
  apply Multiplicative.ext
  simp only [toAdd_mul, toAdd_ofAdd, toAdd_zpow, zsmul_eq_mul, mul_one]
  dsimp only [k]
  push_cast
  ring

theorem degreeMod_reciprocity (T : F.TopologicalData)
    (r : letI := T.topology
      F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier)
    (hr : GeometricProfiniteReciprocityRelation F T r)
    (N : ℕ) [NeZero N] (a : F.Carrierˣ) :
    WeilReciprocityUniqueness.degreeMod F N (r a) =
      Multiplicative.ofAdd ((T.ord (a : F.Carrier) : ℤ) : ZMod N) := by
  obtain ⟨E, hGal, hE, hdeg⟩ :=
    unramifiedExtensionDegreeExistence p F N (NeZero.pos N)
  subst N
  let := hGal
  let E' := E.asPadicField (p := p)
  let : Algebra (Padic p) E'.Carrier := E'.algebra
  let : IsScalarTower (Padic p) F.Carrier E'.Carrier :=
    IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨χ, hχ⟩ := ArithmeticCoordinate.coordinate_exists F E' hE
  have hcomm : IsMulCommutative Gal(E.field/F.Carrier) := .of_comm fun s t => by
    apply χ.injective
    simp only [map_mul, mul_comm]
  let L : LocalFiniteAbelianExtension F := ⟨{ toIntermediateField := E.field }, hcomm⟩
  rw [degreeMod_eq_coordinate F L hE χ hχ]
  exact coordinate_reciprocity F T r hr L χ hχ a

theorem profiniteInteger_eq_one (x : Weil.ProfiniteIntegers)
    (hx : ∀ (N : ℕ) [NeZero N], profiniteIntegerMod N x = 1) : x = 1 := by
  apply Subtype.ext
  funext H
  let N := H.toSubgroup.index
  let : NeZero N := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hzero : x.val (degreeModSubgroup N) = 1 := by
    apply (QuotientGroup.injective_lift_iff (degreeModHom N).ker
      (degreeModHom N) (fun _ h => h)).mpr rfl
    exact (hx N).trans (map_one _).symm
  have hle : degreeModSubgroup N ≤ H := by
    intro m hm
    have hm' : (m.toAdd : ZMod N) = 0 := by
      exact congrArg Multiplicative.toAdd hm
    obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd m.toAdd N).mp hm'
    have hmem := H.toSubgroup.pow_index_mem (Multiplicative.ofAdd (1 : ℤ))
    have heq : m = ((Multiplicative.ofAdd (1 : ℤ)) ^ N) ^ t := by
      apply Multiplicative.ext
      simp [ht, mul_comm]
    rw [heq]
    exact H.toSubgroup.zpow_mem hmem t
  have hcompat := x.property (CategoryTheory.homOfLE hle)
  change x.val H = 1
  calc
    x.val H =
        (ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of Weil.Degree)).map
          (CategoryTheory.homOfLE hle) (x.val (degreeModSubgroup N)) := hcompat.symm
    _ = (ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of Weil.Degree)).map
          (CategoryTheory.homOfLE hle) 1 := congrArg _ hzero
    _ = 1 := map_one
      ((ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of Weil.Degree)).map
        (CategoryTheory.homOfLE hle)).hom

theorem profiniteInteger_ext (x y : Weil.ProfiniteIntegers)
    (h : ∀ (N : ℕ) [NeZero N], profiniteIntegerMod N x = profiniteIntegerMod N y) :
    x = y := by
  apply mul_inv_eq_one.mp
  apply profiniteInteger_eq_one
  intro N _
  rw [map_mul, map_inv, h N, mul_inv_cancel]

local instance : IsMulCommutative Weil.ProfiniteIntegers := .of_comm fun x y => by
  apply profiniteInteger_ext
  intro N _
  simp only [map_mul, mul_comm]

def galoisDegree :
    Field.absoluteGaloisGroupAbelianization F.Carrier →ₜ* Weil.ProfiniteIntegers :=
  abelianizationLift (localResidueDegree F)

theorem degreeMod_galoisDegree (N : ℕ) [NeZero N]
    (g : Field.absoluteGaloisGroupAbelianization F.Carrier) :
    profiniteIntegerMod N (galoisDegree F g) =
      WeilReciprocityUniqueness.degreeMod F N g := by
  induction g using QuotientGroup.induction_on with
  | H σ => rfl

theorem galoisDegree_reciprocity (T : F.TopologicalData)
    (r : letI := T.topology
      F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier)
    (hr : GeometricProfiniteReciprocityRelation F T r) (a : F.Carrierˣ) :
    galoisDegree F (r a) = Weil.frobenius (T.orderHom a) := by
  apply profiniteInteger_ext
  intro N _
  rw [degreeMod_galoisDegree, degreeMod_reciprocity F T r hr]
  rfl

theorem galoisDegree_toGroupAbelianization
    (w : WeilQuotients.Abelianization (localResidueDegree F)) :
    galoisDegree F (WeilQuotients.toGroupAbelianization (localResidueDegree F) w) =
      Weil.frobenius (WeilQuotients.degree (localResidueDegree F) w) := by
  induction w using QuotientGroup.induction_on with
  | H w => exact w.property

theorem inertia_in_reciprocity_range (T : F.TopologicalData)
    (r : letI := T.topology
      F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier)
    (hr : GeometricProfiniteReciprocityRelation F T r)
    (g : Field.absoluteGaloisGroupAbelianization F.Carrier)
    (hg : galoisDegree F g = 1) :
    ∃ a : F.Carrierˣ, a ∈ T.unitSubgroup ∧ r a = g := by
  let := T.topology
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  let : CompactSpace (Field.absoluteGaloisGroup F.Carrier) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure F.Carrier/F.Carrier))
  let := absoluteGaloisNonarchimedean F.Carrier
  let := abelianizationHausdorff (Field.absoluteGaloisGroup F.Carrier)
  let := quotientNonarchimedean
    (commutator (Field.absoluteGaloisGroup F.Carrier)).topologicalClosure
  have hcompact : IsCompact (r '' (T.unitSubgroup : Set F.Carrierˣ)) := by
    apply IsCompact.image _ r.continuous
    rw [← T.unitFiltration_zero]
    exact T.isCompact_unitFiltration 0
  have hcl : g ∈ closure (r '' (T.unitSubgroup : Set F.Carrierˣ)) := by
    apply mem_closure_iff_nhds_one.mpr
    intro V hV
    obtain ⟨H, hHV⟩ := NonarchimedeanGroup.is_nonarchimedean V hV
    let : DiscreteTopology
        (Field.absoluteGaloisGroupAbelianization F.Carrier ⧸ H.toSubgroup) :=
      QuotientGroup.discreteTopology_iff.mpr H.isOpen
    let : H.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    let N := H.toSubgroup.index
    let : NeZero N := ⟨Subgroup.index_ne_zero_of_finite⟩
    let C : Set (Field.absoluteGaloisGroupAbelianization F.Carrier) :=
      {z | z / g ∈ H ∧ WeilReciprocityUniqueness.degreeMod F N z = 1}
    have hC : IsOpen C :=
      (H.isOpen.preimage (continuous_id.div_const g)).inter
        (isOpen_discrete ({1} : Set (Multiplicative (ZMod N))) |>.preimage
          (WeilReciprocityUniqueness.degreeMod F N).continuous)
    have hgC : g ∈ C := by
      refine ⟨by simp, ?_⟩
      rw [← degreeMod_galoisDegree, hg, map_one]
    obtain ⟨a, ha⟩ := hr.1.1.exists_mem_open hC ⟨g, hgC⟩
    have hdiv : (N : ℤ) ∣ T.ord (a : F.Carrier) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      have he := ha.2
      rw [degreeMod_reciprocity F T r hr] at he
      exact congrArg Multiplicative.toAdd he
    let π := LocalFactor.PadicAbelian.uniformizerUnit T
    have hπ : T.ord (π : F.Carrier) = 1 :=
      LocalFactor.PadicAbelian.uniformizerUnit_ord T
    have hpH : r (π ^ T.ord (a : F.Carrier)) ∈ H := by
      obtain ⟨t, ht⟩ := hdiv
      rw [map_zpow, ht, zpow_mul, zpow_natCast]
      exact H.zpow_mem (H.toSubgroup.pow_index_mem (r π)) t
    let b := a / π ^ T.ord (a : F.Carrier)
    have hb : b ∈ T.unitSubgroup := by
      apply (mem_unitSubgroup_iff_ord_eq_zero F T b).mpr
      dsimp only [b]
      rw [Units.val_div_eq_div_val, div_eq_mul_inv,
        T.ord_mul a.ne_zero (inv_ne_zero (Units.ne_zero _)), T.ord_inv,
        Units.val_zpow_eq_zpow_val, T.ord_zpow, hπ, mul_one, add_neg_cancel]
    refine ⟨r b, ⟨b, hb, rfl⟩, hHV ?_⟩
    convert H.div_mem ha.1 hpH using 1
    simp [b, div_eq_mul_inv, mul_comm, mul_assoc]
  rw [hcompact.isClosed.closure_eq] at hcl
  rcases hcl with ⟨a, ha, he⟩
  exact ⟨a, ha, he⟩

theorem reciprocity_lifts_to_weil (T : F.TopologicalData)
    (r : letI := T.topology
      F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier)
    (hr : GeometricProfiniteReciprocityRelation F T r) (a : F.Carrierˣ) :
    ∃ w : WeilQuotients.Abelianization (localResidueDegree F),
      WeilQuotients.toGroupAbelianization (localResidueDegree F) w = r a ∧
        WeilQuotients.degree (localResidueDegree F) w = T.orderHom a := by
  have hd := galoisDegree_reciprocity F T r hr a
  generalize r a = g at hd ⊢
  induction g using QuotientGroup.induction_on with
  | H σ =>
    let w : localWeilGroup F := ⟨(σ, T.orderHom a), hd⟩
    exact ⟨WeilQuotients.projection (localResidueDegree F) w, rfl, rfl⟩

theorem weil_in_reciprocity_range (T : F.TopologicalData)
    (r : letI := T.topology
      F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier)
    (hr : GeometricProfiniteReciprocityRelation F T r)
    (w : WeilQuotients.Abelianization (localResidueDegree F)) :
    ∃ a : F.Carrierˣ,
      r a = WeilQuotients.toGroupAbelianization (localResidueDegree F) w ∧
        T.orderHom a = WeilQuotients.degree (localResidueDegree F) w := by
  let := T.topology
  let π := LocalFactor.PadicAbelian.uniformizerUnit T
  let n : ℤ := (WeilQuotients.degree (localResidueDegree F) w).toAdd
  have hπ : T.ord (π : F.Carrier) = 1 :=
    LocalFactor.PadicAbelian.uniformizerUnit_ord T
  have hpow : T.orderHom (π ^ n) =
      WeilQuotients.degree (localResidueDegree F) w := by
    apply Multiplicative.ext
    change T.ord ((π ^ n : F.Carrierˣ) : F.Carrier) = n
    rw [Units.val_zpow_eq_zpow_val, T.ord_zpow, hπ, mul_one]
  let g := WeilQuotients.toGroupAbelianization (localResidueDegree F) w / r (π ^ n)
  have hg : galoisDegree F g = 1 := by
    dsimp only [g]
    rw [map_div, galoisDegree_toGroupAbelianization,
      galoisDegree_reciprocity F T r hr, hpow, div_self']
  obtain ⟨b, hb, hbg⟩ := inertia_in_reciprocity_range F T r hr g hg
  refine ⟨b * π ^ n, ?_, ?_⟩
  · rw [map_mul, hbg]
    exact div_mul_cancel _ _
  · rw [map_mul, (T.mem_unitSubgroup_iff_orderHom b).mp hb, one_mul, hpow]

end WeilReciprocityExistence

/-- Actual geometric Weil reciprocity exists uniquely for every p-adic field
and every supplied topological realization, in every carrier universe. -/
theorem geometricWeilReciprocityExistenceUniqueness :
    WeilReciprocityExistenceUniqueness.{u} := by
  apply WeilReciprocityExistence.weilReciprocityExistenceUniqueness_of_range
  intro p _ F T
  let := T.topology
  intro r hr
  exact ⟨WeilReciprocityExistence.reciprocity_lifts_to_weil F T r hr,
    WeilReciprocityExistence.weil_in_reciprocity_range F T r hr⟩

end Langlands.LocalClassField
