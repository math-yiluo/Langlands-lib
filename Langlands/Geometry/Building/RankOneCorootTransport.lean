import Langlands.Geometry.Building.QuasiSplitValuedRankOneCoordinates
import Langlands.Geometry.Building.RankOneComponentComparison
import Langlands.GroupScheme.SpecialLinearBinaryOppositeCommutator
import Langlands.GroupScheme.Examples.SU3RootOppositeBigCell
import Langlands.GroupScheme.Rational.RootSubgroupMultipleInclusion

/-! # Transport of rank-one coroot parameters to the actual centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
  {B : MaximalUnramified.BuildingData F H} {hZ : IsTorus B.centralizer.Z}
  {b : characterLattice B.S}

namespace ValuedSL2RootCoordinates

variable (C : ValuedSL2RootCoordinates B hZ b)

/-- The actual centralizer point obtained from an extension-field unit. -/
def corootPoint : C.extensionˣ →* rationalPoints B.centralizer.Z :=
  (rationalPoints.map C.coroot).comp
    (WeilGm.rationalUnitsEquiv (UnramifiedClosure F) C.extension).symm.toMonoidHom

theorem map_corootPoint (t : C.extensionˣ) :
    rationalPoints.map B.centralizer.j (C.corootPoint t) =
      C.rho (SpecialLinear.Root.contractingMatrix
        (zero_ne_one : (0 : Fin 2) ≠ 1) t) :=
  C.coroot_points t

/-- The matrix factorization maps to an actual root/centralizer/root factorization. -/
theorem commutator_factorization (p q : C.extension)
    (ht : SpecialLinear.BinaryRoot.oppositeProductPivot p q ≠ 0) :
    (C.negative.equiv (Multiplicative.ofAdd q) : rationalPoints H)⁻¹ *
        (C.positive.equiv (Multiplicative.ofAdd p) : rationalPoints H) *
        (C.negative.equiv (Multiplicative.ofAdd q) : rationalPoints H) *
        (C.positive.equiv (Multiplicative.ofAdd p) : rationalPoints H)⁻¹ =
      (C.negative.equiv (Multiplicative.ofAdd
        (q / SpecialLinear.BinaryRoot.oppositeProductPivot p q - q)) : rationalPoints H) *
        rationalPoints.map B.centralizer.j
          (C.corootPoint (Units.mk0 (SpecialLinear.BinaryRoot.oppositeProductPivot p q) ht)) *
        (C.positive.equiv (Multiplicative.ofAdd
          (p / SpecialLinear.BinaryRoot.oppositeProductPivot p q - p)) : rationalPoints H) := by
  have h := congrArg C.rho
    (SpecialLinear.BinaryRoot.oppositeCommutator_factorization p q ht)
  simpa only [map_mul, map_inv, C.rho_upper, C.rho_lower, C.map_corootPoint] using h

/-- Any supplied factorization has the coroot parameter of the explicit SL2 calculation. -/
theorem exists_corootPoint_of_factorization (hb : b ≠ 0)
    (x : B.Apartment) (u u' : rationalPoints H)
    (hu : u ∈ B.rootGroup b) (hu' : u' ∈ B.rootGroup (-b))
    (r : ℝ) (hr : 0 < r)
    (hdepth : x.val b u + x.val (-b) u' = (r : WithTop ℝ))
    (v' v : rationalPoints H) (z : rationalPoints B.centralizer.Z)
    (hv' : v' ∈ B.rootGroup (-b)) (hv : v ∈ B.rootGroup b)
    (hfactor : u'⁻¹ * u * u' * u⁻¹ =
      v' * rationalPoints.map B.centralizer.j z * v) :
    ∃ t : C.extensionˣ, C.corootPoint t = z ∧
      Langlands.FieldTheory.henselianSeparableAddValuation (MaximalUnramified.valuation F)
        (MaximalUnramified.valuationSubring_isHenselian F) C.extension ((t : C.extension) - 1) =
          (r : WithTop ℝ) := by
  obtain ⟨p, hp⟩ := C.positive.equiv.surjective ⟨u, hu⟩
  obtain ⟨q, hq⟩ := C.negative.equiv.surjective ⟨u', hu'⟩
  have hp' : (C.positive.equiv p : rationalPoints H) = u := congrArg Subtype.val hp
  have hq' : (C.negative.equiv q : rationalPoints H) = u' := congrArg Subtype.val hq
  let omega := Langlands.FieldTheory.henselianSeparableAddValuation
    (MaximalUnramified.valuation F) (MaximalUnramified.valuationSubring_isHenselian F)
      C.extension
  have hvalue : omega p.toAdd + omega q.toAdd = (r : WithTop ℝ) := by
    rw [← C.depth_positive p.toAdd, ← C.depth_negative q.toAdd,
      ofAdd_toAdd, ofAdd_toAdd, hp', hq']
    exact (KPApartmentData.opposite_value_sum_eq B.i B.apartment C.origin x b u u').trans
      hdepth
  let ht := SpecialLinear.BinaryRoot.oppositeProductPivot_ne_zero_of_value_sum
    omega p.toAdd q.toAdd r hr hvalue
  let t := Units.mk0 (SpecialLinear.BinaryRoot.oppositeProductPivot p.toAdd q.toAdd) ht
  refine ⟨t, ?_, ?_⟩
  · apply (centralizerComponent_eq_of_root_factorizations B.i
      B.isMaximalSplitTorus.1.1 B.centralizer hb
      (C.negative.equiv _).property (C.positive.equiv _).property hv' hv)
    exact (C.commutator_factorization p.toAdd q.toAdd ht).symm.trans
      (by simpa only [ofAdd_toAdd, hp', hq'] using hfactor)
  · exact (SpecialLinear.BinaryRoot.value_oppositeProductPivot_sub_one
      omega p.toAdd q.toAdd).trans hvalue

end ValuedSL2RootCoordinates

namespace ValuedSU3RootCoordinates

variable (C : ValuedSU3RootCoordinates B hZ b)

/-- The actual centralizer point obtained from a quadratic-extension unit. -/
def corootPoint : C.extensionˣ →* rationalPoints B.centralizer.Z :=
  (rationalPoints.map C.coroot).comp
    (WeilGm.rationalUnitsEquiv (UnramifiedClosure F) C.extension).symm.toMonoidHom

theorem map_corootPoint (t : C.extensionˣ) :
    rationalPoints.map B.centralizer.j (C.corootPoint t) =
      C.rho ⟨SU3Root.diagonal (SU3Root.fieldInvolution C.base C.extension) t,
        SU3Root.diagonal_mem_specialUnitarySubgroup
          (SU3Root.fieldInvolution C.base C.extension) t⟩ :=
  C.coroot_points t

/-- The actual unitary matrix factorization maps into the ambient group. -/
theorem commutator_factorization (p q : SU3Root.rationalParameters C.base C.extension)
    (ht : SU3Root.oppositeProductPivot p q ≠ 0) :
    (C.negative.equiv q : rationalPoints H)⁻¹ *
        (C.positive.equiv p : rationalPoints H) *
        (C.negative.equiv q : rationalPoints H) *
        (C.positive.equiv p : rationalPoints H)⁻¹ =
      (C.negative.equiv (q⁻¹ * SU3Root.oppositeProductLower p q ht) : rationalPoints H) *
        rationalPoints.map B.centralizer.j
          (C.corootPoint (Units.mk0 (SU3Root.oppositeProductPivot p q) ht)) *
        (C.positive.equiv (SU3Root.oppositeProductUpper p q ht * p⁻¹) : rationalPoints H) := by
  let c := SU3Root.fieldInvolution C.base C.extension
  let upper (p : SU3Root.rationalParameters C.base C.extension) :
      SU3Root.specialUnitarySubgroup c :=
    ⟨SU3Root.Parameters.embedding c p, SU3Root.embedding_mem_specialUnitarySubgroup c p⟩
  let lower (p : SU3Root.rationalParameters C.base C.extension) :
      SU3Root.specialUnitarySubgroup c :=
    ⟨SU3Root.oppositeEmbedding c p, SU3Root.oppositeEmbedding_mem_specialUnitarySubgroup c p⟩
  let diag (t : C.extensionˣ) : SU3Root.specialUnitarySubgroup c :=
    ⟨SU3Root.diagonal c t, SU3Root.diagonal_mem_specialUnitarySubgroup c t⟩
  have heq : (lower q)⁻¹ * upper p * lower q * (upper p)⁻¹ =
      lower (q⁻¹ * SU3Root.oppositeProductLower p q ht) *
        diag (Units.mk0 (SU3Root.oppositeProductPivot p q) ht) *
        upper (SU3Root.oppositeProductUpper p q ht * p⁻¹) := by
    apply Subtype.ext
    exact SU3Root.oppositeCommutator_factorization p q ht
  have h := congrArg C.rho heq
  have hu (p : SU3Root.rationalParameters C.base C.extension) :
      C.rho (upper p) = (C.positive.equiv p : rationalPoints H) := C.rho_upper p
  have hl (p : SU3Root.rationalParameters C.base C.extension) :
      C.rho (lower p) = (C.negative.equiv p : rationalPoints H) := C.rho_lower p
  have hd (t : C.extensionˣ) :
      C.rho (diag t) = rationalPoints.map B.centralizer.j (C.corootPoint t) :=
    (C.map_corootPoint t).symm
  simpa only [map_mul, map_inv, hu, hl, hd] using h

/-- At an ordinary unitary root, any centralizer component has at least the
positive sum of the two supplied root depths. -/
theorem exists_corootPoint_of_factorization (hb : b ≠ 0)
    (x : B.Apartment) (u u' : rationalPoints H)
    (hu : u ∈ B.rootGroup b) (hu' : u' ∈ B.rootGroup (-b))
    (r : ℝ) (hr : 0 < r)
    (hdepth : x.val b u + x.val (-b) u' = (r : WithTop ℝ))
    (v' v : rationalPoints H) (z : rationalPoints B.centralizer.Z)
    (hv' : v' ∈ B.rootGroup (-b)) (hv : v ∈ B.rootGroup b)
    (hfactor : u'⁻¹ * u * u' * u⁻¹ =
      v' * rationalPoints.map B.centralizer.j z * v) :
    ∃ t : C.extensionˣ, C.corootPoint t = z ∧
      (r : WithTop ℝ) ≤
        Langlands.FieldTheory.henselianSeparableAddValuation (MaximalUnramified.valuation F)
          (MaximalUnramified.valuationSubring_isHenselian F) C.extension ((t : C.extension) - 1) := by
  obtain ⟨p, hp⟩ := C.positive.equiv.surjective ⟨u, hu⟩
  obtain ⟨q, hq⟩ := C.negative.equiv.surjective ⟨u', hu'⟩
  have hp' : (C.positive.equiv p : rationalPoints H) = u := congrArg Subtype.val hp
  have hq' : (C.negative.equiv q : rationalPoints H) = u' := congrArg Subtype.val hq
  let omega := Langlands.FieldTheory.henselianSeparableAddValuation
    (MaximalUnramified.valuation F) (MaximalUnramified.valuationSubring_isHenselian F)
      C.extension
  have hvalue : SU3Root.Parameters.depthA omega p + SU3Root.Parameters.depthA omega q =
      (r : WithTop ℝ) := by
    change SU3Root.towerDepth (UnramifiedClosure F) C.base C.extension
      (MaximalUnramified.valuation F) (MaximalUnramified.valuationSubring_isHenselian F) p +
      SU3Root.towerDepth (UnramifiedClosure F) C.base C.extension
        (MaximalUnramified.valuation F) (MaximalUnramified.valuationSubring_isHenselian F) q = _
    rw [← C.depth_positive p, ← C.depth_negative q, hp', hq']
    exact (KPApartmentData.opposite_value_sum_eq B.i B.apartment C.origin x b u u').trans
      hdepth
  have hinv : ∀ z, omega ((SU3Root.fieldInvolution C.base C.extension).bar z) = omega z :=
    SU3Root.henselianSeparableAddValuation_quadratic_bar
      (UnramifiedClosure F) C.base C.extension (MaximalUnramified.valuation F)
      (MaximalUnramified.valuationSubring_isHenselian F)
  cases hpd : SU3Root.Parameters.depthA omega p using WithTop.recTopCoe with
  | top => simp only [hpd, top_add, WithTop.top_ne_coe] at hvalue
  | coe s =>
    cases hqd : SU3Root.Parameters.depthA omega q using WithTop.recTopCoe with
    | top => simp only [hqd, add_top, WithTop.top_ne_coe] at hvalue
    | coe t =>
      have hsum : s + t = r := by
        rw [hpd, hqd, ← WithTop.coe_add] at hvalue
        exact WithTop.coe_injective hvalue
      let ht := SU3Root.oppositeProductPivot_ne_zero_of_depth_bounds
        omega hinv p q s t (hsum.symm ▸ hr) hpd.symm.le hqd.symm.le
      let unit := Units.mk0 (SU3Root.oppositeProductPivot p q) ht
      refine ⟨unit, ?_, ?_⟩
      · apply (centralizerComponent_eq_of_root_factorizations B.i
          B.isMaximalSplitTorus.1.1 B.centralizer hb
          (C.negative.equiv _).property (C.positive.equiv _).property hv' hv)
        exact (C.commutator_factorization p q ht).symm.trans
          (by simpa only [hp', hq'] using hfactor)
      · have h := SU3Root.value_oppositeProductPivot_sub_one_ge omega hinv p q s t
          (hsum.symm ▸ hr.le) hpd.symm.le hqd.symm.le
        change (r : WithTop ℝ) ≤ omega (SU3Root.oppositeProductPivot p q - 1)
        exact hsum ▸ h

/-- At the doubled unitary root, the literal central-coordinate depths give the
exact value of the induced-torus parameter. -/
theorem exists_corootPoint_of_double_factorization (hb : b ≠ 0)
    (x : B.Apartment) (u u' : rationalPoints H)
    (hu : u ∈ B.rootGroup (2 • b)) (hu' : u' ∈ B.rootGroup (-(2 • b)))
    (r : ℝ) (hr : 0 < r)
    (hdepth : x.val (2 • b) u + x.val (-(2 • b)) u' = (r : WithTop ℝ))
    (v' v : rationalPoints H) (z : rationalPoints B.centralizer.Z)
    (hv' : v' ∈ B.rootGroup (-(2 • b))) (hv : v ∈ B.rootGroup (2 • b))
    (hfactor : u'⁻¹ * u * u' * u⁻¹ =
      v' * rationalPoints.map B.centralizer.j z * v) :
    ∃ t : C.extensionˣ, C.corootPoint t = z ∧
      Langlands.FieldTheory.henselianSeparableAddValuation (MaximalUnramified.valuation F)
        (MaximalUnramified.valuationSubring_isHenselian F) C.extension ((t : C.extension) - 1) =
          (r : WithTop ℝ) := by
  obtain ⟨p, hpc, hp⟩ := (C.positive.double u).mp hu
  obtain ⟨q, hqc, hq⟩ := (C.negative.double u').mp (by simpa only [smul_neg] using hu')
  let omega := Langlands.FieldTheory.henselianSeparableAddValuation
    (MaximalUnramified.valuation F) (MaximalUnramified.valuationSubring_isHenselian F)
      C.extension
  have hvalue : omega p.second + omega q.second = (r : WithTop ℝ) := by
    change SU3Root.towerCentralDepth (UnramifiedClosure F) C.base C.extension
      (MaximalUnramified.valuation F) (MaximalUnramified.valuationSubring_isHenselian F) ⟨p, hpc⟩ +
      SU3Root.towerCentralDepth (UnramifiedClosure F) C.base C.extension
        (MaximalUnramified.valuation F) (MaximalUnramified.valuationSubring_isHenselian F)
        ⟨q, hqc⟩ = _
    rw [← C.depth_double_positive ⟨p, hpc⟩, ← C.depth_double_negative ⟨q, hqc⟩]
    simp only [smul_neg, hp, hq]
    exact (KPApartmentData.opposite_value_sum_eq B.i B.apartment C.origin x (2 • b) u u').trans
      hdepth
  have hdeviation : omega (SU3Root.oppositeProductPivot p q - 1) = (r : WithTop ℝ) := by
    rw [SU3Root.oppositeProductPivot_sub_one_of_double p q (Or.inl hpc), omega.map_mul]
    exact hvalue
  have ht : SU3Root.oppositeProductPivot p q ≠ 0 := by
    intro hzero
    rw [hzero, zero_sub, omega.map_neg, omega.map_one] at hdeviation
    have he : (0 : ℝ) = r := WithTop.coe_injective hdeviation
    linarith
  let t := Units.mk0 (SU3Root.oppositeProductPivot p q) ht
  refine ⟨t, ?_, hdeviation⟩
  have hvb : v ∈ B.rootGroup b :=
    RelativeRoot.double_subgroup_le B.i b (Over.mk (𝟙 _)) hv
  have hv2' : v' ∈ B.rootGroup (2 • (-b)) := by
    simpa only [smul_neg] using hv'
  have hvb' : v' ∈ B.rootGroup (-b) :=
    RelativeRoot.double_subgroup_le B.i (-b) (Over.mk (𝟙 _)) hv2'
  apply (centralizerComponent_eq_of_root_factorizations B.i
    B.isMaximalSplitTorus.1.1 B.centralizer hb
    (C.negative.equiv _).property (C.positive.equiv _).property hvb' hvb)
  exact (C.commutator_factorization p q ht).symm.trans
    (by simpa only [hp, hq] using hfactor)

end ValuedSU3RootCoordinates

end Langlands.Geometry.Building
