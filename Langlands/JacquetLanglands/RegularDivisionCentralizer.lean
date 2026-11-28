import Langlands.Algebra.DivisionFieldEmbeddingsProof
import Langlands.BaseChange.EllipticLocusClopen
import Langlands.BaseChange.RegularCentralizerCompact
import Langlands.BaseChange.RegularCoefficientSlice
import Langlands.JacquetLanglands.DivisionUnits
import Langlands.JacquetLanglands.RegularDivisionParameters

/-! # Polynomial centralizers and coefficient sections of regular division units -/

noncomputable section

namespace Langlands.JacquetLanglands

open Set Matrix _root_.Polynomial _root_.Topology
open Langlands.BaseChange Langlands.CentralSimple Langlands.TraceFormula
open Langlands.BaseChange.SigmaLiftCharacterIdentity (coefficients)

universe u

section Evaluation

variable {F R : Type*} [Field F] [Ring R] [Algebra F R]

/-- Evaluation in a possibly noncommutative algebra at a root of `p`. -/
private def rootEvaluation (p : F[X]) (a : R) (ha : aeval a p = 0) : AdjoinRoot p →ₐ[F] R :=
  Ideal.Quotient.liftₐ _ (aeval a) fun q hq => by
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hq
    rw [map_mul, ha, zero_mul]

@[simp] private theorem rootEvaluation_mk (p : F[X]) (a : R) (ha : aeval a p = 0) (q : F[X]) :
    rootEvaluation p a ha (AdjoinRoot.mk p q) = aeval a q := rfl

@[simp] private theorem rootEvaluation_root (p : F[X]) (a : R) (ha : aeval a p = 0) :
    rootEvaluation p a ha (AdjoinRoot.root p) = a := aeval_X a

private theorem mem_range_rootEvaluation_iff (p : F[X]) (a : R) (ha : aeval a p = 0) {n : ℕ}
    (hspan : ∀ b : R, Commute b a → ∃ c : Fin n → F, b = ∑ i, c i • a ^ (i : ℕ)) (b : R) :
    b ∈ Set.range (rootEvaluation p a ha) ↔ Commute b a := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [rootEvaluation_mk]
    simpa only [aeval_X] using (Commute.all q (X : F[X])).map (aeval a)
  · intro hb
    obtain ⟨c, hc⟩ := hspan b hb
    refine ⟨AdjoinRoot.mk p (∑ i : Fin n, monomial (i : ℕ) (c i)), ?_⟩
    rw [rootEvaluation_mk, hc, map_sum]
    simp only [aeval_monomial, Algebra.smul_def]

private theorem mem_ordinaryCentralizer_iff {a b : Rˣ} :
    b ∈ twistedCentralizer (MonoidHom.id Rˣ) a ↔ Commute b a := by
  change b⁻¹ * a * b = a ↔ _
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  exact eq_comm

private def evaluationUnits (p : F[X]) (a : Rˣ) (ha : aeval a.val p = 0) {n : ℕ}
    (hspan : ∀ b : R, Commute b a.val → ∃ c : Fin n → F, b = ∑ i, c i • a.val ^ (i : ℕ)) :
    (AdjoinRoot p)ˣ →* twistedCentralizer (MonoidHom.id Rˣ) a :=
  (Units.map (rootEvaluation p a.val ha).toMonoidHom).codRestrict _ fun x => by
    apply mem_ordinaryCentralizer_iff.mpr
    apply Units.ext
    exact (mem_range_rootEvaluation_iff p a.val ha hspan _).1 ⟨x.val, rfl⟩

private theorem evaluationUnits_surjective (p : F[X]) (a : Rˣ) (ha : aeval a.val p = 0) {n : ℕ}
    (hspan : ∀ b : R, Commute b a.val → ∃ c : Fin n → F, b = ∑ i, c i • a.val ^ (i : ℕ))
    (hinj : Function.Injective (rootEvaluation p a.val ha)) :
    Function.Surjective (evaluationUnits p a ha hspan) := by
  intro z
  let e := rootEvaluation p a.val ha
  have h (b : twistedCentralizer (MonoidHom.id Rˣ) a) : b.val.val ∈ Set.range e :=
    (mem_range_rootEvaluation_iff p a.val ha hspan _).mpr
      ((mem_ordinaryCentralizer_iff.mp b.property).map (Units.coeHom R))
  obtain ⟨v, hv⟩ := h z
  obtain ⟨w, hw⟩ := h z⁻¹
  have hvw : v * w = 1 := hinj (by rw [map_mul, map_one, hv, hw]; exact z.val.val_inv)
  have hwv : w * v = 1 := hinj (by rw [map_mul, map_one, hv, hw]; exact z.val.inv_val)
  exact ⟨⟨v, w, hvw, hwv⟩, Subtype.ext (Units.ext hv)⟩

variable [TopologicalSpace F] [IsTopologicalRing F] [TopologicalSpace R] [IsModuleTopology F R]

private def evaluationUnitsEquiv [T2Space R] [Nontrivial R]
    (p : F[X]) [Fact (Irreducible p)] [Module.Finite F (AdjoinRoot p)] (a : Rˣ)
    (ha : aeval a.val p = 0) {n : ℕ}
    (hspan : ∀ b : R, Commute b a.val → ∃ c : Fin n → F, b = ∑ i, c i • a.val ^ (i : ℕ)) :
    letI : TopologicalSpace (AdjoinRoot p) := moduleTopology F (AdjoinRoot p)
    (AdjoinRoot p)ˣ ≃ₜ* twistedCentralizer (MonoidHom.id Rˣ) a := by
  let : TopologicalSpace (AdjoinRoot p) := moduleTopology F (AdjoinRoot p)
  let : IsModuleTopology F (AdjoinRoot p) := ⟨rfl⟩
  let : IsTopologicalRing (AdjoinRoot p) := IsModuleTopology.isTopologicalRing F (AdjoinRoot p)
  let : ContinuousAdd R := IsModuleTopology.toContinuousAdd F R
  let e := rootEvaluation p a.val ha
  let f := evaluationUnits p a ha hspan
  have hinj : Function.Injective e := e.injective
  let hr := e.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  let r := hr.choose
  have hleft : Function.LeftInverse r e := LinearMap.congr_fun hr.choose_spec
  have he : IsClosedEmbedding e := hleft.isClosedEmbedding
    (IsModuleTopology.continuous_of_linearMap r)
    (IsModuleTopology.continuous_of_linearMap e.toLinearMap)
  let : T2Space (AdjoinRoot p) := he.isEmbedding.t2Space
  have hf : IsEmbedding f := IsEmbedding.subtypeVal.of_comp_iff.mp he.units_map.isEmbedding
  let eM := MulEquiv.ofBijective f ⟨hf.injective, evaluationUnits_surjective p a ha hspan hinj⟩
  exact { eM with
    continuous_toFun := hf.continuous
    continuous_invFun := (eM.toEquiv.toHomeomorphOfIsInducing hf.isInducing).continuous_invFun }

end Evaluation

section Algebra

variable (F D : Type u) [Field F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D]

local notation "d" => reducedDegree F D

/-- The centralizer of a regular division unit is commutative. -/
theorem divisionCentralizer_mul_comm {a : Dˣ} (ha : IsRegular F D a)
    (b c : divisionCentralizer a) : b * c = c * b := by
  let p := reducedCharpoly F D a.val
  let h := CentralDivision.aeval_reducedCharpoly F D a.val
  let e := rootEvaluation p a.val h
  have preimage (z : divisionCentralizer a) : z.val.val ∈ Set.range e :=
    (mem_range_rootEvaluation_iff p a.val h (fun _ hb =>
      exists_sum_pow_of_commute_regular_division F D ha hb) _).mpr
        ((mem_ordinaryCentralizer_iff.mp z.property).map (Units.coeHom D))
  obtain ⟨v, hv⟩ := preimage b
  obtain ⟨w, hw⟩ := preimage c
  apply Subtype.ext
  apply Units.ext
  change b.val.val * c.val.val = c.val.val * b.val.val
  rw [← hv, ← hw, ← map_mul, ← map_mul, mul_comm v w]

private theorem divisionCentralizer_eq_of_regular_commute {a b : Dˣ}
    (ha : IsRegular F D a) (hb : IsRegular F D b) (hab : Commute a b) :
    divisionCentralizer a = divisionCentralizer b := by
  have hle {x y : Dˣ} (hx : IsRegular F D x) (hxy : Commute x y) :
      divisionCentralizer x ≤ divisionCentralizer y := by
    intro z hz
    apply mem_ordinaryCentralizer_iff.mpr
    have hy : y ∈ divisionCentralizer x := mem_ordinaryCentralizer_iff.mpr hxy.symm
    exact congrArg Subtype.val (divisionCentralizer_mul_comm F D hx ⟨z, hz⟩ ⟨y, hy⟩)
  exact le_antisymm (hle ha hab) (hle hb hab.symm)

/-- Equal reduced characteristic coefficients at a regular unit determine its conjugacy class. -/
theorem exists_divisionConj_of_regular_coefficients_eq {a b : Dˣ}
    (ha : IsRegular F D a) (hab : divisionCoefficients F D a = divisionCoefficients F D b) :
    ∃ x : Dˣ, x⁻¹ * a * x = b := by
  let p := reducedCharpoly F D a.val
  have heq : p = reducedCharpoly F D b.val := (divisionCoefficients_eq_iff F D).mp hab
  let : Fact (Irreducible p) := ⟨irreducible_reducedCharpoly_of_separable F D _ ha⟩
  let : Module.Finite F (AdjoinRoot p) := (reducedCharpoly_monic F D a.val).finite_adjoinRoot
  let f := rootEvaluation p a.val (CentralDivision.aeval_reducedCharpoly F D a.val)
  have hb : aeval b.val p = 0 := by
    rw [heq]
    exact CentralDivision.aeval_reducedCharpoly F D b.val
  let g := rootEvaluation p b.val hb
  obtain ⟨x, hx⟩ := CentralDivision.fieldEmbeddingsConjugate F D (AdjoinRoot p) g f
  refine ⟨x⁻¹, Units.ext ?_⟩
  simpa only [f, g, rootEvaluation_root, Units.val_mul, inv_inv] using (hx (AdjoinRoot.root p)).symm

end Algebra

section LocalField

variable (F D : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D] [TopologicalSpace D] [IsModuleTopology F D]

local notation "d" => reducedDegree F D

/-- A regular division centralizer has a largest compact open subgroup. -/
theorem divisionCentralizer_hasLargestCompactOpenSubgroup {a : Dˣ} (ha : IsRegular F D a) :
    HasLargestCompactOpenSubgroup (divisionCentralizer a) := by
  let : T2Space D := Langlands.JacquetLanglands.t2Space F D
  let p := reducedCharpoly F D a.val
  let : Fact (Irreducible p) := ⟨irreducible_reducedCharpoly_of_separable F D _ ha⟩
  let : Module.Finite F (AdjoinRoot p) := (reducedCharpoly_monic F D a.val).finite_adjoinRoot
  let : TopologicalSpace (AdjoinRoot p) := moduleTopology F (AdjoinRoot p)
  let : IsModuleTopology F (AdjoinRoot p) := ⟨rfl⟩
  let e := evaluationUnitsEquiv p a (CentralDivision.aeval_reducedCharpoly F D a.val) (n := d)
    (fun _ hb => exists_sum_pow_of_commute_regular_division F D ha hb)
  exact HasLargestCompactOpenSubgroup.of_isClosedEmbedding
    (HasLargestCompactOpenSubgroup.finiteAlgebraUnits F (AdjoinRoot p))
    e.symm.toMonoidHom e.symm.toHomeomorph.isClosedEmbedding

variable [CharZero F]

/-- Regular division units form an open subset in the unit group. -/
theorem isOpen_regularDivision : IsOpen {a : Dˣ | IsRegular F D a} := by
  have h : {a : Dˣ | IsRegular F D a} = divisionCoefficients F D ⁻¹'
      {b : Fin d → F | (polynomialOfCoefficients b).Separable} := by
    ext a
    simp only [mem_ofPred_eq, mem_preimage, polynomialOfCoefficients_divisionCoefficients, IsRegular]
  rw [h]
  exact (isOpen_separable_polynomialOfCoefficients d).preimage (continuous_divisionCoefficients F D)

set_option maxHeartbeats 800000 in
/-- Around every regular unit, the reduced coefficients have a continuous section
whose values are regular units in the given centralizer. -/
theorem exists_regularDivisionCoefficientSection {a : Dˣ} (ha : IsRegular F D a) :
    ∃ (V : Set (Fin d → F)) (s : V → Dˣ), IsOpen V ∧ divisionCoefficients F D a ∈ V ∧
      Continuous s ∧ (∀ b, divisionCoefficients F D (s b) = b.val) ∧
      ∀ b, IsRegular F D (s b) ∧ divisionCentralizer (s b) = divisionCentralizer a := by
  let : NontriviallyNormedField F := LocalGalois.localNormedField F
  let : CompleteSpace F := LocalGalois.localNormedField_complete F
  let : IsTopologicalRing D := isTopologicalRing F D
  obtain ⟨g, hg⟩ := exists_corresponds F D a ha
  let p := g.val.charpoly
  let : Fact (Irreducible p) := ⟨hg.1.2⟩
  let : Module.Finite F (AdjoinRoot p) := g.val.charpoly_monic.finite_adjoinRoot
  let : TopologicalSpace (AdjoinRoot p) := moduleTopology F (AdjoinRoot p)
  let : IsModuleTopology F (AdjoinRoot p) := ⟨rfl⟩
  let : IsTopologicalRing (AdjoinRoot p) := IsModuleTopology.isTopologicalRing F (AdjoinRoot p)
  have hpa : aeval a.val p = 0 := by
    change aeval a.val g.val.charpoly = 0
    rw [hg.2.2]
    exact CentralDivision.aeval_reducedCharpoly F D a.val
  let eD := rootEvaluation p a.val hpa
  obtain ⟨v, hv⟩ := regularCyclicBasis F d g.val hg.1.1
  let : IsModuleTopology F (Matrix (Fin d) (Fin d) F) :=
    inferInstanceAs (IsModuleTopology F (Fin d → Fin d → F))
  let evalG := evaluationUnitsEquiv p g (Matrix.aeval_self_charpoly g.val)
    (fun _ hz => exists_sum_pow_of_commute hv hz)
  let eG := rootEvaluation p g.val (Matrix.aeval_self_charpoly g.val)
  have hcoeff : coefficients g = divisionCoefficients F D a :=
    (corresponds_iff_coefficients_eq F D ha).mp hg
  obtain ⟨V₀, hgV₀, t, hV₀, ht, -, hpow, hct⟩ :=
    regularCoefficientSlice F d 1 g Nat.one_pos hg.1.1
  let V := V₀ ∩ {b : Fin d → F | (polynomialOfCoefficients b).Separable ∧
    Irreducible (polynomialOfCoefficients b)}
  have hV : IsOpen V := hV₀.inter (isOpen_separable_irreducible_polynomialOfCoefficients d)
  have haV : divisionCoefficients F D a ∈ V := by
    rw [← hcoeff]
    refine ⟨hgV₀, ?_⟩
    change (polynomialOfCoefficients (coefficients g)).Separable ∧
      Irreducible (polynomialOfCoefficients (coefficients g))
    rw [polynomialOfCoefficients_coefficients]
    exact hg.1
  let i : V → V₀ := fun b => ⟨b.val, b.property.1⟩
  let r (b : V) : GeneralLinear d F := g * t (i b)
  have hri (b : V) : r b ∈ glCentralizer g := by
    apply mem_ordinaryCentralizer_iff.mpr
    obtain ⟨c, hc⟩ := hpow (i b)
    have hsum : Commute (∑ j : Fin d, c j • g.val ^ (j : ℕ)) g.val :=
      Commute.sum_left Finset.univ _ _ fun j _ => by
        rw [Algebra.smul_def]
        have hcomm := Algebra.commute_algebraMap_left (c j) g.val
        exact hcomm.mul_left ((Commute.refl g.val).pow_left (j : ℕ))
    have hcomm : Commute (t (i b)).val g.val := by
      rw [hc]
      exact (Commute.one_left g.val).add_left hsum
    exact Units.ext ((Commute.refl g.val).mul_left hcomm).eq
  let z (b : V) := evalG.symm ⟨r b, hri b⟩
  let s (b : V) : Dˣ := Units.map eD.toMonoidHom (z b)
  have hs : Continuous s := by
    have hrc : Continuous r := continuous_const.mul (ht.comp (continuous_subtype_val.subtype_mk _))
    have hz : Continuous z := evalG.symm.continuous.comp (hrc.subtype_mk _)
    have he : Continuous (eD : AdjoinRoot p → D) :=
      IsModuleTopology.continuous_of_linearMap eD.toLinearMap
    exact (he.units_map eD.toMonoidHom).comp hz
  have hpoly (b : V) : reducedCharpoly F D (s b).val = polynomialOfCoefficients b.val := by
    have hc : coefficients (r b) = b.val := by simpa only [pow_one] using hct (i b)
    have hr : (r b).val.charpoly = polynomialOfCoefficients b.val := by
      rw [← polynomialOfCoefficients_coefficients (r b), hc]
    have hz : eG (z b).val = (r b).val := by
      change (evalG (z b)).val.val = (r b).val
      exact congrArg (fun x : glCentralizer g => x.val.val)
        (evalG.apply_symm_apply ⟨r b, hri b⟩)
    have hroot : aeval (z b).val (polynomialOfCoefficients b.val) = 0 := by
      apply eG.injective
      change eG (aeval (z b).val (polynomialOfCoefficients b.val)) = eG 0
      rw [← aeval_algHom_apply eG, hz, ← hr, Matrix.aeval_self_charpoly, map_zero]
    have hDs : aeval (s b).val (polynomialOfCoefficients b.val) = 0 := by
      change aeval (eD (z b).val) (polynomialOfCoefficients b.val) = 0
      rw [aeval_algHom_apply eD, hroot, map_zero]
    have hm := polynomialOfCoefficients_isMonicOfDegree b.val
    have hmin := minpoly.eq_of_irreducible_of_monic b.property.2.2 hDs hm.monic
    have hdvd := minpoly.dvd F (s b).val (CentralDivision.aeval_reducedCharpoly F D (s b).val)
    rw [← hmin] at hdvd
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hm.monic
      (reducedCharpoly_monic F D (s b).val) hdvd (by
        rw [reducedCharpoly_natDegree, hm.natDegree_eq]))
  refine ⟨V, s, hV, haV, hs, ?_, ?_⟩
  · intro b
    funext j
    change (reducedCharpoly F D (s b).val).coeff j = b.val j
    rw [hpoly]
    simp [polynomialOfCoefficients, finsetSum_coeff, coeff_X_pow, Nat.ne_of_lt j.isLt, Fin.val_eq_val]
  · intro b
    have hr : IsRegular F D (s b) := by
      unfold IsRegular
      rw [hpoly]
      exact b.property.2.1
    refine ⟨hr, divisionCentralizer_eq_of_regular_commute F D hr ha ?_⟩
    apply Units.ext
    exact (mem_range_rootEvaluation_iff p a.val hpa (n := d) (fun _ hz =>
      exists_sum_pow_of_commute_regular_division F D ha hz) _).1 ⟨(z b).val, rfl⟩

end LocalField

end Langlands.JacquetLanglands
