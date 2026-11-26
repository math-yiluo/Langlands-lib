import Langlands.BaseChange.RegularCyclicBasis
import Langlands.BaseChange.SigmaLiftCharacterIdentity.Parameters
import Langlands.Global.AdelicGLDeterminantNormOne
import Langlands.Global.FiniteAdelicGL.RestrictedProduct
import Langlands.Global.PositiveRealIdeles
import Langlands.Global.PrincipalAdelesDiscreteProof
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Closed adelic conjugacy classes with separable rational characteristic polynomial -/

noncomputable section

open Filter Matrix Polynomial
open Langlands.BaseChange Langlands.Global
open scoped NNReal RestrictedProduct

namespace Langlands.TraceFormula

universe u

section CyclicBasis

variable {R : Type u} [CommRing R] {n : ℕ}

private theorem inv_mul_mul_eq_of_mul_eq {G : Type*} [Group G] {x y z : G}
    (h : x * z = z * y) : z⁻¹ * x * z = y := by
  rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem exists_conjugator_of_separable {K : Type u} [Field K]
    {x y : Matrix.GeneralLinearGroup (Fin n) K} (hs : x.val.charpoly.Separable)
    (hp : x.val.charpoly = y.val.charpoly) : ∃ z, z⁻¹ * x * z = y := by
  obtain ⟨v, hv⟩ := regularCyclicBasis K n x.val hs
  obtain ⟨w, hw⟩ := regularCyclicBasis K n y.val (hp ▸ hs)
  exact ⟨hv.unit * hw.unit⁻¹,
    inv_mul_mul_eq_of_mul_eq (Units.ext (cyclicBasis_conjugator hv hw hp))⟩

private theorem exists_cyclicBasisMatrix_of_residue [IsLocalRing R]
    (A : Matrix (Fin n) (Fin n) R)
    (hsep : (A.map (IsLocalRing.residue R)).charpoly.Separable) :
    ∃ v, IsUnit (cyclicBasisMatrix A v) := by
  let f := IsLocalRing.residue R
  obtain ⟨v₀, hv₀⟩ := regularCyclicBasis (IsLocalRing.ResidueField R) n (A.map f) hsep
  choose v hv using fun i => IsLocalRing.residue_surjective (v₀ i)
  have he : f ∘ v = v₀ := funext hv
  have hM : (cyclicBasisMatrix A v).map f = cyclicBasisMatrix (A.map f) v₀ := by
    rw [cyclicBasisMatrix_map, he]
  refine ⟨v, (Matrix.isUnit_iff_isUnit_det _).mpr ?_⟩
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  change f (cyclicBasisMatrix A v).det ≠ 0
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hv₀).ne_zero

end CyclicBasis

section FinitePlaces

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

private abbrev integers (v : FinitePlace F) := v.adicCompletionIntegers F

private abbrev integralInclusion (v : FinitePlace F) : integers F v →+* FiniteCompletion F v :=
  (integers F v).toSubring.subtype

private theorem eventually_polynomial_has_integral_lift (p : F[X]) :
    ∀ᶠ v : FinitePlace F in cofinite,
      ∃ q : (integers F v)[X], q.map (integralInclusion F v) =
        p.map (algebraMap F (FiniteCompletion F v)) := by
  have hcoeff : ∀ᶠ v : FinitePlace F in cofinite,
      ∀ i : {i // i ∈ p.support},
        algebraMap F (FiniteCompletion F v) (p.coeff i.val) ∈ integers F v :=
    Filter.eventually_all.mpr fun i => (algebraMap F (FiniteAdeles F) (p.coeff i.val)).2
  filter_upwards [hcoeff] with v hv
  apply (Polynomial.mem_lifts _).mp
  apply (Polynomial.lifts_iff_coeff_lifts _).mpr
  intro i
  rw [Polynomial.coeff_map]
  by_cases hi : i ∈ p.support
  · exact ⟨⟨_, hv ⟨i, hi⟩⟩, rfl⟩
  · rw [Polynomial.notMem_support_iff.mp hi, map_zero]
    exact ⟨0, map_zero _⟩

private def integralMatrix (v : FinitePlace F) (x : FiniteLocalGL F n v)
    (hx : x ∈ FiniteAdelicGL.localIntegral F n v) : Matrix (Fin n) (Fin n) (integers F v) :=
  Matrix.of fun i j => ⟨x i j, (FiniteAdelicGL.mem_localIntegral F n v x).mp hx |>.1 i j⟩

private theorem exists_integral_conjugator (v : FinitePlace F) {x y : FiniteLocalGL F n v}
    (hx : x ∈ FiniteAdelicGL.localIntegral F n v)
    (hy : y ∈ FiniteAdelicGL.localIntegral F n v)
    (hp : x.val.charpoly = y.val.charpoly)
    (hs : (integralMatrix F n v x hx).charpoly.Separable) :
    ∃ z ∈ FiniteAdelicGL.localIntegral F n v, z⁻¹ * x * z = y := by
  let A := integralMatrix F n v x hx
  let B := integralMatrix F n v y hy
  let f := integralInclusion F v
  have hA : A.map f = x.val := rfl
  have hB : B.map f = y.val := rfl
  have hAB : A.charpoly = B.charpoly := by
    apply Polynomial.map_injective f Subtype.val_injective
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_map, hA, hB, hp]
  have hsepA : (A.map (IsLocalRing.residue _)).charpoly.Separable := by
    rw [Matrix.charpoly_map]
    exact hs.map
  have hsepB : (B.map (IsLocalRing.residue _)).charpoly.Separable := by
    rw [Matrix.charpoly_map, ← hAB]
    exact hs.map
  obtain ⟨a, ha⟩ := exists_cyclicBasisMatrix_of_residue A hsepA
  obtain ⟨b, hb⟩ := exists_cyclicBasisMatrix_of_residue B hsepB
  let z₀ := ha.unit * hb.unit⁻¹
  let z := Matrix.GeneralLinearGroup.map f z₀
  have hz : z ∈ FiniteAdelicGL.localIntegral F n v := by
    rw [FiniteAdelicGL.mem_localIntegral]
    exact ⟨fun i j => (z₀ i j).property, fun i j => (z₀⁻¹ i j).property⟩
  refine ⟨z, hz, inv_mul_mul_eq_of_mul_eq (Units.ext ?_)⟩
  change x.val * z₀.val.map f = z₀.val.map f * y.val
  have h := congrArg f.mapMatrix (cyclicBasis_conjugator ha hb hAB)
  simpa only [map_mul, RingHom.mapMatrix_apply, hA, hB, z₀] using h

private theorem eventually_exists_integral_conjugator (g : RationalGL F n)
    (hs : g.val.charpoly.Separable) (y : FiniteAdelicGL F n)
    (hp : ∀ v, (FiniteAdelicGL.localProjection F n v
      (AdelicGL.finite F n (AdelicGL.rational F n g))).val.charpoly =
        (FiniteAdelicGL.localProjection F n v y).val.charpoly) :
    ∀ᶠ v : FinitePlace F in cofinite,
      ∃ z ∈ FiniteAdelicGL.localIntegral F n v,
        z⁻¹ * FiniteAdelicGL.localProjection F n v
          (AdelicGL.finite F n (AdelicGL.rational F n g)) * z =
            FiniteAdelicGL.localProjection F n v y := by
  let p := g.val.charpoly
  let x := AdelicGL.finite F n (AdelicGL.rational F n g)
  obtain ⟨s, t, hst⟩ := hs
  filter_upwards [FiniteAdelicGL.eventually_localIntegral F n x,
    FiniteAdelicGL.eventually_localIntegral F n y,
    eventually_polynomial_has_integral_lift F s, eventually_polynomial_has_integral_lift F t]
    with v hx hy hsl htl
  obtain ⟨s₀, hsl⟩ := hsl
  obtain ⟨t₀, htl⟩ := htl
  let A := integralMatrix F n v (FiniteAdelicGL.localProjection F n v x) hx
  let f := integralInclusion F v
  let fv := algebraMap F (FiniteCompletion F v)
  have hA : A.charpoly.map f = p.map fv := by
    rw [← Matrix.charpoly_map]
    change (g.val.map fv).charpoly = p.map fv
    exact Matrix.charpoly_map g.val fv
  have hst₀ : s₀ * A.charpoly + t₀ * A.charpoly.derivative = 1 := by
    apply Polynomial.map_injective f Subtype.val_injective
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
      hA, hsl, htl, Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul,
      ← Polynomial.map_add, hst, Polynomial.map_one, Polynomial.map_one]
  exact exists_integral_conjugator F n v hx hy (hp v) ⟨s₀, t₀, hst₀⟩

private theorem exists_finite_conjugator (g : RationalGL F n)
    (hs : g.val.charpoly.Separable) (y : FiniteAdelicGL F n)
    (hp : ∀ v, (FiniteAdelicGL.localProjection F n v
      (AdelicGL.finite F n (AdelicGL.rational F n g))).val.charpoly =
        (FiniteAdelicGL.localProjection F n v y).val.charpoly) :
    ∃ z : FiniteAdelicGL F n,
      z⁻¹ * AdelicGL.finite F n (AdelicGL.rational F n g) * z = y := by
  classical
  let x := AdelicGL.finite F n (AdelicGL.rational F n g)
  let P (v : FinitePlace F) (z : FiniteLocalGL F n v) :=
    z⁻¹ * FiniteAdelicGL.localProjection F n v x * z = FiniteAdelicGL.localProjection F n v y
  have hgood := eventually_exists_integral_conjugator F n g hs y hp
  change ∀ᶠ v : FinitePlace F in cofinite, ∃ z ∈ FiniteAdelicGL.localIntegral F n v, P v z at hgood
  have hex (v : FinitePlace F) : ∃ z, P v z ∧
      ((∃ c ∈ FiniteAdelicGL.localIntegral F n v, P v c) → z ∈ FiniteAdelicGL.localIntegral F n v) := by
    by_cases h : ∃ c ∈ FiniteAdelicGL.localIntegral F n v, P v c
    · obtain ⟨c, hI, hc⟩ := h
      exact ⟨c, hc, fun _ => hI⟩
    · have hsep : (FiniteAdelicGL.localProjection F n v x).val.charpoly.Separable := by
        change (g.val.map (algebraMap F (FiniteCompletion F v))).charpoly.Separable
        rw [Matrix.charpoly_map]
        exact hs.map
      obtain ⟨c, hc⟩ := exists_conjugator_of_separable hsep (hp v)
      exact ⟨c, hc, fun hc' => (h hc').elim⟩
  choose c hc using hex
  let cr : FiniteAdelicGL.LocalRestrictedProduct F n :=
    ⟨c, hgood.mono fun v hv => (hc v).2 hv⟩
  refine ⟨FiniteAdelicGL.fromRestrictedProduct F n cr, ?_⟩
  apply FiniteAdelicGL.ext_localProjection F n
  intro v
  simp only [map_mul, map_inv, FiniteAdelicGL.localProjection_fromRestrictedProduct]
  exact (hc v).1

end FinitePlaces

section Adelic

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

private def infiniteMatrixEquiv : InfiniteAdelicGL F n ≃*
    ((v : Global.InfinitePlace F) → Matrix.GeneralLinearGroup (Fin n) (InfiniteCompletion F v)) :=
  (Units.mapEquiv (Matrix.piRingEquiv (β := InfiniteCompletion F) (n := Fin n)).toMulEquiv).trans
    MulEquiv.piUnits

private theorem exists_adelic_conjugator (g : RationalGL F n) (hs : g.val.charpoly.Separable)
    (y : AdelicGL F n) (hp : (AdelicGL.rational F n g).val.charpoly = y.val.charpoly) :
    ∃ z : AdelicGL F n, z⁻¹ * AdelicGL.rational F n g * z = y := by
  classical
  let x := AdelicGL.rational F n g
  let e := infiniteMatrixEquiv F n
  have hi (v : Global.InfinitePlace F) : ∃ c,
      c⁻¹ * e (AdelicGL.infinite F n x) v * c = e (AdelicGL.infinite F n y) v := by
    apply exists_conjugator_of_separable
    · change (g.val.map (algebraMap F (InfiniteCompletion F v))).charpoly.Separable
      rw [Matrix.charpoly_map]
      exact hs.map
    · change (x.val.map (infiniteProjection F v)).charpoly =
        (y.val.map (infiniteProjection F v)).charpoly
      rw [Matrix.charpoly_map, Matrix.charpoly_map, hp]
  choose ci hci using hi
  let a := e.symm ci
  have ha : a⁻¹ * AdelicGL.infinite F n x * a = AdelicGL.infinite F n y := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, e.apply_symm_apply]
    exact funext hci
  obtain ⟨b, hb⟩ := exists_finite_conjugator F n g hs (AdelicGL.finite F n y) (fun v => by
    change (x.val.map (finiteProjection F v)).charpoly = (y.val.map (finiteProjection F v)).charpoly
    rw [Matrix.charpoly_map, Matrix.charpoly_map, hp])
  let z := AdelicGL.pair F n a b
  refine ⟨z, ?_⟩
  apply (AdelicGL.split F n).injective
  apply Prod.ext
  · change AdelicGL.infinite F n (z⁻¹ * x * z) = AdelicGL.infinite F n y
    simpa only [map_mul, map_inv, z, AdelicGL.infinite_pair] using ha
  · change AdelicGL.finite F n (z⁻¹ * x * z) = AdelicGL.finite F n y
    simpa only [map_mul, map_inv, z, AdelicGL.finite_pair] using hb

set_option maxHeartbeats 600000 in
/-- The adelic conjugacy class of the image of a rational matrix with separable characteristic
polynomial is the full characteristic-polynomial fiber in the adelic matrix group. -/
theorem adelicRationalConjugacyOrbit_eq_charpolyFiber (g : RationalGL F n)
    (hs : g.val.charpoly.Separable) :
    Set.range (fun z : AdelicGL F n => z⁻¹ * AdelicGL.rational F n g * z) =
      {y | y.val.charpoly = (AdelicGL.rational F n g).val.charpoly} := by
  refine Set.ext fun y => ?_
  change (∃ z : AdelicGL F n, z⁻¹ * AdelicGL.rational F n g * z = y) ↔
    y.val.charpoly = (AdelicGL.rational F n g).val.charpoly
  constructor
  · rintro ⟨z, rfl⟩
    simpa only [Units.val_mul, Matrix.coe_units_inv] using
      (Matrix.charpoly_units_conj' z (AdelicGL.rational F n g).val)
  · intro hy
    exact exists_adelic_conjugator F n g hs y hy.symm

/-- In the existing units topology, the rational separable adelic conjugacy class is closed. -/
theorem isClosed_adelicRationalConjugacyOrbit (g : RationalGL F n)
    (hs : g.val.charpoly.Separable) :
    IsClosed (Set.range (fun z : AdelicGL F n => z⁻¹ * AdelicGL.rational F n g * z)) := by
  rw [adelicRationalConjugacyOrbit_eq_charpolyFiber F n g hs]
  have h : {y : AdelicGL F n | y.val.charpoly = (AdelicGL.rational F n g).val.charpoly} =
      ⋂ k : ℕ, {y : AdelicGL F n | y.val.charpoly.coeff k =
        (AdelicGL.rational F n g).val.charpoly.coeff k} := by
    refine Set.ext fun y => ?_
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Polynomial.ext_iff]
  rw [h]
  let : T2Space (Adeles F) := adeles_t2Space F
  exact isClosed_iInter fun k => isClosed_eq
    (SigmaLiftCharacterIdentity.continuous_charpoly_coefficient (R := Adeles F) k) continuous_const

private theorem exists_determinantNormOne_conjugator (hn : n ≠ 0) (x z : AdelicGL F n) :
    ∃ z₁ : AdelicGL.determinantNormOne F n, z₁.val⁻¹ * x * z₁.val = z⁻¹ * x * z := by
  let d := Module.finrank ℚ F * n
  have hd : d ≠ 0 := mul_ne_zero Module.finrank_pos.ne' hn
  let D := AdelicBlockDeterminantCharacter.determinantNorm F n
  let t := Units.map (NNReal.rpowMonoidHom ((d : ℝ)⁻¹)) (D z)
  have ht : t ^ d = D z := by
    apply Units.ext
    exact NNReal.rpow_inv_natCast_pow _ hd
  let a := PositiveRealIdeles.full F t
  let s := AdelicGL.scalar F n a
  have hD : D s = D z := by
    change AdelicBlockDeterminantCharacter.determinantNorm F n (AdelicGL.scalar F n a) = _
    rw [AdelicBlockDeterminantCharacter.determinantNorm_scalar,
      show a = PositiveRealIdeles.full F t from rfl, PositiveRealIdeles.absoluteValue_full,
      ← pow_mul, ht]
  have hg : s⁻¹ * z ∈ AdelicGL.determinantNormOne F n := by
    change D (s⁻¹ * z) = 1
    rw [map_mul, map_inv, hD, inv_mul_cancel]
  refine ⟨⟨s⁻¹ * z, hg⟩, ?_⟩
  have hcomm : Commute s x := AdelicGL.scalar_commute F n a x
  change (s⁻¹ * z)⁻¹ * x * (s⁻¹ * z) = z⁻¹ * x * z
  calc
    (s⁻¹ * z)⁻¹ * x * (s⁻¹ * z) = z⁻¹ * (s * x * s⁻¹) * z := by group
    _ = z⁻¹ * x * z := by rw [hcomm.eq, mul_assoc x s, mul_inv_cancel, mul_one]

/-- The conjugacy class of a determinant-norm-one rational matrix is closed inside the
norm-one adelic matrix group when the rational characteristic polynomial is separable. -/
theorem isClosed_normOneRationalConjugacyOrbit (hn : n ≠ 0) (g : RationalGL F n)
    (hs : g.val.charpoly.Separable) (r : AdelicGL.determinantNormOne F n)
    (hr : r.val = AdelicGL.rational F n g) :
    IsClosed (Set.range (fun z : AdelicGL.determinantNormOne F n => z⁻¹ * r * z)) := by
  have he : Set.range (fun z : AdelicGL.determinantNormOne F n => z⁻¹ * r * z) =
      Subtype.val ⁻¹' Set.range (fun z : AdelicGL F n => z⁻¹ * AdelicGL.rational F n g * z) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.val, by rw [← hr]; rfl⟩
    · rintro ⟨z, hz⟩
      obtain ⟨z₁, hz₁⟩ := exists_determinantNormOne_conjugator F n hn r.val z
      exact ⟨z₁, Subtype.ext (hz₁.trans (hr ▸ hz))⟩
  rw [he]
  exact (isClosed_adelicRationalConjugacyOrbit F n g hs).preimage continuous_subtype_val

end Adelic

end Langlands.TraceFormula
