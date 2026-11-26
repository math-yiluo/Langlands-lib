import Langlands.Automorphic.AssociatedGammaOutsideMatch
import Langlands.Global.Factors.RelativePairLFactorProduct
import Langlands.Correspondence.HenniartTwistBridge
import Langlands.Global.Factors.WeilPoleRegionUnitaryProof
import Langlands.Representation.RankinSelberg.PairGammaOrder
import Langlands.Representation.RankinSelberg.UnitaryContragredientTwistParameters
import Langlands.VirtualRepresentation.Supercuspidal.UnitarySupportInduction

/-! # Recovering normalized pair L-polynomials from their pole orders -/

noncomputable section

set_option autoImplicit false

universe uF

namespace Langlands.Global.PoleComparison

open Polynomial RankinSelberg

variable {q : ℕ}

/-- A twist with parameter `z = q^(-s₀)` moves the multiplicity of the root `z`
to the reciprocal polynomial's pole order at the spectral origin. -/
theorem meromorphicOrderAt_rescaledPairLFactor
    (hq : 1 < q) (P : ℂ[X]) (hP : P ≠ 0) {s₀ : ℂ} {z : ℂ}
    (hz : spectralPoint q s₀ = z) :
    meromorphicOrderAt (fun s =>
      RatFunc.eval (RingHom.id ℂ) (spectralPoint q s)
        ((algebraMap ℂ[X] (RatFunc ℂ) (P.comp (C z * X)))⁻¹)) 0 =
      ((-(P.rootMultiplicity z : ℤ)) : WithTop ℤ) := by
  have hfun : (fun s => RatFunc.eval (RingHom.id ℂ) (spectralPoint q s)
      ((algebraMap ℂ[X] (RatFunc ℂ) (P.comp (C z * X)))⁻¹)) =
      fun s => ((P.eval (spectralPoint q (s + s₀)))⁻¹) := by
    funext s
    rw [ClassFieldTheory.Global.RelativeWeilGroup.eval_inv_algebraMap_total,
      eval_comp, eval_mul, eval_C, eval_X, spectralPoint_add hq, hz, mul_comm]
  rw [hfun, meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt
    (f := fun s => ((P.eval (spectralPoint q s))⁻¹)), zero_add]
  change meromorphicOrderAt (fun s => P.eval (spectralPoint q s))⁻¹ s₀ = _
  rw [meromorphicOrderAt_inv, meromorphicOrderAt_eval_spectralPoint q hq P hP, hz]

/-- Normalized complex polynomials whose roots all lie on the unit circle agree
when their root multiplicities agree at each point of the circle. -/
theorem eq_of_unitCircle_rootMultiplicity {P Q : ℂ[X]} (hP : P.coeff 0 = 1)
    (hQ : Q.coeff 0 = 1)
    (hrootP : ∀ z, P.IsRoot z → ‖z‖ = 1)
    (hrootQ : ∀ z, Q.IsRoot z → ‖z‖ = 1)
    (hord : ∀ z : ℂ, ‖z‖ = 1 → P.rootMultiplicity z = Q.rootMultiplicity z) :
    P = Q := by
  classical
  have hr : P.roots = Q.roots := by
    apply Multiset.ext.mpr
    intro z
    rw [count_roots, count_roots]
    by_cases hz : ‖z‖ = 1
    · exact hord z hz
    · rw [rootMultiplicity_eq_zero (fun h => hz (hrootP z h)),
        rootMultiplicity_eq_zero (fun h => hz (hrootQ z h))]
  have hsP := IsAlgClosed.splits P
  have hsQ := IsAlgClosed.splits Q
  have heP : P.eval 0 = 1 := by simpa [← coeff_zero_eq_eval_zero] using hP
  have heQ : Q.eval 0 = 1 := by simpa [← coeff_zero_eq_eval_zero] using hQ
  rw [hsP.eval_eq_prod_roots, hr] at heP
  rw [hsQ.eval_eq_prod_roots] at heQ
  have hn : (Q.roots.map (fun x => 0 - x)).prod ≠ 0 := by
    intro h
    rw [h, mul_zero] at heQ
    exact zero_ne_one heQ
  have hlead : P.leadingCoeff = Q.leadingCoeff :=
    mul_right_cancel₀ hn (heP.trans heQ.symm)
  rw [hsP.eq_prod_roots, hsQ.eq_prod_roots, hr, hlead]

open Langlands.VirtualRepresentation.PadicSupercuspidal in
/-- Every root of a basis pair polynomial lies on the circle. In equal ranks
the factors of JPSS (8.1) come from contragredient-twist parameters of unitary
objects. In unequal ranks the polynomial is one. -/
theorem isUnitaryBasisPairLPolynomial_root_norm
    {p : ℕ} [Fact p.Prime] {F : PadicField p}
    {ψ : Correspondence.NontrivialAdditiveCharacter F}
    {ν : Correspondence.LocalAdditiveHaarMeasure F}
    (hν : Correspondence.IsSelfDualMeasure F ψ ν)
    {a b : UnitaryBasis F} {P : ℂ[X]}
    (hP : IsUnitaryBasisPairLPolynomial F ψ ν a b P)
    {z : ℂ} (hz : P.IsRoot z) : ‖z‖ = 1 := by
  let := F.canonicalTopologicalData.topology
  obtain ⟨⟨⟨_ | r, hr⟩, π⟩, ha⟩ := a
  · exact absurd hr (lt_irrefl 0)
  obtain ⟨⟨⟨_ | n, hn⟩, τ⟩, hb⟩ := b
  · exact absurd hn (lt_irrefl 0)
  induction π using Quotient.inductionOn with
  | h A =>
    induction τ using Quotient.inductionOn with
    | h B =>
      change IsPadicSymmetricLPolynomial F ψ ν A.obj.representation B.obj.representation P at hP
      rcases lt_trichotomy n r with hlt | rfl | hgt
      · have h1 := supercuspidalUnequalRankLFactor p F ψ ⟨ν, hν⟩ r n
          A.obj.representation B.obj.representation A.property.1 A.property.2
          (supercuspidalRep_isOfWhittakerType F ψ B) hlt
        simp only [IsPadicSymmetricLPolynomial, hlt.le, ↓reduceIte] at hP
        rw [hP.unique h1] at hz
        simp [IsRoot] at hz
      · obtain ⟨S, hS, hSP⟩ := supercuspidalEqualRankLFactor p F ψ ⟨ν, hν⟩ n
          A.obj.representation B.obj.representation A.property.1 A.property.2 B.property.1
          (supercuspidalRep_isOfWhittakerType F ψ B)
        simp only [IsPadicSymmetricLPolynomial, le_refl, ↓reduceIte] at hP
        rw [hP.unique hSP] at hz
        change (∏ a ∈ S, (1 - C a * X)).eval z = 0 at hz
        rw [eval_prod, Finset.prod_eq_zero_iff] at hz
        obtain ⟨a, haS, haz⟩ := hz
        have hnorm := IsContragredientTwistParameter.norm_eq_one F
          A.obj.representation B.obj.representation ((hS a).mp haS)
          A.property.1 B.property.1 (supercuspidalRep_isOfWhittakerType F ψ A).1
          (supercuspidalRep_isOfWhittakerType F ψ B).1 ha hb
        simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X, sub_eq_zero] at haz
        simpa only [norm_one, norm_mul, hnorm, one_mul] using congrArg norm haz.symm
      · have h1 := supercuspidalUnequalRankLFactor p F ψ ⟨ν, hν⟩ n r
          B.obj.representation A.obj.representation B.property.1 B.property.2
          (supercuspidalRep_isOfWhittakerType F ψ A) hgt
        simp only [IsPadicSymmetricLPolynomial, Nat.not_le.mpr hgt, ↓reduceIte] at hP
        rw [hP.unique h1] at hz
        simp [IsRoot] at hz

/-- The Euler polynomial on the inertia-fixed monodromy kernel of a unitary
Weil action has all its roots on the unit circle. -/
theorem weilDeligne_eulerPolynomial_root_norm
    {G : Type*} [Group G] {ν : G →* ℂˣ}
    (A : WeilDeligneRepresentation ℂ G ν) (hA : A.toFiniteRepresentation.IsUnitary)
    (I : Subgroup G) [I.Normal] (g : G) {z : ℂ}
    (hz : (LocalFactor.WeilDeligne.eulerPolynomial A I g).IsRoot z) : ‖z‖ = 1 := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    change (LocalFactor.WeilDeligne.eulerPolynomial A I g).eval 0 = 0 at hz
    rw [← coeff_zero_eq_eval_zero, LocalFactor.WeilDeligne.eulerPolynomial_coeff_zero] at hz
    exact one_ne_zero hz
  obtain ⟨x, hx, -, -, he⟩ :=
    WeilPoleRegionUnitary.exists_kernel_eigenvector_of_eulerPolynomial_eval_eq_zero A I g hz0 hz
  obtain ⟨b⟩ := (FiniteRepresentation.isUnitary_iff_isUnitarizable _).mp hA
  have hinv := Henniart.Extension.norm_eq_one_of_invariantPositiveForm b hx he
  rw [norm_inv] at hinv
  exact inv_eq_one.mp hinv

section Support

open Langlands.VirtualRepresentation.PadicSupercuspidal

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

private local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology

private local instance (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- For two irreducible representations with unitary supercuspidal supports,
JPSS (8.4) puts every root of the pair polynomial on the unit circle. -/
theorem isPadicSymmetricLPolynomial_roots_of_unitarySupport
    {ψ : Correspondence.NontrivialAdditiveCharacter F}
    {ν : Correspondence.LocalAdditiveHaarMeasure F}
    (hν : Correspondence.IsSelfDualMeasure F ψ ν) {r t : ℕ}
    (A : Correspondence.AutomorphicObject.{uF, uF} F r.succPNat)
    (B : Correspondence.AutomorphicObject.{uF, uF} F t.succPNat)
    {x y : UnitaryLattice.{uF, uF} F}
    (hx : IsUnitaryLatticeSupport F A.obj x) (hy : IsUnitaryLatticeSupport F B.obj y)
    {P : ℂ[X]} (hP : IsPadicSymmetricLPolynomial F ψ ν A.obj.representation
      B.obj.representation P) {z : ℂ} (hz : P.IsRoot z) : ‖z‖ = 1 := by
  let := F.canonicalTopologicalData.topology
  obtain ⟨D, σ, hσ, ⟨eσ⟩⟩ := exists_equiv_unitarizableSupercuspidalProduct r.succ_pos hx
  obtain ⟨E, τ, hτ, ⟨eτ⟩⟩ := exists_equiv_unitarizableSupercuspidalProduct t.succ_pos hy
  obtain ⟨P', Q, hP', hQ, hprod⟩ := TemperedLFactorStatement.blockShape F ψ ⟨ν, hν⟩
    temperedLFactor.{uF, uF, uF} D E (fun i => (σ i).obj.representation)
    (fun j => (τ j).obj.representation) (fun i => (σ i).property.1)
    (fun i => Classification.unitarizableSupercuspidal_isSquareIntegrable F
      (D.positive i) (σ i) (hσ i))
    (fun j => (τ j).property.1)
    (fun j => Classification.unitarizableSupercuspidal_isSquareIntegrable F
      (E.positive j) (τ j) (hτ j))
  rw [((IsPadicSymmetricLPolynomial.congr_equiv eσ eτ).mp hP).unique hP', hprod] at hz
  change (∏ i, ∏ j, Q i j).eval z = 0 at hz
  simp only [eval_prod, Finset.prod_eq_zero_iff] at hz
  obtain ⟨i, -, j, -, hroot⟩ := hz
  exact isUnitaryBasisPairLPolynomial_root_norm hν
    (isUnitaryBasisPairLPolynomial_blockBasisClass (D.positive i) (E.positive j)
      (σ i) (τ j) (hσ i) (hτ j) (hQ i j)) hroot

end Support

end Langlands.Global.PoleComparison
