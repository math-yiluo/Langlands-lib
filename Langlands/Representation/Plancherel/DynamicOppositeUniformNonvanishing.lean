import Langlands.Representation.Plancherel.DynamicOppositeNonvanishing
import Langlands.Representation.Plancherel.DynamicOppositeUnitaryNonnegativity
import Langlands.Representation.Plancherel.RationalUnitaryNonvanishing

/-! # Strict positivity of `j_P` at unitary points from the Hermitian adjunction

Derived from Waldspurger IV.1 (10) (printed p.283) and the proof of IV.3 (6) (printed p.287).
For a vector `e` of the compact picture whose forward integral has a nonzero value at `1`, and
for unitary `χ`, `j(π ⊗ χ) (e, e) = (J_{P̄|P} e, J_{P̄|P} e)`. This module shows that the right
side is strictly positive at every unitary common regular point of the continuations.

* `compactTestVector`: the restriction to `K` of the section of `Ind_P A` supported on `P Q`
  with value `v` at `1`, for a compact open `Q ⊆ K`. Unramified twists are trivial on `P ∩ K`
  (`leviInflated_twist_apply_of_mem`), so this restriction is the same for every twist
  (`unramifiedLeviInductionCompactEquiv_sourceTestVector`).
* `compactIntertwiningOperator_compactTestVector_eval_one`: every intertwiner satisfying the
  standard integral relation sends `compactTestVector` to a vector with value `qν(S) • v` at
  `1`, independently of the twist.
* `RationalFunctionPosAt`: a rational function is regular at a point with a positive real
  value there.
* `continuedOperator_map_eq_of_eqOn` (generic): if a linear image of an operator family is
  constant on a nonempty open set, then the same linear image of its rational continuation
  takes that constant value at every regular point.
* `continuedCompositeRationalScalar_posAt` (generic): the strict form of
  `continuedCompositeRationalScalar_nonnegAt` for a definite form `sW` when the continued
  operator does not kill `v`.
* `exists_forwardCompactFamily_eval_one_eq`: a z-uniform form of IV.1 (10) for
  `J_{P̄|P}(z)` on the full convergence domain.
* `ConditionalDynamicOppositeUnitaryPositiveStatement` is the target: `j_P ≠ 0`, and at every
  unitary common regular point `j_P` and `j_P⁻¹` are regular with positive real values.
* `conditionalDynamicOppositeUnitaryPositive_of_hermitianAdjunction` proves the target from the
  Hermitian adjunction target `ConditionalDynamicOppositeHermitianAdjunctionStatement`.
-/

noncomputable section

universe u uV uW uX uG uI

open CategoryTheory AlgebraicGeometry MeasureTheory Filter Topology
open scoped CategoryTheory.MonObj NNReal ComplexConjugate
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

/-! ### Unramified twists are trivial on `P ∩ K` -/

section CompactTwist

open Aubert.General Induction StandardIntertwining

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hr : Continuous h.projection)
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (A : SmoothRep.{0, uG, uV} ℂ M)

/-- The image of `P ∩ K` in the Levi factor, a compact subgroup of `M`. -/
def compactLeviImage : Subgroup M :=
  (conjOpenSubgroup P K 1).toSubgroup.map h.projection

omit [LocallyCompactSpace G] in
include hP hK hr in
theorem isCompact_compactLeviImage : IsCompact (compactLeviImage h K : Set M) := by
  have hc := (isCompact_conjOpenSubgroup P hP K hK 1).image hr
  simpa only [compactLeviImage, Subgroup.coe_map, OpenSubgroup.coe_toSubgroup] using hc

omit [LocallyCompactSpace G] in
theorem projection_mem_compactLeviImage {p : P} (hp : (p : G) ∈ K) :
    h.projection p ∈ compactLeviImage h K :=
  Subgroup.mem_map_of_mem _
    (show p ∈ conjOpenSubgroup P K 1 by
      simpa only [mem_conjOpenSubgroup, inv_one, one_mul, mul_one] using hp)

include hP hK hr in
/-- The positive half-modulus of the Levi is trivial on the projection of `P ∩ K`. -/
theorem leviHalfCharacter_projection_eq_one {p : P} (hp : (p : G) ∈ K) :
    HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer (h.projection p) = 1 := by
  have hδ := RankinSelberg.LastRowReduction.eq_one_of_isCompact
    (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer)
    (Weil.continuous_of_open_kernel _
      (HaarModulus.isOpen_ker_closedRestrictCharacter U hU M h.levi_le_normalizer))
    (compactLeviImage h K) (isCompact_compactLeviImage h hP K hK hr)
    (projection_mem_compactLeviImage h K hp)
  let := hU.locallyCompactSpace
  change h.projection p ∈ (HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer).ker
  rw [HaarModulus.closedHalfCharacter_eq, HaarModulus.halfCharacter_ker]
  exact hδ

omit [LocallyCompactSpace G] in
include hP hK hr hν in
/-- Every unramified character is trivial on the projection of `P ∩ K`. -/
theorem unramifiedCharacter_projection_eq_one (z : unramifiedCharacters ν) {p : P}
    (hp : (p : G) ∈ K) : z.val (h.projection p) = 1 :=
  z.property ((mem_commonNormKernel ν _).mpr fun i =>
    RankinSelberg.LastRowReduction.eq_one_of_isCompact (ν i) (hν i) (compactLeviImage h K)
      (isCompact_compactLeviImage h hP K hK hr) (projection_mem_compactLeviImage h K hp))

include hP hK hr hν in
/-- On `P ∩ K`, the Levi-inflated action of every unramified twist is the untwisted action. -/
theorem leviInflated_twist_apply_of_mem (z : unramifiedCharacters ν) {p : P}
    (hp : (p : G) ∈ K) (w : A) :
    leviInflatedInducingRepresentation h hU
        (A.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z)) p w =
      A.representation (h.projection p) w := by
  change ((HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer (h.projection p) : ℂˣ) :
      ℂ) • (((z.val (h.projection p) : ℂˣ) : ℂ) • A.representation (h.projection p) w) = _
  rw [leviHalfCharacter_projection_eq_one h hU hP K hK hr hp,
    unramifiedCharacter_projection_eq_one h hP K hK hr ν hν z hp]
  simp

include hP hK hr hν in
/-- A vector fixed by the untwisted inflated action of `P ∩ Q`, for `Q ⊆ K`, is fixed by the
inflated action of every unramified twist. -/
theorem mem_fixedVectors_twist {Q : OpenSubgroup G} (hQK : (Q : Set G) ⊆ K) {v : A}
    (hv : v ∈ fixedVectors (A.representation.comp h.projection)
      (conjOpenSubgroup P Q 1).toSubgroup)
    (z : unramifiedCharacters ν) :
    v ∈ fixedVectors (leviInflatedInducingRepresentation h hU
        (A.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z)))
      (conjOpenSubgroup P Q 1).toSubgroup := by
  rw [fixedVectors, Representation.mem_invariants] at hv ⊢
  intro p
  have hpQ : ((p : P) : G) ∈ Q := by
    simpa only [inv_one, one_mul, mul_one] using mem_conjOpenSubgroup.mp p.property
  have hfix := hv p
  change leviInflatedInducingRepresentation h hU
    (A.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z)) (p : P) v = v
  rw [leviInflated_twist_apply_of_mem h hU hP K hK hr ν hν A z (hQK hpQ)]
  exact hfix

include hP hK hr hν in
/-- On `K`, the test vectors supported on `P Q` of all unramified twists agree, for `Q ⊆ K`. -/
theorem sourceTestVector_twist_eval_eq {Q : OpenSubgroup G} (hQ : IsCompact (Q : Set G))
    (hQK : (Q : Set G) ⊆ K) {v : A}
    (hv : v ∈ fixedVectors (A.representation.comp h.projection)
      (conjOpenSubgroup P Q 1).toSubgroup)
    (z z' : unramifiedCharacters ν) (k : K) :
    eval P (leviInflatedInducingRepresentation h hU
        (A.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z)))
      (sourceTestVector h hU (A.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z))
        Q hQ v (mem_fixedVectors_twist h hU hP K hK hr ν hν A hQK hv z)) (k : G) =
    eval P (leviInflatedInducingRepresentation h hU
        (A.twist z'.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z')))
      (sourceTestVector h hU (A.twist z'.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z'))
        Q hQ v (mem_fixedVectors_twist h hU hP K hK hr ν hν A hQK hv z')) (k : G) := by
  by_cases hk : ∃ p ∈ P, ∃ q ∈ Q, (k : G) = p * q
  · obtain ⟨p, hp, q, hq, hkpq⟩ := hk
    have hpK : ((⟨p, hp⟩ : P) : G) ∈ K := by
      have hpk : p = (k : G) * q⁻¹ := by rw [hkpq, mul_inv_cancel_right]
      change p ∈ K
      rw [hpk]
      exact K.mul_mem k.property (K.inv_mem (hQK hq))
    have hk' : (k : G) = ((⟨p, hp⟩ : P) : G) * ((⟨q, hq⟩ : Q) : G) := hkpq
    rw [hk', sourceTestVector_eval_mul, sourceTestVector_eval_mul,
      leviInflated_twist_apply_of_mem h hU hP K hK hr ν hν A z hpK,
      leviInflated_twist_apply_of_mem h hU hP K hK hr ν hν A z' hpK]
  · rw [sourceTestVector_eval_eq_zero _ _ _ _ _ _ _ _ hk,
      sourceTestVector_eval_eq_zero _ _ _ _ _ _ _ _ hk]

variable (hδ : IsUnimodularModulus U hU)
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))

/-- The compact picture of the test vector supported on `P Q` with value `v` at `1`, for
`Q ⊆ K`, computed in the untwisted induction. -/
def compactTestVector {Q : OpenSubgroup G} (hQ : IsCompact (Q : Set G))
    (hQK : (Q : Set G) ⊆ K) {v : A}
    (hv : v ∈ fixedVectors (A.representation.comp h.projection)
      (conjOpenSubgroup P Q 1).toSubgroup) :
    CompactInductionPicture h K A :=
  unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr 1 A
    (sourceTestVector h hU
      (A.twist (1 : unramifiedCharacters ν).val.toMonoidHom (unramifiedCharacter_isOpen_ker ν 1))
      Q hQ v (mem_fixedVectors_twist h hU hP K hK hr ν hν A hQK hv 1))

/-- The compact picture of the test vector of every unramified twist is `compactTestVector`. -/
theorem unramifiedLeviInductionCompactEquiv_sourceTestVector {Q : OpenSubgroup G}
    (hQ : IsCompact (Q : Set G)) (hQK : (Q : Set G) ⊆ K) {v : A}
    (hv : v ∈ fixedVectors (A.representation.comp h.projection)
      (conjOpenSubgroup P Q 1).toSubgroup)
    (z : unramifiedCharacters ν) :
    unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr z A
        (sourceTestVector h hU (A.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z))
          Q hQ v (mem_fixedVectors_twist h hU hP K hK hr ν hν A hQK hv z)) =
      compactTestVector h hU hP K hK hr ν hν A hδ hPK hQ hQK hv := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  exact sourceTestVector_twist_eval_eq h hU hP K hK hr ν hν A hQ hQK hv z 1 k

variable {P' U' : Subgroup G} (h' : IsSemidirectDecomposition P' M U')
  (hU' : IsClosed (U' : Set G)) (hδ' : IsUnimodularModulus U' hU')
  (hP' : IsClosed (P' : Set G)) (hP'K : ∀ g : G, ∃ p : P', ∃ k : K, g = (p : G) * (k : G))
  (hr' : Continuous h'.projection)
  [MeasurableSpace (QuotientSpace (U := U) U')] [BorelSpace (QuotientSpace (U := U) U')]
  (qν : Measure (QuotientSpace (U := U) U'))

/-- **Uniform value at `1`.** Every intertwiner `J` between the twisted inductions satisfying
the standard integral relation sends `compactTestVector` to a vector with value `qν(S) • v` at
`1`, where `S` is the orbit of `Q ∩ U'`: the value does not depend on the twist. -/
theorem compactIntertwiningOperator_compactTestVector_eval_one
    (hM : IsClosed (M : Set G)) {Q : OpenSubgroup G} (hQ : IsCompact (Q : Set G))
    (hQK : (Q : Set G) ⊆ K) {v : A}
    (hv : v ∈ fixedVectors (A.representation.comp h.projection)
      (conjOpenSubgroup P Q 1).toSubgroup)
    (hloc : HasSourceLocalProduct P U U' Q) (hqν : qν (sourceTestOrbit U U' Q) ≠ ⊤)
    (z : unramifiedCharacters ν)
    (J : (UnramifiedLeviInduction h hU ν z A).representation.IntertwiningMap
      (UnramifiedLeviInduction h' hU' ν z A).representation)
    (hJ : ∀ f, HasIntegral h hU U'
      (A.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z)) qν f
      (eval P' (leviInflatedInducingRepresentation h' hU'
        (A.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z))) (J f))) :
    eval _ _ (compactIntertwiningOperator h hU hδ K hP hK hPK ν hν hr
        h' hU' hδ' hP' hP'K hr' z A J
        (compactTestVector h hU hP K hK hr ν hν A hδ hPK hQ hQK hv)) 1 =
      ((qν (sourceTestOrbit U U' Q)).toReal : ℂ) • v := by
  rw [compactIntertwiningOperator_eval,
    ← unramifiedLeviInductionCompactEquiv_sourceTestVector h hU hP K hK hr ν hν A hδ hPK hQ hQK
      hv z, LinearEquiv.symm_apply_apply]
  exact HasIntegral.eval_one_sourceTestVector h hU U'
    (A.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z)) Q hQ v _ qν hM hloc hqν
    (hJ _)

end CompactTwist

/-! ### Strictly positive values of rational functions -/

section PosAt

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints G)]
  (hp : Continuous (rationalValuationImageProjection G))
  (hG : GroupScheme.IsConnectedReductive G)

set_option hygiene false in
local notation "RG" => unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul)

set_option hygiene false in
local notation "XG" => unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)

/-- A rational function `f` is regular at `z` with **positive real value** there: some
presentation `f = m / n` with `n(z) ≠ 0` has `m(z) / n(z) ∈ (0, ∞)`. -/
def RationalFunctionPosAt (f : rationalUnramifiedFunctionField G hp hG) (z : XG) : Prop :=
  ∃ m n : RG, n.val z ≠ 0 ∧
    f = algebraMap RG (rationalUnramifiedFunctionField G hp hG) m /
      algebraMap RG (rationalUnramifiedFunctionField G hp hG) n ∧
    ∃ r : ℝ, 0 < r ∧ m.val z / n.val z = (r : ℂ)

variable {G hp hG}

/-- A positive value is a nonnegative value. -/
theorem RationalFunctionPosAt.nonnegAt {f : rationalUnramifiedFunctionField G hp hG} {z : XG}
    (h : RationalFunctionPosAt G hp hG f z) : RationalFunctionNonnegAt G hp hG f z :=
  h.elim fun m hm => hm.elim fun n hn =>
    ⟨m, n, hn.1, hn.2.1, hn.2.2.elim fun r hr => ⟨r, hr.1.le, hr.2⟩⟩

/-- If `f` has a positive value at `z`, so does `f⁻¹`, namely the inverse value. -/
theorem RationalFunctionPosAt.inv {f : rationalUnramifiedFunctionField G hp hG} {z : XG}
    (h : RationalFunctionPosAt G hp hG f z) : RationalFunctionPosAt G hp hG f⁻¹ z := by
  obtain ⟨m, n, hn, hf, r, hr, hval⟩ := h
  have hm : m.val z ≠ 0 := by
    intro h0
    rw [h0, zero_div] at hval
    exact hr.ne' (Complex.ofReal_eq_zero.mp hval.symm)
  refine ⟨n, m, hm, by rw [hf, inv_div], r⁻¹, inv_pos.mpr hr, ?_⟩
  rw [← inv_div, hval, Complex.ofReal_inv]

/-- A rational function with a positive value at some point is nonzero. -/
theorem RationalFunctionPosAt.ne_zero {f : rationalUnramifiedFunctionField G hp hG} {z : XG}
    (h : RationalFunctionPosAt G hp hG f z) : f ≠ 0 := by
  obtain ⟨m, n, hn, hf, r, hr, hval⟩ := h
  intro h0
  have h1 : (1 : RG).val z ≠ 0 := by simp
  have hzero : f = algebraMap RG (rationalUnramifiedFunctionField G hp hG) 0 /
      algebraMap RG (rationalUnramifiedFunctionField G hp hG) 1 := by
    rw [h0, map_zero, zero_div]
  have he := rationalFunction_value_eq G hp hG hn h1 hf hzero
  rw [hval] at he
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply, zero_div] at he
  exact hr.ne' (Complex.ofReal_eq_zero.mp he)

end PosAt

/-! ### Linear images and positivity of continued operators -/

section ContinuedIdentity

open UnramifiedOperatorFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {X : Type uX} [AddCommGroup X] [Module ℂ X]
  {Ω Λ : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  {A : Ω → V →ₗ[ℂ] W} {B : Λ → W →ₗ[ℂ] V}

include hp hL in
/-- **Identity theorem for a linear image of a continued operator.** Let `p` continue the
operator family `A` on `Ω`, and let `E` be linear. If `E (A w v) = x` for all `w` in a nonempty
open `D ⊆ Ω`, then `E (p.continuedOperator z v) = x` at every regular point `z` of `p`. -/
theorem continuedOperator_map_eq_of_eqOn (p : RationalOperatorContinuationData Ω A)
    {D : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω) (E : W →ₗ[ℂ] X) (v : V) (x : X)
    (hE : ∀ (w) (hw : w ∈ D), E (A ⟨w, hDΩ hw⟩ v) = x) (z : p.regularRegion) :
    E (p.continuedOperator z v) = x := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun ℓ => ?_
  obtain ⟨a, ha⟩ := (isPolynomialOn_scalar_iff _).mp ((p.polynomial v).linearMap (ℓ ∘ₗ E))
  have hr : a - ℓ x • p.denominator = 0 := by
    apply rationalUnramifiedRegular_eq_zero_of_isOpen L hp hL _ hD hne
    intro w hw
    have h1 : ℓ (E (p.numerator w v)) = a.val w := ha ⟨w, Set.mem_univ _⟩
    have hc : p.numerator w v = p.denominator.val w • A ⟨w, hDΩ hw⟩ v :=
      LinearMap.congr_fun (p.clears ⟨w, hDΩ hw⟩) v
    rw [hc, map_smul, map_smul, hE w hw, smul_eq_mul] at h1
    simp only [Subalgebra.coe_sub, Subalgebra.coe_smul, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [← h1]
    ring
  have hz := congrArg (fun f : unramifiedRegularFunctions _ => f.val z.val) hr
  simp only [Subalgebra.coe_sub, Subalgebra.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    ZeroMemClass.coe_zero, Pi.zero_apply] at hz
  have h1 : ℓ (E (p.numerator z.val v)) = a.val z.val := ha ⟨z.val, Set.mem_univ _⟩
  have hd : p.denominator.val z.val ≠ 0 := z.property
  change ℓ (E ((p.denominator.val z.val)⁻¹ • p.numerator z.val v) - x) = 0
  rw [map_sub, map_smul, map_smul, h1, smul_eq_mul]
  field_simp
  linear_combination hz

include hp hL in
/-- **Positivity of the extracted coefficient at self-dual points.** In the situation of
`continuedCompositeRationalScalar_nonnegAt`, assume moreover that `sW` is definite and that
`p.continuedOperator z v ≠ 0`. Then the extracted coefficient has a positive real value at
`z`. -/
theorem continuedCompositeRationalScalar_posAt
    (sV : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (sW : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hsV : ∀ u : V, ∃ r : ℝ, 0 ≤ r ∧ sV u u = (r : ℂ))
    (hsW : ∀ u : W, ∃ r : ℝ, 0 ≤ r ∧ sW u u = (r : ℂ))
    (hsWdef : ∀ u : W, u ≠ 0 → sW u u ≠ 0)
    (p : RationalOperatorContinuationData Ω A) (q : RationalOperatorContinuationData Λ B)
    {D : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω)
    (hdag : ∀ w ∈ D, unramifiedConjInv _ w ∈ Λ)
    (hadj : ∀ (w) (hw : w ∈ D) (v : V) (w' : W),
      sW (A ⟨w, hDΩ hw⟩ v) w' = sV v (B ⟨unramifiedConjInv _ w, hdag w hw⟩ w'))
    (hΩ : Ω.Nonempty) (hΛ : Λ.Nonempty) (v : V) (hv : sV v v ≠ 0)
    (f : rationalUnramifiedFunctionField L hp hL)
    (hf : f = continuedCompositeRationalScalar L hp hL p q hΩ hΛ v ((sV v v)⁻¹ • sV v))
    (z : unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))
    (hz : z ∈ p.regularRegion ∩ q.regularRegion) (hzdag : unramifiedConjInv _ z = z)
    (hpz : p.continuedOperator ⟨z, hz.1⟩ v ≠ 0) :
    RationalFunctionPosAt L hp hL f z := by
  obtain ⟨a, b, -, hbreg, hab, hval⟩ :=
    continuedCompositeRationalScalar_spec L hp hL p q hΩ hΛ v ((sV v v)⁻¹ • sV v)
  refine ⟨a, b, hbreg ⟨z, hz⟩, hf.trans hab, ?_⟩
  have hz' : unramifiedConjInv _ (⟨z, hz.1⟩ : p.regularRegion).val ∈ q.regularRegion := by
    change unramifiedConjInv _ z ∈ q.regularRegion
    rw [hzdag]
    exact hz.2
  have hadjz := continuedOperator_adjoint L hp hL sV sW p q hD hne hDΩ hdag hadj
    ⟨z, hz.1⟩ hz' v (p.continuedOperator ⟨z, hz.1⟩ v)
  have hcongr : q.continuedOperator ⟨unramifiedConjInv _ z, hz'⟩ =
      q.continuedOperator ⟨z, hz.2⟩ := continuedOperator_congr L q hz' hz.2 hzdag
  rw [hcongr] at hadjz
  obtain ⟨r1, hr1, he1⟩ := hsV v
  obtain ⟨r2, hr2, he2⟩ := hsW (p.continuedOperator ⟨z, hz.1⟩ v)
  have hr1' : r1 ≠ 0 := by
    rintro rfl
    exact hv (he1.trans (by simp))
  have hr2' : r2 ≠ 0 := by
    rintro rfl
    exact hsWdef _ hpz (he2.trans (by simp))
  refine ⟨r1⁻¹ * r2, mul_pos (inv_pos.mpr (lt_of_le_of_ne hr1 (Ne.symm hr1')))
    (lt_of_le_of_ne hr2 (Ne.symm hr2')), ?_⟩
  rw [← hval ⟨z, hz⟩]
  change (sV v v)⁻¹ * sV v (q.continuedOperator ⟨z, hz.2⟩
    (p.continuedOperator ⟨z, hz.1⟩ v)) = _
  rw [← hadjz, he1, he2]
  push_cast
  rfl

end ContinuedIdentity

/-! ### Evaluation at the identity on the compact picture -/

section EvalOne

open Aubert.General Induction

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U) (K : OpenSubgroup G)
  (A : SmoothRep.{0, uG, uV} ℂ M)

/-- Evaluation at `1` on the compact picture, as a linear map. -/
def compactPictureEvalOne : CompactInductionPicture h K A →ₗ[ℂ] A where
  toFun φ := eval _ _ φ 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
@[simp]
theorem compactPictureEvalOne_apply (φ : CompactInductionPicture h K A) :
    compactPictureEvalOne h K A φ = eval _ _ φ 1 := rfl

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- A nonzero vector of the compact picture has a nonzero value at some point of `K`. -/
theorem CompactInductionPicture.exists_eval_ne_zero {φ : CompactInductionPicture h K A}
    (hφ : φ ≠ 0) : ∃ k : K, eval _ _ φ k ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hφ
  apply Subtype.ext
  apply Subtype.ext
  funext k
  exact hall k

end EvalOne

/-! ### Dynamic opposite parabolics: a forward test vector with constant value at `1` -/

section UniformForward

open Aubert.General Induction StandardIntertwining UnramifiedOperatorFamily
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open DynamicOppositeNonvanishing

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarMeasurableSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarBorelSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarMeasurableSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarBorelSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarMeasurableSpace3
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarBorelSpace3
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarMeasurableSpace4
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarBorelSpace4
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarMeasurableSpace5
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarBorelSpace5
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarMeasurableSpace6
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarBorelSpace6

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppK : ∀ g : RationalPoint F G.X,
    ∃ p : oppositeParabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

/-- **A uniform form of IV.1 (10).** For every vector `v` of `A` there are a vector `e` of the
compact picture of `Ind_P A` and a nonzero constant `c` such that, at every parameter `z` of the
full convergence domain, the forward integral `J_{P̄|P}(z) e` has value `c • v` at `1`. Here `e`
is the restriction to `K` of the section supported on `P Q` with value `v` at `1`, for a small
compact open subgroup `Q` with an Iwahori factorization; `c` is the mass of the orbit of
`Q ∩ U(χ⁻¹)` in the quotient by `U(χ) ∩ U(χ⁻¹)`. -/
theorem exists_forwardCompactFamily_eval_one_eq (v : A) :
    ∃ e : CompactInductionPicture (decomposition χ) K A, ∃ c : ℂ, c ≠ 0 ∧
      ∀ z : forwardFullDomainRegion χ K hK A,
        compactPictureEvalOne (oppositeDecomposition χ) K A
          (conditionalForwardCompactFamily χ hRefl hCST hG K hK hPK hOppK A z e) = c • v := by
  obtain ⟨S, hS⟩ := A.isSmooth v
  obtain ⟨W, hW, hWQ⟩ := exists_nhds_fixedVectors_comp_projection (decomposition χ)
    (projection_continuous χ) A.representation S v hS
  obtain ⟨Q, hQc, hQW, hfac⟩ := exists_factored_compactOpen_subset χ hG
    (Filter.inter_mem hW (K.isOpen.mem_nhds K.one_mem))
  have hQK : (Q : Set (RationalPoint F G.X)) ⊆ K := fun x hx => (hQW hx).2
  have hv := hWQ Q fun x hx => (hQW hx).1
  have hmass := (forwardQuotientMeasure_isCompatible χ K hK).compactOpenQuotientOrbit_mass
    (targetCompactOpen (oppositeRadical χ) Q)
    (targetCompactOpen_isCompact (oppositeRadical χ) (oppositeRadical_isClosed χ) Q hQc)
  refine ⟨compactTestVector (decomposition χ) (radical_isClosed χ) (parabolic_isClosed χ) K hK
      (projection_continuous χ) (leviNormCharacters χ)
      (fun ψ => (normCharacters_continuous χ ψ).comp (parameterHomeomorph χ).symm.continuous)
      A (radical_unimodular χ hG) hPK hQc hQK hv,
    ((forwardQuotientMeasure χ K hK
      (sourceTestOrbit (radical χ) (oppositeRadical χ) Q)).toReal : ℂ),
    Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hmass.1.ne' hmass.2.ne).ne', fun z => ?_⟩
  have key := compactIntertwiningOperator_compactTestVector_eval_one (decomposition χ)
    (radical_isClosed χ) (parabolic_isClosed χ) K hK (projection_continuous χ)
    (leviNormCharacters χ)
    (fun ψ => (normCharacters_continuous χ ψ).comp (parameterHomeomorph χ).symm.continuous) A
    (radical_unimodular χ hG) hPK (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadical_unimodular χ hG) (oppositeParabolic_isClosed χ) hOppK
    (oppositeProjection_continuous χ) (forwardQuotientMeasure χ K hK) (levi_isClosed χ) hQc hQK
    hv (forward_hasSourceLocalProduct χ Q hfac) hmass.2.ne (parameterTransport χ z.val)
    (conditionalForwardFamily χ K hK hRefl hCST hG A z)
    (conditionalForwardFamily_spec χ K hK hRefl hCST hG A z)
  rw [compactPictureEvalOne_apply]
  unfold conditionalForwardCompactFamily
  refine Eq.trans ?_ (key.trans ?_)
  · congr 1
  · rfl

end UniformForward

/-! ### The target and its reduction to the Hermitian adjunction -/

section Target

open Aubert.General Induction UnramifiedOperatorFamily
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  hermitianAdjunctionPointMeasurable
  hermitianAdjunctionPointBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppK : ∀ g : RationalPoint F G.X,
    ∃ p : oppositeParabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
  (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)

/-- The continuations of the forward and reverse integrals have a common regular point which is
a unitary unramified character: a product of two nonzero regular functions does not vanish
identically on the unitary characters. -/
theorem exists_unitary_mem_regularRegion_inter
    (hΩ : (forwardFullDomainRegion χ K hK A).Nonempty)
    (hΛ : (reverseFullDomainRegion χ K hK A).Nonempty) :
    ∃ z : unramifiedCharacters (normCharacters χ), z ∈ p.regularRegion ∩ q.regularRegion ∧
      z.val ∈ unitaryUnramifiedCharacters (normCharacters χ) := by
  have hpd : p.denominator ≠ 0 := fun h0 => hΩ.elim fun w hw =>
    p.denominator_nonzero ⟨w, hw⟩ (by rw [h0]; rfl)
  have hqd : q.denominator ≠ 0 := fun h0 => hΛ.elim fun w hw =>
    q.denominator_nonzero ⟨w, hw⟩ (by rw [h0]; rfl)
  obtain ⟨w, hw⟩ := rationalUnramifiedRegular_exists_unitary_finset_ne_zero (parameterScheme χ)
    (parameterScheme_isConnectedReductive χ hG) Finset.univ ![p.denominator, q.denominator]
    (fun j _ => by fin_cases j; exacts [hpd, hqd])
  exact ⟨⟨w.val, w.property.1⟩, ⟨hw 0 (Finset.mem_univ _), hw 1 (Finset.mem_univ _)⟩,
    w.property⟩

/-- **Strict positivity at one unitary point.** Assume the Hermitian adjunction of IV.1 (11)
on the convergence domains, the splitting of `P ∩ K` and `P̄ ∩ K` through `M`, an invariant
positive form on `A` and a nonzero vector of `A`. Then at every unitary common regular point `z`
of the continuations, `j_P` is regular with a positive real value. -/
theorem conditionalCanonicalRationalScalar_posAt
    (H : ConditionalDynamicOppositeHermitianAdjunctionStatement.{u, uV})
    (hKsplit : ∀ p : parabolic χ, (p : RationalPoint F G.X) ∈ K →
      ((decomposition χ).projection p : RationalPoint F G.X) ∈ K)
    (hOppKsplit : ∀ p : oppositeParabolic χ, (p : RationalPoint F G.X) ∈ K →
      ((oppositeDecomposition χ).projection p : RationalPoint F G.X) ∈ K)
    (b : InvariantPositiveForm A.representation)
    {DForward DReverse : Set (unramifiedCharacters (normCharacters χ))}
    (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
    (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
    (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
    (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
    {D : Set (unramifiedCharacters (normCharacters χ))}
    (hD : IsOpen D) (hne : D.Nonempty)
    (hi : ∀ z ∈ D,
      (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
        (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)
    (hdag : ∀ z ∈ DForward,
      unramifiedConjInv (normCharacters χ) z ∈ reverseFullDomainRegion χ K hK A)
    (v : A) (hv0 : v ≠ 0)
    (z : unramifiedCharacters (normCharacters χ))
    (hz : z ∈ p.regularRegion ∩ q.regularRegion)
    (hzu : z.val ∈ unitaryUnramifiedCharacters (normCharacters χ)) :
    RationalFunctionPosAt (parameterScheme χ) (parameterProjection_continuous χ)
      (parameterScheme_isConnectedReductive χ hG)
      (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
        p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi) z :=
  (exists_forwardCompactFamily_eval_one_eq χ hRefl hCST hG K hK hPK hOppK A v).elim fun e he =>
  he.elim fun c hc =>
  have hcv : c • v ≠ 0 := smul_ne_zero hc.1 hv0
  have hpe : compactPictureEvalOne (oppositeDecomposition χ) K A
      (p.continuedOperator ⟨z, hz.1⟩ e) = c • v :=
    continuedOperator_map_eq_of_eqOn (parameterScheme χ) (parameterProjection_continuous χ)
      (parameterScheme_isConnectedReductive χ hG) p hDForward hneForward hDForwardΩ
      (compactPictureEvalOne (oppositeDecomposition χ) K A) e (c • v)
      (fun w hw => hc.2 ⟨w, hDForwardΩ hw⟩) ⟨z, hz.1⟩
  have hpz : p.continuedOperator ⟨z, hz.1⟩ e ≠ 0 := fun h0 => hcv (by rw [← hpe, h0, map_zero])
  have he0 : e ≠ 0 := fun h0 => hpz (by rw [h0, map_zero])
  have hse := compactPictureHermitianPairing_self_ne_zero (decomposition χ) K hK A b he0
  continuedCompositeRationalScalar_posAt (parameterScheme χ)
    (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
    (compactPictureSesq (decomposition χ) K hK A b)
    (compactPictureSesq (oppositeDecomposition χ) K hK A b)
    (compactPictureHermitianPairing_self (decomposition χ) K hK A b)
    (compactPictureHermitianPairing_self (oppositeDecomposition χ) K hK A b)
    (fun _ hu => compactPictureHermitianPairing_self_ne_zero (oppositeDecomposition χ) K hK A b hu)
    p q hDForward hneForward hDForwardΩ hdag
    (fun w hw φ φ' => H χ hRefl hCST hG K hK hPK hOppK hKsplit hOppKsplit A b
      ⟨w, hDForwardΩ hw⟩ (hdag w hw) φ φ')
    (hneForward.mono hDForwardΩ) (hneReverse.mono hDReverseΩ) e hse _
    (conditionalCanonicalRationalScalar_eq_extraction χ hRefl hCST hG K hK hPK hOppK A
      p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi e
      ((compactPictureSesq (decomposition χ) K hK A b e e)⁻¹ •
        compactPictureSesq (decomposition χ) K hK A b e)
      (inv_mul_cancel₀ hse))
    z hz (unramifiedConjInv_eq_self_of_mem_unitary _ hzu) hpz

/-- **Positivity of `j_P` on the unitary axis.** Under the hypotheses of
`conditionalCanonicalRationalScalar_posAt`, `j_P ≠ 0`, and at every unitary common regular
point both `j_P` and `j_P⁻¹` are regular with positive real values. -/
theorem conditionalCanonicalRationalScalar_unitaryPositive
    (H : ConditionalDynamicOppositeHermitianAdjunctionStatement.{u, uV})
    (hKsplit : ∀ p : parabolic χ, (p : RationalPoint F G.X) ∈ K →
      ((decomposition χ).projection p : RationalPoint F G.X) ∈ K)
    (hOppKsplit : ∀ p : oppositeParabolic χ, (p : RationalPoint F G.X) ∈ K →
      ((oppositeDecomposition χ).projection p : RationalPoint F G.X) ∈ K)
    (b : InvariantPositiveForm A.representation)
    {DForward DReverse : Set (unramifiedCharacters (normCharacters χ))}
    (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
    (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
    (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
    (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
    {D : Set (unramifiedCharacters (normCharacters χ))}
    (hD : IsOpen D) (hne : D.Nonempty)
    (hi : ∀ z ∈ D,
      (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
        (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)
    (hdag : ∀ z ∈ DForward,
      unramifiedConjInv (normCharacters χ) z ∈ reverseFullDomainRegion χ K hK A)
    (v : A) (hv0 : v ≠ 0) :
    conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
        p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi ≠ 0 ∧
      ∀ z : unramifiedCharacters (normCharacters χ),
        z ∈ p.regularRegion ∩ q.regularRegion →
        z.val ∈ unitaryUnramifiedCharacters (normCharacters χ) →
        RationalFunctionPosAt (parameterScheme χ) (parameterProjection_continuous χ)
            (parameterScheme_isConnectedReductive χ hG)
            (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
              p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi) z ∧
          RationalFunctionPosAt (parameterScheme χ) (parameterProjection_continuous χ)
            (parameterScheme_isConnectedReductive χ hG)
            (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
              p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi)⁻¹ z :=
  have hpos := fun z hz hzu => conditionalCanonicalRationalScalar_posAt χ hRefl hCST hG K hK
    hPK hOppK A p q H hKsplit hOppKsplit b hDForward hneForward hDForwardΩ hDReverse hneReverse
    hDReverseΩ hD hne hi hdag v hv0 z hz hzu
  ⟨(exists_unitary_mem_regularRegion_inter χ hRefl hCST hG K hK hPK hOppK A p q
      (hneForward.mono hDForwardΩ) (hneReverse.mono hDReverseΩ)).elim
      fun z hz => (hpos z hz.1 hz.2).ne_zero,
    fun z hz hzu => ⟨hpos z hz hzu, (hpos z hz hzu).inv⟩⟩

/-- **Target (strict positivity of `j_P` on the unitary axis).** Let `χ` be a cocharacter of `G`,
`P = P_G(χ)`, `P̄ = P_G(χ⁻¹)` and `M = Z_G(χ)`. Let `K` be a compact open subgroup with
`G = P K = P̄ K` whose intersections with `P` and `P̄` factor through `M`, and let `A` be a
unitarizable smooth representation of `M(F)`. Take the conditional data of the canonical scalar
`j_P` of `J_{P|P̄} J_{P̄|P}`, and assume that `z ↦ z† = z̄⁻¹` maps the open set `DForward` of
the data, inside the full convergence domain of `J_{P̄|P}`, into the full convergence domain of
`J_{P|P̄}`. Then `j_P ≠ 0`, and at every unitary unramified character `z` where both
continuations are regular, `j_P` and `j_P⁻¹` are regular with positive real values. -/
def ConditionalDynamicOppositeUnitaryPositiveStatement : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hPK : ∀ g : RationalPoint F G.X,
      ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK : ∀ g : RationalPoint F G.X,
      ∃ p : oppositeParabolic χ, ∃ k : K,
        g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (_hKsplit : ∀ p : parabolic χ, (p : RationalPoint F G.X) ∈ K →
      ((decomposition χ).projection p : RationalPoint F G.X) ∈ K)
    (_hOppKsplit : ∀ p : oppositeParabolic χ, (p : RationalPoint F G.X) ∈ K →
      ((oppositeDecomposition χ).projection p : RationalPoint F G.X) ∈ K)
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (_hA : IsUnitarizable A.representation)
    (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
    (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)
    {DForward DReverse : Set (unramifiedCharacters (normCharacters χ))}
    (_hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
    (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
    (_hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
    (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
    {D : Set (unramifiedCharacters (normCharacters χ))}
    (_hD : IsOpen D) (hne : D.Nonempty)
    (hi : ∀ z ∈ D,
      (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
        (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)
    (_hdag : ∀ z ∈ DForward,
      unramifiedConjInv (normCharacters χ) z ∈ reverseFullDomainRegion χ K hK A),
    conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
        p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi ≠ 0 ∧
      ∀ z : unramifiedCharacters (normCharacters χ),
        z ∈ p.regularRegion ∩ q.regularRegion →
        z.val ∈ unitaryUnramifiedCharacters (normCharacters χ) →
        RationalFunctionPosAt (parameterScheme χ) (parameterProjection_continuous χ)
            (parameterScheme_isConnectedReductive χ hG)
            (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
              p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi) z ∧
          RationalFunctionPosAt (parameterScheme χ) (parameterProjection_continuous χ)
            (parameterScheme_isConnectedReductive χ hG)
            (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
              p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi)⁻¹ z

/-- **Reduction.** The Hermitian adjunction of IV.1 (11) on the convergence domains implies the
strict positivity of `j_P` at unitary common regular points, and `j_P ≠ 0`. The nonzero vector
of `A` is a value of a compact-picture vector with a normalized coefficient. -/
theorem conditionalDynamicOppositeUnitaryPositive_of_hermitianAdjunction
    (H : ConditionalDynamicOppositeHermitianAdjunctionStatement.{u, uV}) :
    ConditionalDynamicOppositeUnitaryPositiveStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ χ hRefl hCST hG K hK hPK hOppK hKsplit hOppKsplit A hA p q
    DForward DReverse hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
    D hD hne hi hdag
  exact hA.elim fun b =>
    (exists_normalized_compactCoefficient (χ := χ) (hG := hG) (K := K) (hK := hK)
      (hPK := hPK) (A := A) (hne := hne) (hi := hi)).elim fun φ hφ =>
    hφ.elim fun ℓ0 hℓ0 =>
    have hφ0 : φ ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hℓ0
      exact zero_ne_one hℓ0
    (CompactInductionPicture.exists_eval_ne_zero (decomposition χ) K A hφ0).elim fun k hk =>
    conditionalCanonicalRationalScalar_unitaryPositive χ hRefl hCST hG K hK hPK hOppK A p q H
      hKsplit hOppKsplit b hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
      hD hne hi hdag _ hk

end Target

end Langlands.Plancherel
