import Langlands.Representation.Plancherel.RationalOperatorPolesFromZeroFibers

/-! # Cancellation on full convergence regions stable under unitary twists -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
set_option quotPrecheck false

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel.UnramifiedOperatorFamily

universe u uV uW uJ

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (H : GroupScheme (Spec (CommRingCat.of F))) [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  (hH : IsConnectedReductive H)

local instance pointTopology : TopologicalSpace (rationalPoints H) := rationalPointTopology F H.X

set_option hygiene false in
local notation "ν" => fun a => (rationalNormCharacters H a).toMul
local notation "X" => unramifiedCharacters ν
local notation "Xu" => unitaryUnramifiedCharacters ν
local notation "R" => unramifiedRegularFunctions ν
local notation "hp" => continuous_rationalValuationImageProjection H

private theorem basisCoordinateRoot_dvd_of_unitary_zero {n : ℕ}
    (B : Module.Basis (Fin (n + 1)) ℤ (Additive (rationalDiscreteValuationImage H)))
    (a : Circle) (b : R)
    (hzero : ∀ z : Xu,
      (rationalUnramifiedBasisCoordinateRoot H B (Circle.toUnits a)).val
          (unitaryToUnramified H z) = 0 → b.val (unitaryToUnramified H z) = 0) :
    rationalUnramifiedBasisCoordinateRoot H B (Circle.toUnits a) ∣ b := by
  let e := rationalUnramifiedBasisLaurentEquiv H B
  apply (map_dvd_iff e.symm).mp
  change e.symm (e (finiteLaurentCoordinateRoot n (Circle.toUnits a))) ∣ e.symm b
  rw [AlgEquiv.symm_apply_apply]
  apply finiteLaurentCoordinateRoot_dvd_of_eval_unitary_open (Circle.toUnits a) (e.symm b)
    (U := Set.univ) isOpen_univ Set.univ_nonempty
  intro c _
  let z := rationalUnitaryParameterOfBasis H B (Fin.cons a c)
  have hz : (rationalUnramifiedBasisCoordinateRoot H B (Circle.toUnits a)).val
      (unitaryToUnramified H z) = 0 := by
    change rationalUnitaryRegularRestriction H
      (rationalUnramifiedBasisCoordinateRoot H B (Circle.toUnits a)) z = 0
    rw [rationalUnramifiedBasisCoordinateRoot_eval_cons H B (Circle.toUnits a) a c]
    exact sub_self _
  have he := rationalUnramifiedBasisLaurentEquiv_eval_unitary H B (Fin.cons a c) (e.symm b)
  change rationalUnitaryRegularRestriction H (e (e.symm b)) z = _ at he
  rw [AlgEquiv.apply_symm_apply] at he
  have hc : (fun i => Circle.toUnits ((Fin.cons a c : Fin (n + 1) → Circle) i)) =
      Fin.cons (Circle.toUnits a) (fun i => Circle.toUnits (c i)) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [← hc, ← he]
  exact hzero z hz

include hH in
private theorem prime_dvd_of_complex_and_unitary_zeros (r g b : R) (hr : Prime r)
    (hr₀ : r.val (1 : X) = 0) (G : RationalUnitaryPoleFactorization H g)
    (hcomplex : ∀ z : X, r.val z = 0 → g.val z ≠ 0 → b.val z = 0)
    (hunitary : ∀ z : Xu, r.val (unitaryToUnramified H z) = 0 →
      b.val (unitaryToUnramified H z) = 0) : r ∣ b := by
  let : IsDomain R := rationalUnramifiedRegularFunctions_isDomain H hp hH
  by_cases hrg : r ∣ g
  · let ev := UnramifiedNormalized.evaluation ν (1 : X)
    have hn : ¬ r ∣ G.remainder := by
      intro h
      have hd := map_dvd ev h
      change r.val (1 : X) ∣ G.remainder.val (1 : X) at hd
      rw [hr₀, zero_dvd_iff] at hd
      exact G.remainder_nonzero (1 : Xu) hd
    have hprod : r ∣ rationalUnitaryPoleProduct H G.poles :=
      (hr.dvd_mul.mp (G.factorization ▸ hrg)).resolve_right hn
    obtain ⟨f, hf, hd⟩ := hr.dvd_prod_iff.mp hprod
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hf
    let root := rationalUnramifiedBasisCoordinateRoot H s.basis (Circle.toUnits s.value)
    have hroot : Prime root :=
      (MulEquiv.prime_iff (rationalUnramifiedBasisLaurentEquiv H s.basis).toMulEquiv).mpr
        (finiteLaurentCoordinateRoot_prime s.dimension (Circle.toUnits s.value))
    have hdiv : r ∣ root := hr.dvd_of_dvd_pow hd
    apply hdiv.trans
    apply basisCoordinateRoot_dvd_of_unitary_zero H s.basis s.value b
    intro z hz
    obtain ⟨c, hc⟩ := (hr.associated_of_dvd hroot hdiv).symm.dvd
    have hz' := congrArg (fun f : R => f.val (unitaryToUnramified H z)) hc
    change r.val (unitaryToUnramified H z) = _ at hz'
    change r.val (unitaryToUnramified H z) =
      root.val (unitaryToUnramified H z) * c.val (unitaryToUnramified H z) at hz'
    exact hunitary z (by simpa only [root, hz, zero_mul] using hz')
  · have hd := rationalUnramifiedLocalHypersurfaceDivisibility H hp hH Set.univ r (g * b)
      isOpen_univ hr.irreducible ⟨1, Set.mem_univ _, hr₀⟩ (by
        intro z _ hz
        change g.val z * b.val z = 0
        rcases eq_or_ne (g.val z) 0 with hg | hg
        · rw [hg, zero_mul]
        · rw [hcomplex z hz hg, mul_zero])
    exact (hr.dvd_mul.mp hd).resolve_left hrg

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {Ω D : Set (unramifiedCharacters (fun a => (rationalNormCharacters H a).toMul))}
  (J : Ω → V →ₗ[ℂ] W) (hDΩ : D ⊆ Ω)

private def restrictFamily (z : D) : V →ₗ[ℂ] W := J ⟨z.val, hDΩ z.property⟩

include hH in
private theorem clears_on_full
    (hD : IsOpen D) (hne : D.Nonempty)
    (htwist : ∀ (τ : Ω) (z : Xu), τ.val * unitaryToUnramified H z ∈ Ω)
    {I : Type uJ} (tests : I → W →ₗ[ℂ] ℂ)
    (hsep : ∀ x y : W, (∀ i, tests i x = tests i y) → x = y)
    (hcont : ∀ (τ : Ω) (v : V) (i : I), Continuous (fun z : Xu =>
      tests i (J ⟨τ.val * unitaryToUnramified H z, htwist τ z⟩ v)))
    (q : RationalOperatorContinuationData D (restrictFamily H J hDΩ))
    (a : R) (ha : a ≠ 0) (hpoly : IsPolynomialOperatorOn Ω (fun z => a.val z.val • J z)) :
    ∀ τ : Ω, q.numerator τ.val = q.denominator.val τ.val • J τ := by
  have hcross (z : Ω) : a.val z.val • q.numerator z.val =
      q.denominator.val z.val • (a.val z.val • J z) := by
    apply LinearMap.ext
    intro v
    have h := rationalUnramifiedPolynomial_eq_zero_of_isOpen H hp hH hD hne hDΩ
      (fun w : Ω => a.val w.val • q.numerator w.val v -
        q.denominator.val w.val • (a.val w.val • J w v))
      ((((q.polynomial v).restrict (Set.subset_univ Ω)).regular_smul a).sub
        ((hpoly v).regular_smul q.denominator)) (by
          intro w hw
          let t : D := ⟨w, hw⟩
          change a.val w • q.numerator w v - q.denominator.val w •
            (a.val w • J ⟨w, hDΩ hw⟩ v) = 0
          rw [LinearMap.congr_fun (q.clears t) v, LinearMap.smul_apply, smul_smul,
            smul_smul, mul_comm (a.val w)]
          exact sub_self _) z
    exact sub_eq_zero.mp h
  intro τ
  apply LinearMap.ext
  intro v
  apply hsep
  intro i
  let c (w : Xu) : X := τ.val * unitaryToUnramified H w
  let j (w : Xu) : Ω := ⟨c w, htwist τ w⟩
  let f (w : Xu) : ℂ := tests i (q.numerator (c w) v)
  let g (w : Xu) : ℂ := q.denominator.val (c w) * tests i (J (j w) v)
  have hc : Continuous c := continuous_const.mul
    (continuous_subtype_val.subtype_mk (fun w : Xu => w.property.1))
  have hf : Continuous f := (continuous_of_polynomial_univ (fun z => tests i (q.numerator z v))
    ((q.polynomial v).linearMap (tests i))).comp hc
  have hg : Continuous g := ((continuous_unramifiedRegularFunction ν q.denominator).comp hc).mul
    (hcont τ v i)
  let tr := unramifiedRegularTranslation ν τ.val
  have hd := ActualCommonLeviV3.dense_rationalUnitaryRegularRestriction_ne_zero H hH
    (tr a) (by exact fun e => ha (tr.injective (e.trans (map_zero tr).symm)))
  change Dense {w : Xu | a.val (c w) ≠ 0} at hd
  have he : {w : Xu | a.val (c w) ≠ 0} ⊆ {w : Xu | f w = g w} := by
    intro w hw
    have h := hcross (j w)
    rw [smul_comm (q.denominator.val (j w).val) (a.val (j w).val)] at h
    have h' := congrArg (fun T : V →ₗ[ℂ] W => tests i (T v))
      (smul_right_injective (V →ₗ[ℂ] W) hw h)
    change f w = g w
    simpa only [f, g, LinearMap.smul_apply, map_smul, smul_eq_mul] using h'
  have h := (closure_minimal he (isClosed_eq hf hg)) (hd (1 : Xu))
  change f (1 : Xu) = g (1 : Xu) at h
  change tests i (q.numerator (τ.val * 1) v) = q.denominator.val (τ.val * 1) *
    tests i (J ⟨τ.val * 1, htwist τ (1 : Xu)⟩ v) at h
  simpa only [mul_one, LinearMap.smul_apply, map_smul, smul_eq_mul] using h

include hH in
/-- An open continuation which has a uniform clearing identity on the full
region can be given a denominator avoiding all of that region. At each
convergent parameter the relevant exceptional hypersurfaces are those of a
factored regular scalar for its translate of the parameters. -/
theorem nonempty_fullDomainContinuation_of_unitary_translates
    (hD : IsOpen D) (hne : D.Nonempty)
    (htwist : ∀ (τ : Ω) (z : Xu), τ.val * unitaryToUnramified H z ∈ Ω)
    {I : Type uJ} (tests : I → W →ₗ[ℂ] ℂ)
    (hsep : ∀ x y : W, (∀ i, tests i x = tests i y) → x = y)
    (hcont : ∀ (τ : Ω) (v : V) (i : I), Continuous (fun z : Xu =>
      tests i (J ⟨τ.val * unitaryToUnramified H z, htwist τ z⟩ v)))
    (p : RationalOperatorContinuationData D (restrictFamily H J hDΩ))
    (a : R) (ha : a ≠ 0) (hpoly : IsPolynomialOperatorOn Ω (fun z => a.val z.val • J z))
    (hzero : ∀ (τ : Ω), ∃ g : R, Nonempty (RationalUnitaryPoleFactorization H g) ∧
      ∀ (q : RationalOperatorContinuationData D (restrictFamily H J hDΩ)) (z : X),
        g.val z ≠ 0 → q.denominator.val (τ.val * z) = 0 → q.numerator (τ.val * z) = 0) :
    Nonempty (RationalOperatorContinuationData Ω J) := by
  let : IsDomain R := rationalUnramifiedRegularFunctions_isDomain H hp hH
  let : UniqueFactorizationMonoid R := rationalUnramifiedRegularFunctions_uniqueFactorizationMonoid H hp hH
  let S : Set R := {b | ∃ q : RationalOperatorContinuationData D (restrictFamily H J hDΩ), q.denominator = b}
  obtain ⟨_, ⟨q, rfl⟩, hmin⟩ := (wellFounded_dvdNotUnit (α := R)).has_min S
    ⟨p.denominator, p, rfl⟩
  have hclears := clears_on_full H hH J hDΩ hD hne htwist tests hsep hcont q a ha hpoly
  refine ⟨⟨q.denominator, ?_, q.numerator, q.polynomial, hclears⟩⟩
  intro τ hτ
  obtain ⟨fs, hfs, hassoc⟩ := rationalUnramifiedRegularFunctions_exists_prime_factors H hp hH
    q.denominator (q.denominator_ne_zero hne)
  let ev := UnramifiedNormalized.evaluation ν τ.val
  have hprod : ev fs.prod = 0 := by
    obtain ⟨u, hu⟩ := hassoc
    have h := congrArg ev hu
    rw [map_mul, show ev q.denominator = 0 from hτ, mul_eq_zero] at h
    exact h.resolve_right ((Units.isUnit u).map ev).ne_zero
  rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hprod
  obtain ⟨r, hrf, hrτ⟩ := hprod
  have hr := hfs r hrf
  obtain ⟨d, hd⟩ := (Multiset.dvd_prod hrf).trans hassoc.dvd
  let tr := unramifiedRegularTranslation ν τ.val
  have hr' : Prime (tr r) := (MulEquiv.prime_iff tr.toMulEquiv).mpr hr
  have hr₀ : (tr r).val (1 : X) = 0 := by
    change r.val (τ.val * 1) = 0
    rw [mul_one]
    exact hrτ
  have hdiv (v : V) (ℓ : W →ₗ[ℂ] ℂ) : ∃ b : R, ∀ z : (Set.univ : Set X),
      r.val z.val * b.val z.val = ℓ (q.numerator z.val v) := by
    obtain ⟨b, hb⟩ := (isPolynomialOn_scalar_iff _).mp ((q.polynomial v).linearMap ℓ)
    obtain ⟨g, ⟨G⟩, hg⟩ := hzero τ
    have hbval (z : X) : (tr b).val z = ℓ (q.numerator (τ.val * z) v) :=
      (hb ⟨τ.val * z, Set.mem_univ _⟩).symm
    have hdz (z : X) (hz : (tr r).val z = 0) : q.denominator.val (τ.val * z) = 0 := by
      change r.val (τ.val * z) = 0 at hz
      simp only [hd, Subalgebra.coe_mul, Pi.mul_apply, hz, zero_mul]
    have hbd : tr r ∣ tr b := prime_dvd_of_complex_and_unitary_zeros H hH
      (tr r) g (tr b) hr' hr₀ G (by
        intro z hz hgz
        rw [hbval, hg q z hgz (hdz z hz), LinearMap.zero_apply, map_zero]) (by
        intro z hz
        let w : Ω := ⟨τ.val * unitaryToUnramified H z, htwist τ z⟩
        have he := hclears w
        change q.numerator w.val = q.denominator.val w.val • J w at he
        rw [hdz (unitaryToUnramified H z) hz, zero_smul] at he
        change q.numerator (τ.val * unitaryToUnramified H z) = 0 at he
        rw [hbval, he, LinearMap.zero_apply, map_zero])
    obtain ⟨c, hc⟩ := (map_dvd_iff tr).mp hbd
    exact ⟨c, fun z => (congrArg (fun f : R => f.val z.val) hc).symm.trans (hb z).symm⟩
  obtain ⟨N, hN, hNq⟩ := exists_polynomial_operator_quotient_of_linear_tests r
    (rationalUnramifiedRegular_dense_nonzero_on_open H hp hH r hr.ne_zero isOpen_univ)
      (fun z => q.numerator z.val) q.polynomial hdiv
  have hval (z : D) : q.denominator.val z.val = r.val z.val * d.val z.val :=
    congrArg (fun f : R => f.val z.val) hd
  let q' : RationalOperatorContinuationData D (restrictFamily H J hDΩ) := {
    denominator := d
    denominator_nonzero := fun z => right_ne_zero_of_mul ((hval z) ▸ q.denominator_nonzero z)
    numerator := fun z => N ⟨z, Set.mem_univ z⟩
    polynomial := hN
    clears := fun z => by
      apply smul_right_injective (V →ₗ[ℂ] W)
        (left_ne_zero_of_mul ((hval z) ▸ q.denominator_nonzero z))
      change r.val z.val • N ⟨z.val, Set.mem_univ _⟩ = r.val z.val • (d.val z.val • restrictFamily H J hDΩ z)
      rw [← hNq ⟨z.val, Set.mem_univ _⟩, q.clears z, hval z, smul_smul] }
  apply hmin d ⟨q', rfl⟩
  exact ⟨q'.denominator_ne_zero hne, r, hr.not_isUnit, hd.trans (mul_comm r d)⟩

end Langlands.Plancherel.UnramifiedOperatorFamily
