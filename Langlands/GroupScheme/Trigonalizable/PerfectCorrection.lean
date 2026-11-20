import Langlands.GroupScheme.LinearAdditiveExtension.Correction
import Langlands.GroupScheme.Torus.DiagonalizableSmoothConnectedCriteriaProof
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.FieldTheory.Perfect

/-! # Correcting crossed homomorphisms over perfect fields with connected diagonalizable groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.PerfectCorrection

open RelativeRoot RelativeRoot.AdditiveGroupQuotient PointedCoordinateWeights

variable {k : Type u} [Field k]

/-! ### Coefficients of additive polynomials -/

section Additive

/-- If `f(X + Y) = f(X) + f(Y)`, then `binom(i, j) aᵢ = 0` for `0 < j < i`. -/
theorem choose_mul_coeff_eq_zero {f : k[X]}
    (htaylor : taylor (X : k[X]) (f.map C) = f.map C + C f)
    {i j : ℕ} (hj : 0 < j) (hji : j < i) : (i.choose j : k) * f.coeff i = 0 := by
  have h := congrArg (fun P : k[X][X] => (P.coeff j).coeff (i - j)) htaylor
  rw [AdditivePolynomial.taylor_map_coeff, hasseDeriv_coeff, Nat.sub_add_cancel hji.le] at h
  rw [h, coeff_add, coeff_map, coeff_C]
  simp only [hj.ne', ite_false, add_zero]
  rw [coeff_C, ite_eq_right_iff.mpr (fun h => absurd h (Nat.sub_ne_zero_of_lt hji))]

/-- In characteristic exponent `p`, a nonzero coefficient of an additive polynomial sits at a
power of `p` or at `0`. -/
theorem eq_zero_or_eq_pow_of_coeff_ne_zero (p : ℕ) [ExpChar k p] {f : k[X]}
    (htaylor : taylor (X : k[X]) (f.map C) = f.map C + C f) {i : ℕ}
    (hi : f.coeff i ≠ 0) : i = 0 ∨ ∃ v : ℕ, i = p ^ v := by
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · exact Or.inl h0
  right
  have hch : ∀ j, 0 < j → j < i → (i.choose j : k) = 0 := by
    intro j hj hji
    have := choose_mul_coeff_eq_zero htaylor hj hji
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hi
  rcases expChar_is_prime_or_one k p with hp | hp
  · have : Fact p.Prime := ⟨hp⟩
    have : CharP k p := (expChar_prime_iff (R := k) hp).mp ‹_›
    refine ⟨multiplicity p i, Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat hpos ?_⟩
    intro j hj
    rw [Finset.mem_Icc] at hj
    have h1 := hch j (by omega) (by omega)
    rw [CharP.cast_eq_zero_iff k p] at h1
    exact Nat.modEq_zero_iff_dvd.mpr h1
  · subst hp
    refine ⟨0, ?_⟩
    by_contra hne
    have h2 : 1 < i := by rw [pow_zero] at hne; omega
    have h1 := hch 1 one_pos h2
    rw [Nat.choose_one_right] at h1
    have : CharZero k := charZero_of_expChar_one' k
    exact absurd h1 (by exact_mod_cast hpos.ne')

end Additive

/-! ### Units of finite order on connected spectra -/

section Connected

/-- A unit of order dividing an integer invertible in a ring with connected spectrum, which
specializes to `1` somewhere, is `1`. -/
theorem eq_one_of_pow_eq_one {R K : Type*} [CommRing R] [CommRing K] [Nontrivial K]
    [ConnectedSpace (PrimeSpectrum R)] (φ : R →+* K) {w : R} {m : ℕ} (hw : w ^ m = 1)
    (hm : IsUnit (m : R)) (hφ : φ w = 1) : w = 1 := by
  obtain ⟨c, hc⟩ : ∃ c : R, c * m = 1 := ⟨((hm.unit⁻¹ : Rˣ) : R), hm.val_inv_mul⟩
  have he := Diagonalizable.SmoothConnectedCriteria.isIdempotentElem_geomSum hw hc
  set S := ∑ i ∈ Finset.range m, w ^ i with hS
  have hφS : φ S = m := by
    simp [S, map_sum, map_pow, hφ]
  rcases Diagonalizable.SmoothConnectedCriteria.eq_zero_or_one_of_connectedSpace he with h0 | h1
  · exfalso
    have h := congrArg φ h0
    rw [map_mul, hφS, map_zero, ← map_natCast φ, ← map_mul, hc, map_one] at h
    exact one_ne_zero h
  · have hSm : S = m := by
      calc S = (c * m) * S := by rw [hc, one_mul]
        _ = m * (c * S) := by ring
        _ = m := by rw [h1, mul_one]
    have hgeom : S * (w - 1) = 0 := by
      rw [hS, geom_sum_mul, hw, sub_self]
    rw [hSm] at hgeom
    have := (hm.mul_right_eq_zero).mp hgeom
    exact sub_eq_zero.mp this

/-- The same for global functions on a connected affine scheme. -/
theorem eq_one_of_pow_eq_one_of_connectedSpace {X : Scheme.{u}} [IsAffine X] [ConnectedSpace X]
    {K : Type*} [CommRing K] [Nontrivial K] (φ : Γ(X, ⊤) →+* K) {w : Γ(X, ⊤)} {m : ℕ}
    (hw : w ^ m = 1) (hm : IsUnit (m : Γ(X, ⊤))) (hφ : φ w = 1) : w = 1 := by
  have : ConnectedSpace (PrimeSpectrum Γ(X, ⊤)) :=
    (Scheme.homeoOfIso X.isoSpec).connectedSpace_iff.mp ‹_›
  exact eq_one_of_pow_eq_one φ hw hm hφ

end Connected


/-! ### Scaling identities for the closed polynomial -/

section Scaling

open ClosedAdditivePolynomial

variable {K : GroupScheme (Spec (CommRingCat.of k))}
  (a : K ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)
  {S : CommGroupScheme (Spec (CommRingCat.of k))} [IsAffineHom S.X.hom]
  (χ : characterLattice S)

/-- Coefficientwise scaling: if the `i`-th coefficient of the closed polynomial is nonzero, then
`χ(d)^i = χ(d)^N` for every point `d`, where `N` is the degree. -/
theorem charValue_pow_eq_of_coeff_ne_zero (ha : IsClosedSubgroup a) (h : closedPolynomial a ≠ 0)
    (hst : ∀ (T : Over (Spec (CommRingCat.of k))) (d : T ⟶ S.X)
      (x : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
      x ∈ (SubgroupFunctor.range a).carrier T →
        (VectorGroup.weightAction (n := 1) χ).act d x ∈ (SubgroupFunctor.range a).carrier T)
    {i : ℕ} (hi : (closedPolynomial a).coeff i ≠ 0)
    {T : Over (Spec (CommRingCat.of k))} (d : T ⟶ S.X) :
    VectorGroup.charValue χ T d ^ i =
      VectorGroup.charValue χ T d ^ (closedPolynomial a).natDegree := by
  set R := (Coord S.X : Type u)
  let t : T ⟶ affTest k R := d ≫ (coordinateIso S.X).inv
  let θ : R →+* Γ(T.left, ⊤) :=
    t.left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have hθc : θ (DiagonalizableAverage.charCoeff χ (universalPoint S.X)) =
      VectorGroup.charValue χ T d := by
    have hd : d = t ≫ universalPoint S.X := by
      rw [universalPoint_eq_coordinateIso, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hd, VectorGroup.charValue_comp]
    change t.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom _)) = _
    congr 1
    exact (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply _
  have hθk : θ.comp (algebraMap k R) = structureMap T := by
    rw [← structureMap_comp t]
    ext c
    change t.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (algebraMap k R c)) =
      t.left.appTop.hom (structureMap (affTest k R) c)
    congr 1
    have h1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k R))
    change ((CommRingCat.ofHom (algebraMap k R)) ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv) c =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap k R))).appTop) c
    rw [h1]
  have key := congrArg (fun q : R[X] => θ (q.coeff i)) (comp_C_mul_X_eq a χ ha h hst)
  simp only [comp_C_mul_X_coeff, coeff_C_mul, coeff_map] at key
  simp only [map_mul, map_pow, hθc] at key
  have hu : IsUnit (θ (algebraMap k R ((closedPolynomial a).coeff i))) := by
    rw [← RingHom.comp_apply, hθk]
    exact (isUnit_iff_ne_zero.mpr hi).map _
  rw [mul_comm] at key
  exact hu.mul_right_cancel key

end Scaling


/-! ### Solvability of the correction equation over perfect fields -/

section Solvability

open ClosedAdditivePolynomial

variable {Λ : Type u} [AddCommGroup Λ] {K : GroupScheme (Spec (CommRingCat.of k))}
  (a : K ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)
  (χ : characterLattice (Diagonalizable.groupScheme (CommRingCat.of k) Λ))

/-- Over a perfect field with `D(Λ)` connected, either the closed polynomial of a closed
subgroup of `𝔾ₐ` stable under the weight action of `χ` is surjective on `k`, or `χ^N` is
trivial, where `N` is its degree. -/
theorem surjective_or_charValue_pow_eq_one [PerfectField k]
    (hD : ConnectedSpace (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X.left)
    (ha : IsClosedSubgroup a) (hf : closedPolynomial a ≠ 0)
    (hst : ∀ (T : Over (Spec (CommRingCat.of k)))
      (d : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X)
      (x : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
      x ∈ (SubgroupFunctor.range a).carrier T →
        (VectorGroup.weightAction (n := 1) χ).act d x ∈ (SubgroupFunctor.range a).carrier T) :
    (∀ m : k, ∃ r : k, (closedPolynomial a).eval r = m) ∨
      ∀ (T : Over (Spec (CommRingCat.of k)))
        (d : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X),
        VectorGroup.charValue χ T d ^ (closedPolynomial a).natDegree = 1 := by
  obtain ⟨p, hp⟩ := ExpChar.exists k
  set f := closedPolynomial a with hfdef
  set N := f.natDegree with hN
  have hmonic : f.Monic := closedPolynomial_monic a hf
  have hpos : 0 < N := natDegree_pos a ha hf
  have htaylor := AdditivePolynomial.taylor_eq_of_mem_span hmonic hpos (taylor_mem_span a ha)
  have h0 : f.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    exact eval_zero a ha
  have hNc : f.coeff N ≠ 0 := by
    rw [hmonic.coeff_natDegree]
    exact one_ne_zero
  obtain ⟨s, hs⟩ : ∃ s : ℕ, N = p ^ s := by
    rcases eq_zero_or_eq_pow_of_coeff_ne_zero p htaylor hNc with h | h
    · omega
    · exact h
  by_cases hall : ∀ i < N, f.coeff i = 0
  · left
    have hfX : f = X ^ N := by
      ext i
      rw [coeff_X_pow]
      rcases lt_trichotomy i N with hi | hi | hi
      · rw [hall i hi]
        simp [hi.ne]
      · rw [hi, hmonic.coeff_natDegree]
        simp
      · rw [coeff_eq_zero_of_natDegree_lt hi]
        simp [hi.ne']
    intro m
    refine ⟨(iterateFrobeniusEquiv k p s).symm m, ?_⟩
    rw [hfX, eval_pow, eval_X, hs, ← iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]
  · right
    push Not at hall
    obtain ⟨i, hiN, hi⟩ := hall
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hi h0
    obtain ⟨v, hv⟩ := (eq_zero_or_eq_pow_of_coeff_ne_zero p htaylor hi).resolve_left hi0
    have hp1 : p ≠ 1 := by
      rintro rfl
      rw [one_pow] at hs hv
      omega
    have hprime : p.Prime := (expChar_is_prime_or_one k p).resolve_right hp1
    have : CharP k p := (expChar_prime_iff (R := k) hprime).mp hp
    have hvs : v < s := by
      have h1 : p ^ v < p ^ s := by
        rw [← hv, ← hs]
        exact hiN
      exact (Nat.pow_lt_pow_iff_right hprime.one_lt).mp h1
    have hscale : ∀ (T : Over (Spec (CommRingCat.of k)))
        (d : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X),
        VectorGroup.charValue χ T d ^ p ^ v = VectorGroup.charValue χ T d ^ p ^ s := by
      intro T d
      have h := charValue_pow_eq_of_coeff_ne_zero a χ ha hf hst hi d
      rwa [hv, ← hN, hs] at h
    obtain ⟨u, hudef⟩ : ∃ u, u = VectorGroup.charValue χ
        (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X
        (𝟙 (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X) := ⟨_, rfl⟩
    have hu : IsUnit u := by
      rw [hudef]
      exact Units.isUnit _
    obtain ⟨m, hm⟩ : ∃ m, m = p ^ (s - v) - 1 := ⟨_, rfl⟩
    have hm1 : m + 1 = p ^ (s - v) := by
      have := Nat.one_le_pow (s - v) p hprime.pos
      omega
    have hwm : (u ^ p ^ v) ^ m = 1 := by
      have huv := hscale _ (𝟙 (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X)
      rw [← hudef] at huv
      have hwu : IsUnit (u ^ p ^ v) := hu.pow _
      apply hwu.mul_left_cancel
      rw [mul_one, ← pow_succ', hm1, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hvs.le]
      exact huv.symm
    let B : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 (Spec (CommRingCat.of k)))
    have : Nontrivial Γ(B.left, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
    let φ : Γ((Diagonalizable.groupScheme (CommRingCat.of k) Λ).X.left, ⊤) →+* Γ(B.left, ⊤) :=
      (1 : B ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X).left.appTop.hom
    have hφu : φ u = 1 := by
      have h := VectorGroup.charValue_comp χ (1 : B ⟶ (Diagonalizable.groupScheme
        (CommRingCat.of k) Λ).X) (𝟙 (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X)
      rw [Category.comp_id, VectorGroup.charValue_one] at h
      rw [hudef]
      exact h.symm
    have hφw : φ (u ^ p ^ v) = 1 := by
      rw [map_pow, hφu, one_pow]
    have hmk : IsUnit ((m : ℕ) : k) := by
      rw [hm, Nat.cast_sub (Nat.one_le_pow _ _ hprime.pos), Nat.cast_pow, CharP.cast_eq_zero,
        zero_pow (Nat.sub_ne_zero_of_lt hvs), Nat.cast_one, zero_sub]
      exact isUnit_one.neg
    have hmR : IsUnit ((m : ℕ) :
        Γ((Diagonalizable.groupScheme (CommRingCat.of k) Λ).X.left, ⊤)) := by
      have := hmk.map (structureMap (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X)
      rwa [map_natCast] at this
    have : IsAffine (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X.left :=
      isAffine_of_isAffineHom (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X.hom
    have hw1 : u ^ p ^ v = 1 := eq_one_of_pow_eq_one_of_connectedSpace φ hwm hmR hφw
    intro T d
    have hc : VectorGroup.charValue χ T d = d.left.appTop u := by
      have h := VectorGroup.charValue_comp χ d
        (𝟙 (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X)
      rw [Category.comp_id] at h
      rw [h, hudef]
    rw [hs, hc, ← Nat.add_sub_cancel' hvs.le, pow_add, pow_mul, ← map_pow, hw1,
      map_one, one_pow]

end Solvability

end Langlands.GroupScheme.PerfectCorrection
