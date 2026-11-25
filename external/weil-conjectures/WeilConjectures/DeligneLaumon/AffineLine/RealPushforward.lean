/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.FibreCohomology
public import WeilConjectures.WeilSheaf.Fourier
public import WeilConjectures.WeilSheaf.UpperStarPointwise
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Real

/-!
# Reality of a higher direct image with compact support concentrated in one degree

Let `f : X ⟶ Y` be a separated morphism of finite type of `k₀`-schemes and `K` an `ι`-real Weil
sheaf on `X`. If the higher direct images `Rᵛf_!K` vanish for `ν ≠ 1`, then `R¹f_!K` is
`ι`-real. At a closed point `ξ` of `Y` of degree `d`, compact support base change identifies
`det(1 - T^d F_ξ | (R¹f_!K)_ξ̄)` with the local polynomial of `H_c^1(X_ξ ⊗ k̄, K)` for the fibre
`X_ξ` of `f` over `ξ`, the only nonzero compactly supported cohomology group of the fibre. By the
Grothendieck–Lefschetz trace formula on `X_ξ` the traces of the powers of its Frobenius are, up to
sign, sums of traces of powers of local Frobenius of `K`, which are `ι`-real since `K` is, so
`H_c^1(X_ξ ⊗ k̄, K)` is `ι`-real by Newton's identities
(`FrobeniusModule.isReal_iff_forall_trace_pow`).

## Main statements

- `AlgebraicGeometry.WeilSheaf.isReal_higherLowerShriek_one`: reality of `R¹f_!K` when the
  `Rᵛf_!K` vanish for `ν ≠ 1`.
- `AlgebraicGeometry.WeilSheaf.isReal_higherLowerShriek_snd_one`
  (`proposition-purity-lisse-part-fourier-transform`): the case of the second projection `𝔸² ⟶ 𝔸¹`.
-/

@[expose] public section

universe u v

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

/-- The traces of the powers of the Frobenius on the compactly supported cohomology of an `ι`-real
Weil sheaf concentrated in a single degree `r` are `ι`-real: by the Grothendieck–Lefschetz trace
formula they are, up to the sign `(-1)ʳ`, sums of multiples of traces of powers of the local
Frobenius, which are `ι`-real (`FrobeniusModule.isReal_iff_forall_trace_pow`). -/
theorem IsReal.isReal_compactlySupportedCohomology_of_subsingleton {ι : PadicAlgCl l →+* ℂ}
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] {K : WeilSheaf k₀ l X} (hK : K.IsReal ι)
    (r : ℤ) (hvan : ∀ i ≠ r, Subsingleton (K.compactlySupportedCohomology i).carrier) :
    (K.compactlySupportedCohomology r).IsReal ι := by
  rw [FrobeniusModule.isReal_iff_forall_trace_pow]
  intro m
  rcases m with _ | m
  · rw [pow_zero, LinearMap.trace_one, map_natCast, Complex.conj_natCast]
  have hGL := K.sum_trace_compactlySupportedCohomology (m := m + 1) (Nat.succ_ne_zero m)
  rw [finsum_eq_single _ r fun i hi ↦ by
    have := hvan i hi
    rw [Subsingleton.elim ((K.compactlySupportedCohomology i).frobeniusEnd ^ (m + 1)) 0,
      map_zero, smul_zero]] at hGL
  have hRHS : (∑ᶠ x : X.finitePoints, if (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ∣ m + 1
      then ((X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 : PadicAlgCl l) *
        LinearMap.trace (PadicAlgCl l) (K.stalk x).carrier ((K.stalk x).frobeniusEnd ^
          ((m + 1) / (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1))
      else 0) ∈ ι.realSubfield := by
    refine finsum_induction _ (zero_mem _) (fun _ _ ↦ add_mem) fun x ↦ ?_
    split_ifs
    · exact mul_mem (natCast_mem _ _)
        (RingHom.mem_realSubfield.2 ((FrobeniusModule.isReal_iff_forall_trace_pow ι _).1
          (hK x) _))
    · exact zero_mem _
  rw [← hGL] at hRHS
  have hu : ((r.negOnePow : ℤ) : PadicAlgCl l) ∈ ι.realSubfield := intCast_mem _ _
  have hr : ((r.negOnePow : ℤ) : PadicAlgCl l) * ((r.negOnePow : ℤ) : PadicAlgCl l) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  rw [zsmul_eq_mul] at hRHS
  have := mul_mem hu hRHS
  rwa [← mul_assoc, hr, one_mul] at this

variable {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f]
  [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- The local polynomial of a Frobenius module over `PadicAlgCl l` is its `charpolyRev`, with the
`CommRing` instance found by instance search (`AlgebraicClosure.instCommRing`) rather than the one
unfolded from `Field`; stated on a generic module so that the kernel checks it once. -/
private lemma charpolyRev_eq_localPolynomial {l : ℕ} [Fact l.Prime]
    (M : FrobeniusModule.{v, 0} (PadicAlgCl l)) :
    M.frobeniusEnd.charpolyRev = M.localPolynomial := rfl

variable (f) in
/-- **Reality survives a direct image concentrated in degree one.** Let `f : X ⟶ Y` be a
separated morphism of finite type of `k₀`-schemes and `K` an `ι`-real Weil sheaf on `X` such
that the higher direct images `Rᵛf_!K` vanish for `ν ≠ 1`. Then `R¹f_!K` is `ι`-real.

At a closed point `ξ` of degree `d`, with fibre `X_ξ`, compact support base change gives
`det(1 - T^d F_ξ | (R¹f_!K)_ξ̄) = det(1 - T F | H_c^1(X_ξ ⊗ k̄, K))` and the vanishing of the
other `H_c^ν(X_ξ ⊗ k̄, K)`
(`AlgebraicGeometry.WeilSheaf.exists_fiber_expand_charpolyRev_stalk_higherLowerShriek`). The
restriction of `K` to `X_ξ` is `ι`-real, so `H_c^1(X_ξ ⊗ k̄, K)` is `ι`-real by the
Grothendieck–Lefschetz trace formula
(`AlgebraicGeometry.WeilSheaf.IsReal.isReal_compactlySupportedCohomology_of_subsingleton`),
and the coefficients of `det(1 - T F_ξ)` are among those of its local polynomial.
(blueprint: `proposition-purity-lisse-part-fourier-transform`, for a general `f`) -/
theorem isReal_higherLowerShriek_one {ι : PadicAlgCl l →+* ℂ} {K : WeilSheaf k₀ l X}
    (hK : K.IsReal ι) (hvan : ∀ ν : ℕ, ν ≠ 1 → IsZero ((higherLowerShriek k₀ l f ν).obj K)) :
    ((higherLowerShriek k₀ l f 1).obj K).IsReal ι := by
  intro ξ n
  obtain ⟨X', _, g, _, _, _, _, hfib⟩ :=
    exists_fiber_expand_charpolyRev_stalk_higherLowerShriek (k₀ := k₀) (f := f) (l := l) ξ
  have h₁ := (hK.upperStar g).isReal_compactlySupportedCohomology_of_subsingleton
      ((1 : ℕ) : ℤ) fun i hi ↦ by
    rcases lt_or_ge i 0 with h | h
    · exact subsingleton_globalSections_of_isZero
        (isZero_homologySheaf_derivedLowerShriek_of_neg ((upperStar g).obj K) h)
    · obtain ⟨ν, rfl⟩ := Int.eq_ofNat_of_zero_le h
      exact (hfib K ν).1 (hvan ν (by exact_mod_cast hi))
  have hd := Scheme.Hom.degreeOver_ne_zero (Y ↘ Spec (CommRingCat.of k₀)) ξ.2
  have := h₁ (n * (Y ↘ Spec (CommRingCat.of k₀)).degreeOver ξ.1)
  have hc := (hfib K 1).2
  -- `hfib` states the characteristic polynomials with the instance
  -- `AlgebraicClosure.instCommRing`, while `localPolynomial` unfolds to `charpolyRev` through
  -- `Field.toCommRing`; identify the two on a generic module (`charpolyRev_eq_localPolynomial`)
  -- so that the kernel never compares them on the stalk (v4.35: timeout).
  rw [charpolyRev_eq_localPolynomial, charpolyRev_eq_localPolynomial] at hc
  rwa [← hc, Polynomial.coeff_expand_mul (Nat.pos_of_ne_zero hd)] at this

/-- **Reality survives the Fourier projection.** Let `K` be an `ι`-real Weil sheaf on the
affine plane `𝔸¹ ×_{k₀} 𝔸¹` such that `Rpr₂!K` has no cohomology sheaves outside degree one,
for the second projection `pr₂ : 𝔸¹ ×_{k₀} 𝔸¹ ⟶ 𝔸¹`. Then `R¹pr₂!K` is `ι`-real. This is the
case `f = pr₂` of `AlgebraicGeometry.WeilSheaf.isReal_higherLowerShriek_one`.
(blueprint: `proposition-purity-lisse-part-fourier-transform`) -/
theorem isReal_higherLowerShriek_snd_one {ι : PadicAlgCl l →+* ℂ}
    {K : WeilSheaf k₀ l (affinePlane k₀)} (hK : K.IsReal ι)
    (hvan : ∀ ν : ℕ, ν ≠ 1 → IsZero ((higherLowerShriek k₀ l (affinePlane.snd k₀) ν).obj K)) :
    ((higherLowerShriek k₀ l (affinePlane.snd k₀) 1).obj K).IsReal ι :=
  isReal_higherLowerShriek_one _ hK hvan

end WeilSheaf

end AlgebraicGeometry
