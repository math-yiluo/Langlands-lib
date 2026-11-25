/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryConstruction
public import WeilConjectures.Mathlib.Algebra.Polynomial.FieldDivision
public import WeilConjectures.PointCountBound
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.EulerRadius
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseRank
public import WeilConjectures.WeilSheaf.BoundaryStalk
public import WeilConjectures.WeilSheaf.DirectImageStalk

/-!
# Boundary semicontinuity of weights for Weil sheaves

Let `C₀` be a smooth geometrically connected affine curve over `k₀ = 𝔽_q`, `j : U₀ ⟶ C₀` a
dense open immersion and `ℱ` a lisse Weil sheaf on `U₀` with punctual weights at most `β`. Then
the direct image `j_* ℱ` has punctual weights at most `β` on all of `C₀`
(`proposition-weights-j-boundary-points--1`, and the first assertion of
`proposition-weights-j-boundary-points`).

This is the sheaf-level form of the argument of
`AlgebraicGeometry.WeilGroup.frobeniusWeight_le_of_isAffine`. Put `J = j_* ℱ` and let `T` be the
set of closed points of `C₀` lying in `U₀`, whose complement is finite. The Euler product of `J`
(`proposition-weights-j-boundary-points`,
`AlgebraicGeometry.WeilSheaf.coeff_prod_inv_localPolynomial_stalk_directImage`), split into the
product over `T` and the finitely many local factors outside `T`, gives

`L (T, J, T) · ι det (1 - F T ∣ H_c² (J)) =`
`  ι det (1 - F T ∣ H_c¹ (J)) · ∏_{s ∉ T} ι P_s (J, T ^ e_s)`.

On `T` the stalks of `J` are those of `ℱ`
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_directImage`), of bounded rank
(`AlgebraicGeometry.WeilSheaf.IsLisse.exists_finrank_stalk_le`), and the closed points of degree
`n` number `O(qⁿ)`; so the inverse of `L (T, J, T)` converges on the disc of radius
`R = q ^ (-(β / 2 + 1))`. The group `H_c² (J)` is the geometric coinvariants of `ℱ` twisted by
`(-1)`, whose eigenvalues have absolute value at most `q ^ (β / 2 + 1)`
(`AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_geometricCoinvariants`). Hence the boundary
local polynomials have no zero in that disc (`PowerSeries.one_le_mul_norm_of_tprod_mul_eq_mul`),
which bounds the boundary weights by `β + 2`
(`AlgebraicGeometry.WeilSheaf.norm_le_of_hasEigenvalue_stalk_directImage`). Applied to the tensor
powers `ℱ^{⊗ k}`, whose boundary eigenvalues include the `k`-th powers of those of `ℱ`
(`AlgebraicGeometry.WeilSheaf.hasEigenvalue_stalk_directImage_tensorPow`), this gives the bound
`β + 2 / k` for every `k ≥ 1`, hence `β`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsLisse.exists_finrank_stalk_le`: a lisse Weil sheaf on a
  quasi-compact scheme has stalks of bounded dimension.
- `AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_geometricCoinvariants`: the geometric
  coinvariants of a lisse sheaf with weights at most `w` have weights at most `w`.
- `AlgebraicGeometry.WeilSheaf.norm_le_of_hasEigenvalue_stalk_directImage`: the preliminary
  bound `β + 2` at the boundary points.
- `AlgebraicGeometry.WeilSheaf.hasWeightsAtMost_directImage`: boundary semicontinuity of
  weights on a smooth geometrically connected affine curve.

The case of a general, not necessarily affine, curve (Step 0 of the blueprint proof) is
`AlgebraicGeometry.WeilSheaf.IsLisse.hasWeightsAtMost_directImage`
(`WeilConjectures.WeilSheaf.RealPurity`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped PowerSeries.WithPiTopology NNReal ENNReal

namespace FrobeniusModule

variable {K : Type*} [Field K]

/-- The eigenvalues of the Frobenius of the dual `M^∨` are the inverses of those of `M`. -/
theorem hasEigenvalue_inv_of_hasEigenvalue_dual {M : FrobeniusModule K} {α : K}
    (hα : M.dual.frobeniusEnd.HasEigenvalue α) : M.frobeniusEnd.HasEigenvalue α⁻¹ := by
  have hF : M.dual.frobeniusEnd.charpoly = M.frobenius.symm.toLinearMap.charpoly :=
    LinearMap.charpoly_dualMap _
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hF,
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hα
  obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
  have hx' : x = α • M.frobenius x := by
    simpa using congrArg M.frobenius hx.1
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact hx.2 (by simpa using hx')
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := x)
    (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 ?_, hx.2⟩)
  change M.frobenius x = α⁻¹ • x
  conv_rhs => rw [hx', inv_smul_smul₀ hα0]

end FrobeniusModule

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section Lisse

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- **A lisse Weil sheaf has bounded rank.** On a quasi-compact `k₀`-scheme the stalks of a
lisse Weil sheaf at the closed points have bounded dimension. -/
theorem IsLisse.exists_finrank_stalk_le [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    {F : WeilSheaf k₀ l X} (hF : F.IsLisse) :
    ∃ d : ℕ, ∀ x : X.finitePoints, Module.finrank (PadicAlgCl l) (F.stalk x).carrier ≤ d := by
  have : CompactSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    QuasiCompact.compactSpace_of_compactSpace
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  obtain ⟨d, hd⟩ := ProEtale.IsAdicLisseSheaf.exists_finrank_globalSections_upperStar_le hF
    (AlgebraicClosure k₀)
  exact ⟨d, fun x ↦ hd _⟩

/-- *Weights of the geometric coinvariants.* If the lisse Weil sheaf `F` has weights at most `w`,
then its geometric coinvariants `V_{π₁(X̄)}` have weights at most `w` over `k₀`. Every
eigenvalue of the Frobenius on the global sections of `F^∨` is, up to the power `deg x`, an
eigenvalue of the local Frobenius of `F^∨` at a closed point `x`
(`AlgebraicGeometry.WeilSheaf.exists_hasEigenvalue_stalk_of_hasEigenvalue_globalSections`), the
inverse of one of `F`. This is the upper-bound analogue of
`AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_geometricCoinvariants`. -/
theorem hasWeightsAtMostOver_geometricCoinvariants
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (ι : PadicAlgCl l →+* ℂ)
    {F : WeilSheaf k₀ l X} (hF : F.IsLisse) {w : ℝ} (hw : F.HasWeightsAtMost ι w) :
    (F.geometricCoinvariants hF).HasWeightsAtMostOver k₀ ι w := by
  intro γ hγ
  have hγ' := FrobeniusModule.hasEigenvalue_inv_of_hasEigenvalue_dual
    (M := (F.dual hF).globalSections) hγ
  obtain ⟨x, hx⟩ := exists_hasEigenvalue_stalk_of_hasEigenvalue_globalSections (F.dual hF) hγ'
  obtain ⟨e⟩ := nonempty_equiv_stalk_dual hF x
  have h := FrobeniusModule.hasEigenvalue_inv_of_hasEigenvalue_dual (e.hasEigenvalue hx)
  rw [inv_pow, inv_inv] at h
  have hm := (X ↘ Spec (CommRingCat.of k₀)).degreeOver_ne_zero x.2
  have hq : (0 : ℝ) ≤ Nat.card k₀ := Nat.cast_nonneg _
  have hb := hw x _ h
  rw [map_pow, norm_pow, Scheme.Hom.residueCard, Nat.cast_pow, ← Real.rpow_natCast_mul hq,
    mul_comm, Real.rpow_mul_natCast hq] at hb
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.rpow_nonneg hq _) hm).1 hb

end Lisse

section Semicontinuity

variable {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
  {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ C) [IsOpenImmersion j]
  [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] [IsDominant j]
  (ι : PadicAlgCl l →+* ℂ)

/-- A smooth curve `C₀` is locally of finite type over `k₀`. -/
local instance locallyOfFiniteType_semicontinuity :
    LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀)) :=
  haveI := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  inferInstance

/-- Steps 1–3 of `proposition-weights-j-boundary-points--1`: the preliminary bound at the boundary.

Let `C₀` be a smooth geometrically connected affine curve, `j : U₀ ⟶ C₀` a dense open
immersion and `ℱ` a lisse Weil sheaf on `U₀` with weights at most `β`. At a closed point `s` of
`C₀` outside `U₀`, every eigenvalue `α` of the local Frobenius on the stalk of `j_* ℱ` satisfies
`|ι α| ≤ q ^ (e_s (β / 2 + 1))`, i.e. it has weight at most `β + 2`. -/
theorem norm_le_of_hasEigenvalue_stalk_directImage {F : WeilSheaf k₀ l U} (hF : F.IsLisse)
    {β : ℝ} (hw : F.HasWeightsAtMost ι β) (s : C.finitePoints)
    (hs : s.1 ∉ Set.range j.base) {α : PadicAlgCl l}
    (hα : (((directImage j).obj F).stalk s).frobeniusEnd.HasEigenvalue α) :
    ‖ι α‖ ≤ ((Nat.card k₀ : ℝ) ^ (β / 2 + 1)) ^
      (C ↘ Spec (CommRingCat.of k₀)).degreeOver s.1 := by
  classical
  set p := C ↘ Spec (CommRingCat.of k₀) with hp
  set J := (directImage j).obj F
  set q : ℝ := (Nat.card k₀ : ℝ) with hqdef
  have hq1 : 1 < q := by
    have := (Finite.one_lt_card_iff_nontrivial (α := k₀)).2 inferInstance
    rw [hqdef]
    exact_mod_cast this
  have hq0 : 0 < q := zero_lt_one.trans hq1
  set c : ℝ := q ^ (β / 2) with hcdef
  have hc : 0 ≤ c := Real.rpow_nonneg hq0.le _
  have hqc : q * c = q ^ (β / 2 + 1) := by rw [Real.rpow_add hq0, Real.rpow_one, mul_comm]
  -- finiteness properties of `C₀` and `U₀`
  have : QuasiCompact p := inferInstance
  have : IsCurve p :=
    { krullDim_le_one := by exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension p 1 }
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have : ConnectedSpace C := GeometricallyConnected.connectedSpace_of_subsingleton p
  have : Nonempty U := j.denseRange.nonempty_iff.2 inferInstance
  have hjp : j ≫ p = U ↘ Spec (CommRingCat.of k₀) :=
    (Scheme.Hom.isOver_iff (Spec (CommRingCat.of k₀))).1 inferInstance
  have : QuasiCompact (U ↘ Spec (CommRingCat.of k₀)) := hjp ▸ inferInstance
  have : LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀)) := hjp ▸ inferInstance
  have hdeg (y : U) : (U ↘ Spec (CommRingCat.of k₀)).degreeOver y = p.degreeOver (j.base y) := by
    rw [← hjp, Scheme.Hom.degreeOver_comp_of_isIso]
  -- the closed points of `C₀` in `U₀`, with finite complement
  set T : Set C.finitePoints := {x | x.1 ∈ Set.range j.base} with hTdef
  have hT : Tᶜ.Finite :=
    ((WeilGroup.finite_boundary (p := p) j).preimage Subtype.val_injective.injOn).subset
      fun x hx ↦ hx
  have hTU (x : C.finitePoints) (hx : x ∈ T) : ∃ y : U.finitePoints, j.base y.1 = x.1 := by
    obtain ⟨y, hy⟩ := hx
    exact ⟨⟨y, (Scheme.Hom.mem_finitePoints_iff_of_isIso j y).1 (hy ▸ x.2)⟩, hy⟩
  -- the local data of the Euler product
  set e : C.finitePoints → ℕ := fun x ↦ p.degreeOver x.1 with hedef
  have he (x : C.finitePoints) : e x ≠ 0 := p.degreeOver_ne_zero x.2
  set M : C.finitePoints → Multiset ℂ := fun x ↦ (J.stalk x).frobeniusEnd.charpoly.roots.map ι
    with hMdef
  have hlp (x : C.finitePoints) :
      ((J.stalk x).localPolynomial.map ι).comp (Polynomial.X ^ e x) =
        PowerSeries.eulerPoly (M x) (e x) := by
    rw [FrobeniusModule.localPolynomial, LinearMap.charpolyRev_eq_prod_roots,
      Polynomial.map_multiset_prod_one_sub_C_mul_X]
    rfl
  have hroot (x : C.finitePoints) {a : PadicAlgCl l} :
      a ∈ (J.stalk x).frobeniusEnd.charpoly.roots ↔ (J.stalk x).frobeniusEnd.HasEigenvalue a := by
    rw [Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  -- Step 1: the open part, with bounded rank and bounded local roots
  obtain ⟨d, hd⟩ := hF.exists_finrank_stalk_le
  have hcard (x : C.finitePoints) (hx : x ∈ T) : Multiset.card (M x) ≤ d := by
    obtain ⟨y, hy⟩ := hTU x hx
    obtain ⟨E⟩ := nonempty_equiv_stalk_directImage j F y x hy
    rw [Multiset.card_map, LinearMap.card_roots_charpoly, E.toLinearEquiv.finrank_eq]
    exact hd y
  have hMb (x : C.finitePoints) (hx : x ∈ T) : ∀ a ∈ M x, ‖a‖ ≤ c ^ e x := by
    intro a ha
    obtain ⟨y, hy⟩ := hTU x hx
    obtain ⟨E⟩ := nonempty_equiv_stalk_directImage j F y x hy
    obtain ⟨a', ha', rfl⟩ := Multiset.mem_map.1 ha
    have h := hw y a' (E.hasEigenvalue ((hroot x).1 ha'))
    rwa [Scheme.Hom.residueCard, hdeg, hy, Nat.cast_pow, ← Real.rpow_natCast_mul hq0.le,
      mul_comm, Real.rpow_mul_natCast hq0.le] at h
  obtain ⟨A, hA⟩ := p.exists_card_filter_degreeOver_le (IsCurve.krullDim_le_one p)
  -- Step 2: the eigenvalues on `H_c²`
  set S := ((J.compactlySupportedCohomology 2).frobeniusEnd.charpoly.roots).map ι with hSdef
  have hS : ∀ b ∈ S, ‖b‖ ≤ q * c := by
    intro b hb
    obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.1 hb
    rw [Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hμ
    obtain ⟨E⟩ := nonempty_equiv_compactlySupportedCohomology_directImage_two j F hF
    have hμ' := E.hasEigenvalue hμ
    set cK : PadicAlgCl l := (Nat.card k₀ : PadicAlgCl l) ^ (-(-1 : ℤ)) with hcK
    have hcK' : cK = (Nat.card k₀ : PadicAlgCl l) := by rw [hcK, neg_neg, zpow_one]
    have hιc : ι cK = (Nat.card k₀ : ℂ) := by rw [hcK', map_natCast]
    have hcK0 : cK ≠ 0 := fun h ↦ by
      have := congrArg ι h
      rw [hιc, map_zero, Nat.cast_eq_zero] at this
      exact Nat.card_pos.ne' this
    have hγ : (F.geometricCoinvariants hF).frobeniusEnd.HasEigenvalue (cK⁻¹ * μ) := by
      refine (FrobeniusModule.hasEigenvalue_frobeniusEnd_rescale_iff hcK0 _).1 ?_
      rw [mul_inv_cancel_left₀ hcK0]
      exact hμ'
    have hγb := hasWeightsAtMostOver_geometricCoinvariants ι hF hw _ hγ
    have hμe : μ = cK * (cK⁻¹ * μ) := by rw [mul_inv_cancel_left₀ hcK0]
    rw [hμe, map_mul, norm_mul, hιc, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hγb hq0.le
  -- the Euler product identity, transported to `ℂ` along `ι`
  set P : Polynomial ℂ := (J.compactlySupportedCohomology 1).localPolynomial.map ι with hPdef
  set D2 : Polynomial ℂ := (J.compactlySupportedCohomology 2).localPolynomial.map ι with hD2def
  set f : C.finitePoints → PowerSeries ℂ :=
    fun x ↦ ((PowerSeries.eulerPoly (M x) (e x) : Polynomial ℂ) : PowerSeries ℂ)⁻¹ with hfdef
  have hfin (n : ℕ) : {x : C.finitePoints | e x ≤ n}.Finite := p.finite_setOf_degreeOver_le n
  set Sn : ℕ → Finset C.finitePoints := fun n ↦ (hfin n).toFinset with hSndef
  have hSn (n : ℕ) : ∀ x ∉ Sn n, (PowerSeries.X : PowerSeries ℂ) ^ (n + 1) ∣ f x - 1 := by
    intro x hx
    have hlt : n < e x := by
      simpa [Sn] using hx
    exact (pow_dvd_pow _ hlt).trans (PowerSeries.X_pow_dvd_inv_eulerPoly_sub_one (M x) (he x))
  have hG (n : ℕ) (t : Finset C.finitePoints) (ht : Sn n ⊆ t) :
      PowerSeries.coeff n (∏ x ∈ t, f x) =
        PowerSeries.coeff n ((P : PowerSeries ℂ) * (D2 : PowerSeries ℂ)⁻¹) := by
    have h := congrArg ι (coeff_prod_inv_localPolynomial_stalk_directImage j F hF n t
      fun x hx ↦ ht (by simpa [Sn] using hx))
    rw [← PowerSeries.coeff_map, ← PowerSeries.coeff_map] at h
    have h1 : PowerSeries.map ι (∏ x ∈ t, ((((J.stalk x).localPolynomial.comp
        (Polynomial.X ^ p.degreeOver x.1) : Polynomial _) : PowerSeries (PadicAlgCl l)))⁻¹) =
        ∏ x ∈ t, f x := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun x _ ↦ ?_
      rw [PowerSeries.map_inv, ← Polynomial.polynomial_map_coe, Polynomial.map_comp,
        Polynomial.map_pow, Polynomial.map_X, hlp]
    have h2 : PowerSeries.map ι (((J.compactlySupportedCohomology 1).localPolynomial :
        PowerSeries (PadicAlgCl l)) * (((J.compactlySupportedCohomology 2).localPolynomial :
          Polynomial _) : PowerSeries (PadicAlgCl l))⁻¹) =
        (P : PowerSeries ℂ) * (D2 : PowerSeries ℂ)⁻¹ := by
      rw [map_mul, PowerSeries.map_inv, ← Polynomial.polynomial_map_coe,
        ← Polynomial.polynomial_map_coe]
    rw [← h1, ← h2]
    exact h
  have hsplit := PowerSeries.eq_tprod_mul_prod_of_forall_coeff_prod_eq Sn hSn hG hT
  -- Step 3: the product `B` of the boundary local polynomials
  set B : Polynomial ℂ := ∏ x ∈ hT.toFinset, PowerSeries.eulerPoly (M x) (e x) with hBdef
  have hFB : (∏ x ∈ hT.toFinset, f x) * (B : PowerSeries ℂ) = 1 := by
    rw [hBdef, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun x _ ↦ PowerSeries.inv_mul_cancel _
      (by rw [PowerSeries.constantCoeff_eulerPoly _ (he x)]; exact one_ne_zero)
  have hD2 : (D2 : PowerSeries ℂ) =
      (S.map fun b ↦ 1 - PowerSeries.C b * PowerSeries.X).prod := by
    rw [hD2def, FrobeniusModule.localPolynomial, LinearMap.charpolyRev_eq_prod_roots,
      Polynomial.map_multiset_prod_one_sub_C_mul_X, ← Polynomial.coeToPowerSeries.ringHom_apply,
      map_multiset_prod, Multiset.map_map]
    exact congrArg _ (Multiset.map_congr rfl fun b _ ↦ by simp)
  have hD20 : PowerSeries.constantCoeff (D2 : PowerSeries ℂ) ≠ 0 := by
    rw [hD2, map_multiset_prod, Multiset.map_map, Multiset.prod_eq_one fun a ha ↦ by
      obtain ⟨b, -, rfl⟩ := Multiset.mem_map.1 ha
      simp]
    exact one_ne_zero
  have hPB : (∏' x : T, f x.1) * (S.map fun b ↦ 1 - PowerSeries.C b * PowerSeries.X).prod =
      (P : PowerSeries ℂ) * (B : PowerSeries ℂ) := by
    set L := ∏' x : T, f x.1
    set Fin := ∏ x ∈ hT.toFinset, f x
    calc L * (S.map fun b ↦ 1 - PowerSeries.C b * PowerSeries.X).prod
        = L * (D2 : PowerSeries ℂ) := by rw [hD2]
      _ = L * Fin * D2 * B := by linear_combination (-(L * (D2 : PowerSeries ℂ))) * hFB
      _ = P * (D2 : PowerSeries ℂ)⁻¹ * D2 * B := by rw [hsplit]
      _ = P * B := by rw [mul_assoc (P : PowerSeries ℂ), PowerSeries.inv_mul_cancel _ hD20,
          mul_one]
  have hB0 : B.coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hBdef, Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.2 fun x _ ↦ ?_
    rw [← Polynomial.coeff_zero_eq_eval_zero, PowerSeries.eulerPoly_coeff_zero _ (he x)]
    exact one_ne_zero
  -- the zero `z` of the local polynomial at `s`
  have hα0 : ι α ≠ 0 := (map_ne_zero ι).2 (FrobeniusModule.ne_zero_of_hasEigenvalue hα)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (ι α)⁻¹ (Nat.pos_of_ne_zero (he s))
  have hBz : B.eval z = 0 := by
    rw [hBdef, Polynomial.eval_prod]
    refine Finset.prod_eq_zero (i := s) (hT.mem_toFinset.2 hs) ?_
    rw [PowerSeries.eulerPoly, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X, hz,
      Polynomial.eval_multiset_prod]
    refine Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨1 - Polynomial.C (ι α) * Polynomial.X,
      Multiset.mem_map_of_mem _ (Multiset.mem_map_of_mem ι ((hroot s).2 hα)), ?_⟩)
    simp [hα0]
  have key := PowerSeries.one_le_mul_norm_of_tprod_mul_eq_mul (J := T) (e := fun x ↦ e x.1)
    (fun x ↦ he x.1) (fun n ↦ (hfin n).preimage Subtype.val_injective.injOn) (fun x ↦ M x.1)
    hc hq0.le (fun x ↦ hMb x.1 x.2) (fun x ↦ hcard x.1 x.2) (hA T) hS hB0 hPB hBz
  -- hence `|ι α| ≤ (q c) ^ e_s`
  have hze : ‖z‖ ^ e s = ‖ι α‖⁻¹ := by rw [← norm_pow, hz, norm_inv]
  have h1 : 1 ≤ (q * c) ^ e s * ‖ι α‖⁻¹ := by
    rw [← hze, ← mul_pow]
    exact one_le_pow₀ key
  rw [← hqc]
  simpa using (le_mul_inv_iff₀ (norm_pos_iff.2 hα0)).1 h1

/-- Blueprint `proposition-weights-j-boundary-points--1` (first assertion of
`proposition-weights-j-boundary-points`):
*boundary semicontinuity of weights* on a smooth geometrically connected affine curve.

Let `C₀` be a smooth geometrically connected affine curve over `k₀`, `j : U₀ ⟶ C₀` a dense
quasi-compact open immersion and `ℱ` a lisse Weil sheaf on `U₀` with punctual weights at most
`β`. Then `j_* ℱ` has punctual weights at most `β` on all of `C₀`.

At the points of `U₀` the stalks of `j_* ℱ` are those of `ℱ`. At a boundary point `s`, an
eigenvalue `α` of the local Frobenius gives the eigenvalue `α ^ k` at `s` of `j_* (ℱ^{⊗ k})`,
where `ℱ^{⊗ k}` has weights at most `k β`; the preliminary bound
(`AlgebraicGeometry.WeilSheaf.norm_le_of_hasEigenvalue_stalk_directImage`) gives
`|ι α| ^ k ≤ q_s ^ (k β / 2 + 1)` for every `k ≥ 1`, hence `|ι α| ≤ q_s ^ (β / 2)`. -/
theorem hasWeightsAtMost_directImage {F : WeilSheaf k₀ l U} (hF : F.IsLisse) {β : ℝ}
    (hw : F.HasWeightsAtMost ι β) : ((directImage j).obj F).HasWeightsAtMost ι β := by
  set p := C ↘ Spec (CommRingCat.of k₀) with hp
  have hq1 : (1 : ℝ) < Nat.card k₀ := by
    have := (Finite.one_lt_card_iff_nontrivial (α := k₀)).2 inferInstance
    exact_mod_cast this
  have hq0 : (0 : ℝ) < Nat.card k₀ := zero_lt_one.trans hq1
  have hjp : j ≫ p = U ↘ Spec (CommRingCat.of k₀) :=
    (Scheme.Hom.isOver_iff (Spec (CommRingCat.of k₀))).1 inferInstance
  have : LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀)) := hjp ▸ inferInstance
  intro x α hα
  rw [Scheme.Hom.residueCard, Nat.cast_pow]
  by_cases hx : x.1 ∈ Set.range j.base
  · -- a point of `U₀`: the stalk is that of `ℱ`
    obtain ⟨y, hy⟩ := hx
    have hyfin : y ∈ U.finitePoints := (Scheme.Hom.mem_finitePoints_iff_of_isIso j y).1 (hy ▸ x.2)
    obtain ⟨E⟩ := nonempty_equiv_stalk_directImage j F ⟨y, hyfin⟩ x hy
    have h := hw ⟨y, hyfin⟩ α (E.hasEigenvalue hα)
    rwa [Scheme.Hom.residueCard, ← hjp, Scheme.Hom.degreeOver_comp_of_isIso, hy,
      Nat.cast_pow] at h
  · -- a boundary point: sharpening by tensor powers
    set e := p.degreeOver x.1
    have ha0 : 0 < ‖ι α‖ :=
      norm_pos_iff.2 ((map_ne_zero ι).2 (FrobeniusModule.ne_zero_of_hasEigenvalue hα))
    have hlog (k : ℕ) (hk : k ≠ 0) :
        k * Real.log ‖ι α‖ ≤ e * ((k * β / 2 + 1) * Real.log (Nat.card k₀)) := by
      have h := norm_le_of_hasEigenvalue_stalk_directImage j ι (isLisse_tensorPow F hF k)
        (hw.tensorPow hF k) x hx
        (hasEigenvalue_stalk_directImage_tensorPow j hF x hα k)
      rw [map_pow, norm_pow] at h
      have := Real.log_le_log (pow_pos ha0 k) h
      rwa [Real.log_pow, Real.log_pow, Real.log_rpow hq0] at this
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le,
      ← Real.log_le_log_iff ha0 (Real.rpow_pos_of_pos hq0 _), Real.log_rpow hq0]
    refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
    obtain ⟨k, hk⟩ := exists_nat_gt (e * Real.log (Nat.card k₀) / ε)
    have hk0 : (0 : ℝ) < k :=
      lt_of_le_of_lt (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_pos hq1).le)
        hε.le) hk
    have h1 := hlog k (by exact_mod_cast hk0.ne')
    have h2 : e * Real.log (Nat.card k₀) < ε * k := by
      rw [div_lt_iff₀ hε] at hk
      linarith
    have h3 : (k : ℝ) * Real.log ‖ι α‖ <
        k * (e * (β / 2) * Real.log (Nat.card k₀) + ε) := by
      nlinarith
    exact lt_of_mul_lt_mul_left h3 hk0.le

end Semicontinuity

end AlgebraicGeometry.WeilSheaf
