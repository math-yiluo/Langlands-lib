import Langlands.BaseChange.SatakeCharacter
import Langlands.BaseChange.UnramifiedBaseChangeHomStatement
import Langlands.Representation.Unramified.PrincipalSeriesHecke
import Langlands.Representation.Unramified.SphericalHeckeSpectrumExistenceProof
import Langlands.Representation.Unramified.TopHeckeOperator
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-! # Unramified base change on the spherical Hecke algebra of `GL_n` -/

noncomputable section

namespace Langlands.BaseChange

open Correspondence Langlands.Unramified MvPolynomial

universe u v

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

private theorem aeval_esymm_ofTuple {n : ℕ} (z : Fin n → ℂˣ) (i : ℕ) :
    aeval (fun j => (z j : ℂ)) (esymm (Fin n) ℂ i) =
      elementaryCoefficient (Eigenvalues.ofTuple z) i := by
  rw [esymm_eq_sum_subtype, elementaryCoefficient_ofTuple]
  simp_rw [map_sum, map_prod, aeval_X]

/-- Raising the entries of an unordered tuple to a power gives polynomial expressions
in its elementary coefficients. -/
private theorem exists_polynomial_power_elementary (n i l : ℕ) :
    ∃ Q : MvPolynomial (Fin n) ℂ, ∀ s : Eigenvalues n,
      aeval (fun j : Fin n => elementaryCoefficient s (j.val + 1)) Q =
        elementaryCoefficient (s.power l) i := by
  let powerSubstitution : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
    aeval fun j => X j ^ l
  let P := powerSubstitution (esymm (Fin n) ℂ i)
  have hP : P.IsSymmetric := by
    intro σ
    have hcomm : (rename σ).comp powerSubstitution = powerSubstitution.comp (rename σ) := by
      apply MvPolynomial.algHom_ext
      intro j
      simp [powerSubstitution]
    change ((rename σ).comp powerSubstitution) (esymm (Fin n) ℂ i) = P
    rw [hcomm, AlgHom.comp_apply, rename_esymm]
  obtain ⟨Q, hQ⟩ := esymmAlgHom_fin_surjective ℂ (le_refl n) ⟨P, hP⟩
  have hpoly : aeval (fun j : Fin n => esymm (Fin n) ℂ (j.val + 1)) Q = P :=
    (esymmAlgHom_apply Q).symm.trans (congrArg Subtype.val hQ)
  refine ⟨Q, ?_⟩
  intro s
  obtain ⟨z, rfl⟩ := Eigenvalues.ofTuple_surjective n s
  have h := congrArg (aeval (fun j => (z j : ℂ))) hpoly
  have hpower : aeval (fun j : Fin n => (z j : ℂ) ^ l) (esymm (Fin n) ℂ i) =
      elementaryCoefficient (Eigenvalues.ofTuple (fun j => z j ^ l)) i := by
    simpa only [Units.val_pow_eq_pow_val] using aeval_esymm_ofTuple (fun j => z j ^ l) i
  simpa only [P, powerSubstitution, comp_aeval_apply, map_pow, aeval_X, aeval_esymm_ofTuple,
    hpower, Eigenvalues.power_ofTuple] using h

private theorem elementaryCoefficient_power_top {n : ℕ} (s : Eigenvalues n) (l : ℕ) :
    elementaryCoefficient (s.power l) n = elementaryCoefficient s n ^ l := by
  obtain ⟨z, rfl⟩ := Eigenvalues.ofTuple_surjective n s
  have htop : esymm (Fin n) ℂ n = ∏ j : Fin n, X j := by
    have h := Finset.powersetCard_self (Finset.univ : Finset (Fin n))
    rw [Finset.card_univ, Fintype.card_fin] at h
    simp [esymm, h]
  simp only [Eigenvalues.power_ofTuple, ← aeval_esymm_ofTuple, htop, map_prod, aeval_X,
    Units.val_pow_eq_pow_val]
  exact Finset.prod_pow _ _ _

variable {p : ℕ} [Fact p.Prime]

private def heckeNormalization (F : PadicField.{u} p) (r : ℕ) (i : Fin (r + 2)) : ℂ :=
  (Real.sqrt (F.canonicalTopologicalData.residueCardinality : ℝ) : ℂ) ^
    (i.val * (r + 1 - i.val))

private theorem heckeNormalization_ne_zero (F : PadicField.{u} p) (r : ℕ) (i : Fin (r + 2)) :
    heckeNormalization F r i ≠ 0 := by
  have hq : (0 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast Nat.zero_lt_of_lt F.canonicalTopologicalData.residueCardinality_gt_one
  refine pow_ne_zero _ ?_
  exact_mod_cast (Real.sqrt_pos.2 hq).ne'

private theorem powerScalar_mem_range {F : PadicField.{u} p} {E : PadicField.{v} p}
    {r : ℕ} {ωF : ∀ _ : Eigenvalues (r + 1), SphericalHeckeAlgebra F r →ₐ[ℂ] ℂ}
    (hωF : ∀ s, IsSatakeCharacter F r s (ωF s)) (l : ℕ) (i : Fin (r + 2)) :
    (fun s => standardHeckeScalar E (s.power l) i) ∈ (AlgHom.pi ωF).range := by
  let SF := AlgHom.pi ωF
  let generators : Fin (r + 1) → SF.range := fun j =>
    SF.rangeRestrict (algebraMap ℂ (SphericalHeckeAlgebra F r) (heckeNormalization F r j.succ)⁻¹ *
      standardHeckeElement F r j.succ)
  have hgen (s : Eigenvalues (r + 1)) (j : Fin (r + 1)) :
      (generators j : Eigenvalues (r + 1) → ℂ) s = elementaryCoefficient s (j.val + 1) := by
    change ωF s (_ * standardHeckeElement F r j.succ) = _
    rw [map_mul, AlgHom.commutes, hωF s j.succ]
    change (heckeNormalization F r j.succ)⁻¹ *
      (heckeNormalization F r j.succ * elementaryCoefficient s (j.val + 1)) = _
    rw [← mul_assoc, inv_mul_cancel₀ (heckeNormalization_ne_zero F r j.succ), one_mul]
  obtain ⟨Q, hQ⟩ := exists_polynomial_power_elementary (r + 1) i.val l
  let y : SF.range := algebraMap ℂ SF.range (heckeNormalization E r i) * aeval generators Q
  have hy : (y : Eigenvalues (r + 1) → ℂ) = fun s => standardHeckeScalar E (s.power l) i := by
    funext s
    let ev : SF.range →ₐ[ℂ] ℂ := (Pi.evalAlgHom ℂ (fun _ => ℂ) s).comp SF.range.val
    change ev (algebraMap ℂ SF.range (heckeNormalization E r i) * aeval generators Q) = _
    have hev : (fun j => ev (generators j)) = fun j => elementaryCoefficient s (j.val + 1) :=
      funext (hgen s)
    rw [map_mul, AlgHom.commutes, comp_aeval_apply, hev, hQ]
    rfl
  rw [← hy]
  exact y.property

/-- The power pullback of every spherical Hecke element of `E` is in the spectral image of
the spherical Hecke algebra of `F`. -/
private theorem powerEvaluation_mem_range {F : PadicField.{u} p} {E : PadicField.{v} p}
    {r : ℕ} {ωF : ∀ _ : Eigenvalues (r + 1), SphericalHeckeAlgebra F r →ₐ[ℂ] ℂ}
    {ωE : ∀ _ : Eigenvalues (r + 1), SphericalHeckeAlgebra E r →ₐ[ℂ] ℂ}
    (hωF : ∀ s, IsSatakeCharacter F r s (ωF s))
    (hωE : ∀ s, IsSatakeCharacter E r s (ωE s))
    (l : ℕ) (φ : SphericalHeckeAlgebra E r) :
    (fun s => ωE (s.power l) φ) ∈ (AlgHom.pi ωF).range := by
  let SF := AlgHom.pi ωF
  let pullback := AlgHom.pi fun s => ωE (Eigenvalues.power s l)
  let topE := standardHeckeElement E r (Fin.last (r + 1))
  let topF := standardHeckeElement F r (Fin.last (r + 1))
  change pullback φ ∈ SF.range
  have hadj : Algebra.adjoin ℂ (Set.range (standardHeckeElement E r)) ≤ SF.range.comap pullback := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    change pullback (standardHeckeElement E r i) ∈ SF.range
    have h : pullback (standardHeckeElement E r i) = fun s => standardHeckeScalar E (s.power l) i :=
      funext fun s => hωE (s.power l) i
    rw [h]
    exact powerScalar_mem_range hωF l i
  have htop : pullback topE = SF (topF ^ l) := by
    rw [map_pow]
    funext s
    change ωE (s.power l) (standardHeckeElement E r (Fin.last (r + 1))) =
      ωF s (standardHeckeElement F r (Fin.last (r + 1))) ^ l
    rw [hωE (s.power l), hωF s, standardHeckeScalar_last, standardHeckeScalar_last]
    exact elementaryCoefficient_power_top s l
  obtain ⟨m, hm⟩ := sphericalHeckeGeneration p E r φ
  obtain ⟨uF, huF⟩ := standardHeckeElement_last_isUnit F r
  let U := (uF ^ l) ^ m
  have hU : pullback (topE ^ m) = SF (U : SphericalHeckeAlgebra F r) := by
    rw [map_pow, htop, ← map_pow]
    simp only [U, Units.val_pow_eq_pow_val, huF, topF]
  have hmem : pullback (topE ^ m * φ) ∈ SF.range := hadj hm
  have hinv := SF.range.mul_mem (SF.mem_range_self (↑U⁻¹)) hmem
  rwa [map_mul pullback, hU, ← mul_assoc, ← map_mul SF, Units.inv_mul, map_one, one_mul] at hinv

/-- The Satake character parametrization implies existence and uniqueness of the power
pullback on the spherical Hecke algebras. -/
theorem unramifiedBaseChangeHom_of_satakeCharacters
    (hF : SatakeCharacterStatement.{u}) (hE : SatakeCharacterStatement.{v}) :
    UnramifiedBaseChangeHomStatement.{u, v} := by
  intro p _ F E l r
  obtain ⟨hFex, hFsep⟩ := hF p F r
  choose ωF hωF using hFex
  choose ωE hωE using (hE p E r).1
  let SF := AlgHom.pi ωF
  let pullback := AlgHom.pi fun s => ωE (Eigenvalues.power s l)
  have hSF : Function.Injective SF := by
    intro f g h
    apply sub_eq_zero.mp
    apply hFsep
    intro s ω hω
    rw [← (hωF s).unique hω, map_sub]
    exact sub_eq_zero.mpr (congrFun h s)
  have hmem (φ) : pullback φ ∈ SF.range := powerEvaluation_mem_range hωF hωE l φ
  let eF := AlgEquiv.ofInjective SF hSF
  let b := eF.symm.toAlgHom.comp (pullback.codRestrict SF.range hmem)
  have hb (φ) : SF (b φ) = pullback φ :=
    congrArg Subtype.val (eF.apply_symm_apply (pullback.codRestrict SF.range hmem φ))
  refine ⟨b, ?_, ?_⟩
  · intro s ψF ψE hψF hψE
    rw [← (hωF s).unique hψF, ← (hωE (s.power l)).unique hψE]
    apply AlgHom.ext
    intro φ
    exact congrFun (hb φ) s
  · intro b' hb'
    apply AlgHom.ext
    intro φ
    apply hSF
    funext s
    exact (DFunLike.congr_fun (hb' s (ωF s) (ωE (s.power l)) (hωF s) (hωE _)) φ).trans
      (congrFun (hb φ) s).symm

/-- Existence and uniqueness of unramified base change on the spherical Hecke algebra. -/
theorem unramifiedBaseChangeHom : UnramifiedBaseChangeHomStatement.{u, v} :=
  unramifiedBaseChangeHom_of_satakeCharacters satakeCharacter.{u} satakeCharacter.{v}

end Langlands.BaseChange
