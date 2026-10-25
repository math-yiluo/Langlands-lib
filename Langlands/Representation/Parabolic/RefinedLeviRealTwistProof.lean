import Langlands.Representation.Parabolic.RefinedLeviRealTwistStatement
import Langlands.Representation.Induction.CharacterTwistProof
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Category.Twist

/-! # Refined induction and real-character twists -/

noncomputable section

open scoped BigOperators

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity

universe uF uV uW

private theorem blockDeterminant {R : Type uF} [CommRing R] {n : ℕ}
    (B : BlockShape n) (q : B.parabolic R) :
    determinant q.val = ∏ i, determinant (B.leviProjection R q i) := by
  let A : Matrix B.Index B.Index R := q.val.val.submatrix B.indexEquiv B.indexEquiv
  have hA : A.BlockTriangular Sigma.fst := q.property
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply,
    ← Matrix.det_submatrix_equiv_self B.indexEquiv, hA.det_fintype, Units.coe_prod]
  apply Finset.prod_congr rfl
  intro i _
  let e : {a : B.Index // a.1 = i} ≃ Fin (B.size i) :=
    { toFun := fun a => a.property ▸ a.val.2
      invFun := fun j => ⟨⟨i, j⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨j, a⟩, h⟩
        dsimp only at h
        subst j
        rfl
      right_inv := fun _ => rfl }
  rw [← Matrix.det_submatrix_equiv_self e.symm]
  rfl

private theorem realPower_parabolic {p : ℕ} [Fact p.Prime]
    {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
    (B : BlockShape n) (s : ℝ) (q : B.parabolic F.Carrier) :
    realPowerCharacter (T.determinantNorm n) s q.val =
      ∏ i, realPowerCharacter (T.determinantNorm (B.size i)) s
        (B.leviProjection F.Carrier q i) := by
  let ψ : F.Carrierˣ →* ℂˣ :=
    (positiveUnitsToComplex.comp (Units.map (NNReal.rpowMonoidHom s))).comp
      T.normalizedAbsUnits
  change ψ (determinant q.val) = ∏ i, ψ (determinant (B.leviProjection F.Carrier q i))
  rw [blockDeterminant, map_prod]

private theorem realPower_sizeTransport {p : ℕ} [Fact p.Prime]
    {F : PadicField.{uF} p} (T : F.TopologicalData) {a b : ℕ}
    (h : a = b) (s : ℝ) (g : GeneralLinear b F.Carrier) :
    realPowerCharacter (T.determinantNorm a) s
      ((reindex (finCongr h)).symm g) =
        realPowerCharacter (T.determinantNorm b) s g := by
  subst b
  rfl

private theorem refinedCharacter_restriction {p : ℕ} [Fact p.Prime]
    {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
    (B : BlockShape n) (S : BlockRefinement B) (t : Fin B.length → ℝ)
    (q : refinedParabolic F.Carrier B S) :
    T.leviRealPowerCharacter B t q.val =
      T.leviRealPowerCharacter (B.flatten S)
        (fun k => t ((B.flattenBlockEquiv S).symm k).1)
        ((flattenedLeviEquiv F.Carrier B S).symm
          (refinedLeviProjection F.Carrier B S q)) := by
  classical
  rw [T.leviRealPowerCharacter_apply, T.leviRealPowerCharacter_apply]
  calc
    _ = ∏ i, ∏ j, realPowerCharacter (T.determinantNorm ((S i).size j))
        (t i) ((S i).leviProjection F.Carrier (refinedParabolicEval F.Carrier B S i q) j) := by
      apply Finset.prod_congr rfl
      intro i _
      exact realPower_parabolic T (S i) (t i) (refinedParabolicEval F.Carrier B S i q)
    _ = ∏ ij : (i : Fin B.length) × Fin (S i).length,
        realPowerCharacter (T.determinantNorm ((S ij.1).size ij.2)) (t ij.1)
          ((S ij.1).leviProjection F.Carrier
            (refinedParabolicEval F.Carrier B S ij.1 q) ij.2) := by
      rw [Fintype.prod_sigma]
    _ = _ := by
      apply Fintype.prod_equiv (B.flattenBlockEquiv S)
      rintro ⟨i, j⟩
      simp only [Equiv.symm_apply_apply, flattenedLeviEquiv_symm_component]
      rw [realPower_sizeTransport]
      congr 2
      symm
      change ((refinedLeviEquiv F.Carrier B S).symm
        (refinedLeviEquiv F.Carrier B S
          (fun i => (S i).leviProjection F.Carrier
            (refinedParabolicEval F.Carrier B S i q)))) i j = _
      rw [MulEquiv.symm_apply_apply]

/-- Coarse character twisting on actual refined induced functions, including
transport of every specified quotient map. -/
theorem refinedLeviRealTwist : RefinedLeviRealTwistStatement.{uF, uV, uW} := by
  intro p _ F T
  let := T.topology
  intro n B S ω v₀ t
  let := T.leviTopologicalGroup B
  refine ⟨refinedCharacter_restriction T B S t, ?_⟩
  let Q := refinedParabolic F.Carrier B S
  let χ : Induction.SmoothCharacter ℂ (B.Levi F.Carrier) :=
    ⟨T.leviRealPowerCharacter B t, T.isOpen_ker_leviRealPowerCharacter B t⟩
  let σ₀ := twist (T.refinedParabolicHalfModulus B S)
    ((fineTwist T B S ω v₀ 0).ρ.comp (refinedLeviProjection F.Carrier B S))
  let σₜ := twist (T.refinedParabolicHalfModulus B S)
    ((fineTwist T B S ω v₀ t).ρ.comp (refinedLeviProjection F.Carrier B S))
  have hσ : twist (χ.toMonoidHom.comp Q.subtype) σ₀ = σₜ := by
    ext q x
    let m := (flattenedLeviEquiv F.Carrier B S).symm
      (refinedLeviProjection F.Carrier B S q)
    have hc :
        T.leviRealPowerCharacter (B.flatten S)
            (fun k => -v₀ k + t ((B.flattenBlockEquiv S).symm k).1) m =
          T.leviRealPowerCharacter B t q.val *
            T.leviRealPowerCharacter (B.flatten S) (fun k => -v₀ k) m := by
      rw [refinedCharacter_restriction T B S t q]
      rw [← MonoidHom.mul_apply, ← T.leviRealPowerCharacter_add]
      congr 2
      funext k
      exact add_comm _ _
    change (T.leviRealPowerCharacter B t q.val : ℂ) •
        ((T.refinedParabolicHalfModulus B S q : ℂ) •
          ((T.leviRealPowerCharacter (B.flatten S)
            (fun k => -v₀ k + (0 : Fin B.length → ℝ)
              ((B.flattenBlockEquiv S).symm k).1) m : ℂ) • ω.ρ m x)) =
      (T.refinedParabolicHalfModulus B S q : ℂ) •
        ((T.leviRealPowerCharacter (B.flatten S)
          (fun k => -v₀ k + t ((B.flattenBlockEquiv S).symm k).1) m : ℂ) • ω.ρ m x)
    simp only [Pi.zero_apply, add_zero, hc, Units.val_mul, mul_smul]
    exact smul_comm _ _ _
  let E := (Induction.smoothInductionTwistEquiv Q χ σ₀).trans
    (Induction.smoothInducedEquiv Q (equivOfRepresentationEq hσ))
  refine ⟨E, ?_, ?_, ?_⟩
  · intro f m
    rfl
  · intro f m
    rfl
  · intro π q₀ hq₀
    let qₜ := (twistIntertwining χ.toMonoidHom q₀).comp E.symm.toIntertwiningMap
    refine ⟨qₜ, ?_, fun _ => rfl⟩
    exact hq₀.comp E.symm.toLinearEquiv.surjective

end Langlands
