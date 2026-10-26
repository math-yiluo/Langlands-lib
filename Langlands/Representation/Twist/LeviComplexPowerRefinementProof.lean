import Langlands.Representation.Twist.LeviComplexPowerRefinementStatement

/-! # Complex determinant characters through actual Levi refinements -/

noncomputable section

open scoped BigOperators

namespace Langlands

open GeneralLinear Geometric

universe uF uV

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

private theorem complexPower_parabolic {p : ℕ} [Fact p.Prime]
    {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
    (B : BlockShape n) (s : ℂ) (q : B.parabolic F.Carrier) :
    T.determinantComplexPower n s q.val =
      ∏ i, T.determinantComplexPower (B.size i) s
        (B.leviProjection F.Carrier q i) := by
  let ψ : F.Carrierˣ →* ℂˣ :=
    Shahidi.complexPower T.normalizedAbsUnits s
  simp_rw [T.determinantComplexPower_eq_complexPower]
  change ψ (determinant q.val) = ∏ i, ψ (determinant (B.leviProjection F.Carrier q i))
  rw [blockDeterminant, map_prod]

private theorem complexPower_sizeTransport {p : ℕ} [Fact p.Prime]
    {F : PadicField.{uF} p} (T : F.TopologicalData) {a b : ℕ}
    (h : a = b) (s : ℂ) (g : GeneralLinear b F.Carrier) :
    T.determinantComplexPower a s
      ((reindex (finCongr h)).symm g) =
        T.determinantComplexPower b s g := by
  subst b
  rfl

private theorem refinedCharacter_restriction {p : ℕ} [Fact p.Prime]
    {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
    (B : BlockShape n) (S : BlockRefinement B) (t : Fin B.length → ℂ)
    (q : refinedParabolic F.Carrier B S) :
    T.leviComplexPowerCharacter B t q.val =
      T.leviComplexPowerCharacter (B.flatten S)
        (fun k => t ((B.flattenBlockEquiv S).symm k).1)
        ((flattenedLeviEquiv F.Carrier B S).symm
          (refinedLeviProjection F.Carrier B S q)) := by
  classical
  rw [T.leviComplexPowerCharacter_apply, T.leviComplexPowerCharacter_apply]
  calc
    _ = ∏ i, ∏ j, T.determinantComplexPower ((S i).size j)
        (t i) ((S i).leviProjection F.Carrier (refinedParabolicEval F.Carrier B S i q) j) := by
      apply Finset.prod_congr rfl
      intro i _
      exact complexPower_parabolic T (S i) (t i) (refinedParabolicEval F.Carrier B S i q)
    _ = ∏ ij : (i : Fin B.length) × Fin (S i).length,
        T.determinantComplexPower ((S ij.1).size ij.2) (t ij.1)
          ((S ij.1).leviProjection F.Carrier
            (refinedParabolicEval F.Carrier B S ij.1 q) ij.2) := by
      rw [Fintype.prod_sigma]
    _ = _ := by
      apply Fintype.prod_equiv (B.flattenBlockEquiv S)
      rintro ⟨i, j⟩
      simp only [Equiv.symm_apply_apply, flattenedLeviEquiv_symm_component]
      rw [complexPower_sizeTransport]
      congr 2
      symm
      change ((refinedLeviEquiv F.Carrier B S).symm
        (refinedLeviEquiv F.Carrier B S
          (fun i => (S i).leviProjection F.Carrier
            (refinedParabolicEval F.Carrier B S i q)))) i j = _
      rw [MulEquiv.symm_apply_apply]

/-- Restriction through the actual refined parabolic, refined-Levi character
identity and addition of a coarse twist to any fine complex twist. -/
theorem leviComplexPowerRefinement : LeviComplexPowerRefinementStatement.{uF, uV} := by
  intro p _ F T n B S z
  have hLevi (m : refinedLevi F.Carrier B S) :
      T.leviComplexPowerCharacter B z m.val =
        T.leviComplexPowerCharacter (B.flatten S)
          (fun k => z ((B.flattenBlockEquiv S).symm k).1)
          ((flattenedLeviEquiv F.Carrier B S).symm m) := by
    simpa only [refinedLeviSection_val, refinedLeviProjection_section] using
      refinedCharacter_restriction T B S z (refinedLeviSection F.Carrier B S m)
  refine ⟨refinedCharacter_restriction T B S z, ?_, ?_⟩
  · exact MonoidHom.ext hLevi
  · intro V _ _ ρ a
    ext m v
    change (T.leviComplexPowerCharacter B z m.val : ℂ) •
        ((T.leviComplexPowerCharacter (B.flatten S) a
          ((flattenedLeviEquiv F.Carrier B S).symm m) : ℂ) •
          ρ ((flattenedLeviEquiv F.Carrier B S).symm m) v) =
      (T.leviComplexPowerCharacter (B.flatten S)
        (a + fun k => z ((B.flattenBlockEquiv S).symm k).1)
        ((flattenedLeviEquiv F.Carrier B S).symm m) : ℂ) •
          ρ ((flattenedLeviEquiv F.Carrier B S).symm m) v
    rw [hLevi, T.leviComplexPowerCharacter_add, MonoidHom.mul_apply,
      Units.val_mul, mul_smul]
    exact smul_comm _ _ _

end Langlands
