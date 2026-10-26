import Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationStatement
import Langlands.Representation.Induction.ConjugateParabolic
import Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation

/-! Normalization and induced functions for ordered refinement coordinates. -/

noncomputable section

namespace Langlands.Parabolic

open GeneralLinear Geometric
open scoped NNReal

universe uF uV

namespace RefinementCoordinatesNormalization

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData) {n : ℕ} (B D : BlockShape n) (S : BlockRefinement D)
  (e : ((i : Fin D.length) × Fin (S i).length) ≃ Fin B.length)
  (hs : ∀ a, (S a.1).size a.2 = B.size (e a))
  (hc : ∀ i k x, D.index i ((S i).index k x) =
    B.index (e ⟨i, k⟩) (Fin.cast (hs ⟨i, k⟩) x))

include hc in
private theorem block_cast_eq
    (h : (D.flatten S).length = B.length)
    (a : (i : Fin D.length) × Fin (S i).length) :
    Fin.cast h (D.flattenBlockEquiv S a) = e a := by
  let f := D.flattenBlockEquiv S
  let H : Fin (D.flatten S).length → Fin (D.flatten S).length :=
    fun k => Fin.cast h.symm (e (f.symm k))
  have hmono : StrictMono H := by
    intro k l hkl
    obtain ⟨⟨i, j⟩, rfl⟩ := f.surjective k
    obtain ⟨⟨i', j'⟩, rfl⟩ := f.surjective l
    change e (f.symm (f ⟨i, j⟩)) < e (f.symm (f ⟨i', j'⟩))
    simp only [Equiv.symm_apply_apply]
    rcases (D.flattenBlockEquiv_lt_iff S _ _).mp hkl with hi | ⟨hi, hj⟩
    · exact B.refinementBlock_lt_of_outer_lt D S e hs hc j j' hi
    · change i = i' at hi
      subst i'
      exact B.refinementBlock_strictMono D S e hs hc i hj
  have hfix : H (f a) = f a := le_antisymm hmono.apply_le hmono.le_apply
  apply Fin.ext
  have hval := congrArg Fin.val hfix
  simpa only [H, Fin.val_cast, Equiv.symm_apply_apply] using hval.symm

include hc in
private theorem shape_eq_flatten : D.flatten S = B := by
  have hlength : (D.flatten S).length = B.length := by
    have h := Fintype.card_congr ((D.flattenBlockEquiv S).symm.trans e)
    simpa only [Fintype.card_fin] using h
  have hsize : ∀ k, (D.flatten S).size k = B.size (Fin.cast hlength k) := by
    intro k
    obtain ⟨a, rfl⟩ := (D.flattenBlockEquiv S).surjective k
    rw [block_cast_eq B D S e hs hc hlength a,
      D.flatten_size_flattenBlockEquiv S a, hs a]
  have ext : ∀ {A C : BlockShape n} (h : A.length = C.length),
      (∀ k, A.size k = C.size (Fin.cast h k)) → A = C := by
    rintro ⟨l, s, hp, hsum⟩ ⟨l', s', hp', hsum'⟩ h hsize
    dsimp only at h hsize
    subst l'
    have heq : s = s' := funext hsize
    subst s'
    rfl
  exact ext hlength hsize

include hc in
/-- Exact consecutive coordinates reduce the full character comparison to
the flattened-refinement calculation. -/
theorem modulus_of_coordinates : ModulusClause F T B D S e hs := by
  have hshape := shape_eq_flatten B D S e hs hc
  subst B
  have he : e = D.flattenBlockEquiv S := by
    apply Equiv.ext
    intro a
    exact (block_cast_eq (D.flatten S) D S e hs hc rfl a).symm
  subst e
  have hlevi : (D.flatten S).leviRefinementEquiv D S (D.flattenBlockEquiv S) hs
      F.Carrier = flattenedLeviEquiv F.Carrier D S := by
    apply MulEquiv.ext
    intro m
    apply (refinedLeviEquiv F.Carrier D S).symm.injective
    simp only [BlockShape.leviRefinementEquiv, flattenedLeviEquiv,
      MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    funext i j
    rw [BlockShape.nestedLeviEquiv_apply, flattenedLeviProductEquiv_apply]
  intro m
  rw [hlevi]
  exact congrArg (fun χ : (D.flatten S).Levi F.Carrier →* ℝ≥0ˣ => χ m)
    (T.composedLeviModulus_flattened D S)

/-- The same canonical square-root construction carries a full modulus equality
through both the Levi and parabolic coordinates. -/
theorem halfModulus_of_modulus
    (hδ : ModulusClause F T B D S e hs) :
    HalfModulusClause F T B D S e hs hc := by
  have hhalf : ∀ m : B.Levi F.Carrier,
      T.composedLeviHalfModulus D S (B.leviRefinementEquiv D S e hs F.Carrier m) =
        T.leviHalfModulus B m := by
    intro m
    apply Units.ext
    change ((NNReal.sqrt (T.composedLeviModulus D S
      (B.leviRefinementEquiv D S e hs F.Carrier m) : ℝ≥0) : ℝ) : ℂ) =
      ((NNReal.sqrt (T.leviModulus B m : ℝ≥0) : ℝ) : ℂ)
    rw [hδ m]
  refine ⟨hhalf, ?_⟩
  intro q
  change T.composedLeviHalfModulus D S
    (composedLeviProjection F.Carrier D S
      (B.parabolicRefinementEquiv D S e hs F.Carrier hc q)) = _
  rw [B.composedLeviProjection_parabolicRefinementEquiv D S e hs F.Carrier hc q]
  exact hhalf (B.leviProjection F.Carrier q)

/-- Once the specified halves agree, transport at the identity conjugator
identifies the two actual smooth induced representations. -/
theorem induction_of_halfModulus
    (hhalf : HalfModulusClause F T B D S e hs hc) :
    InductionClause.{uF, uV} F T B D S e hs := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro V _ _ σ
  let σL := σ.comp (B.leviRefinementEquiv D S e hs F.Carrier).symm.toMonoidHom
  let σP := twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))
  let σC := T.composedInducingRepresentation D S σL
  let eP := B.parabolicRefinementEquiv D S e hs F.Carrier hc
  have heP : ∀ q : B.parabolic F.Carrier,
      (eP q : GeneralLinear n F.Carrier) = 1 * q * (1 : GeneralLinear n F.Carrier)⁻¹ := by
    intro q
    simp [eP]
  have hσ : ∀ q : B.parabolic F.Carrier, σC (eP q) = σP q := by
    intro q
    apply LinearMap.ext
    intro v
    change (T.composedParabolicHalfModulus D S (eP q) : ℂ) •
      σ ((B.leviRefinementEquiv D S e hs F.Carrier).symm
        (composedLeviProjection F.Carrier D S (eP q))) v =
      (T.parabolicHalfModulus B q : ℂ) • σ (B.leviProjection F.Carrier q) v
    rw [hhalf.2 q,
      B.composedLeviProjection_parabolicRefinementEquiv D S e hs F.Carrier hc q,
      MulEquiv.symm_apply_apply]
  let E := Induction.conjugateSmoothInducedEquiv (1 : GeneralLinear n F.Carrier)
    eP heP hσ
  refine ⟨E.symm, ?_, ?_⟩
  · intro f g
    change f.val.val ((1 : GeneralLinear n F.Carrier) * g) = f.val.val g
    rw [one_mul]
  · intro f g
    change f.val.val ((1 : GeneralLinear n F.Carrier)⁻¹ * g) = f.val.val g
    rw [inv_one, one_mul]

end RefinementCoordinatesNormalization

/-- The exact full normalization and identity-on-functions comparison. -/
theorem refinementCoordinatesNormalization :
    RefinementCoordinatesNormalizationTheorem.{uF, uV} := by
  intro p _ F T n B D S e hs hc
  have hδ := RefinementCoordinatesNormalization.modulus_of_coordinates F T B D S e hs hc
  have hhalf := RefinementCoordinatesNormalization.halfModulus_of_modulus
    F T B D S e hs hc hδ
  exact ⟨hδ, hhalf, RefinementCoordinatesNormalization.induction_of_halfModulus
    F T B D S e hs hc hhalf⟩

end Langlands.Parabolic
