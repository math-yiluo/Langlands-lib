import Langlands.BaseChange.CuspidalSigmaLift
import Langlands.AllField.Representation.Induction.NormalizedProductCharacterTwist
import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Twist.PullbackProof

/-! # Galois-invariant determinant twists of sigma-orbit products -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v uV uW

namespace Langlands.BaseChange

open GeneralLinear

private theorem determinant_reindex_symm {E : Type v} [Field E] {m n : ℕ}
    (e : Fin m ≃ Fin n) (g : GeneralLinear n E) :
    determinant ((GeneralLinear.reindex (R := E) e).symm g) = determinant g := by
  apply Units.ext
  change (g.val.submatrix e e).det = g.val.det
  exact Matrix.det_submatrix_equiv_self e g.val

/-- A common smooth determinant twist invariant under the powers of the
field automorphism carries a rank-reindexed orbit product to the orbit
product of the twisted first block. -/
def SigmaOrbitDeterminantTwistStatement : Prop :=
  ∀ (F : Type u) [Field F] (E : Type v) [Field E] [TopologicalSpace E]
    [ValuativeRel E] [IsNonarchimedeanLocalField E] [Algebra F E]
    (σ : E ≃ₐ[F] E) (χ : Induction.SmoothCharacter ℂ Eˣ),
    (∀ (j : ℕ) (x : Eˣ),
      χ.toMonoidHom (Units.map (σ ^ j).toRingHom.toMonoidHom x) = χ.toMonoidHom x) →
    ∀ (s n₁ n : ℕ) (hn₁ : 0 < n₁) (h : s * n₁ = n)
      (V : Type uV) (W : Type uW) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (P₁ : Representation ℂ (GeneralLinear n₁ E) V) (P : Representation ℂ (GeneralLinear n E) W),
      Nonempty (P.Equiv ((sigmaOrbitProduct σ s hn₁ P₁).comp
        (GeneralLinear.reindex (R := E) (finCongr h)).symm.toMonoidHom)) →
      Nonempty ((twist (χ.toMonoidHom.comp determinant) P).Equiv
        ((sigmaOrbitProduct σ s hn₁ (twist (χ.toMonoidHom.comp determinant) P₁)).comp
          (GeneralLinear.reindex (R := E) (finCongr h)).symm.toMonoidHom))

set_option maxHeartbeats 1500000 in
theorem sigmaOrbitDeterminantTwist : SigmaOrbitDeterminantTwistStatement.{u, v, uV, uW} := by
  intro F _ E _ _ _ _ _ σ χ hχ s n₁ n hn₁ h V W _ _ _ _ P₁ P ⟨e⟩
  let T := LocalFieldData.ofInstances E
  let B := BlockShape.uniform s n₁ hn₁
  let α := χ.toMonoidHom.comp (determinant (n := n₁))
  let P₁χ := twist α P₁
  let R (i : Fin B.length) := P₁.comp (entrywiseAut (σ ^ (i : ℕ)) n₁).toMonoidHom
  have hR : (show ∀ i : Fin B.length, Representation ℂ (GeneralLinear (B.size i) E) V from
      fun i => P₁χ.comp (entrywiseAut (σ ^ (i : ℕ)) n₁).toMonoidHom) =
      fun i => twist α (R i) := by
    funext i
    rw [twist_comp]
    congr 1
    apply MonoidHom.ext
    intro g
    change χ.toMonoidHom (determinant (Matrix.GeneralLinearGroup.map (σ ^ (i : ℕ)).toRingHom g)) =
      χ.toMonoidHom (determinant g)
    rw [Matrix.GeneralLinearGroup.map_det]
    exact hχ i (determinant g)
  have ep : (twist (χ.toMonoidHom.comp determinant) (sigmaOrbitProduct σ s hn₁ P₁)).Equiv
      (sigmaOrbitProduct σ s hn₁ P₁χ) := by
    change (twist (χ.toMonoidHom.comp determinant) (T.normalizedProductInduced B R)).Equiv
      (T.normalizedProductInduced B (fun i => P₁χ.comp (entrywiseAut (σ ^ (i : ℕ)) n₁).toMonoidHom))
    rw [hR]
    exact T.normalizedProductDeterminantTwistEquiv B χ R
  let φ := (GeneralLinear.reindex (R := E) (finCongr h)).symm.toMonoidHom
  have hd : (χ.toMonoidHom.comp (determinant (n := s * n₁))).comp φ =
      χ.toMonoidHom.comp (determinant (n := n)) := by
    apply MonoidHom.ext
    intro g
    exact congrArg χ.toMonoidHom (determinant_reindex_symm (finCongr h) g)
  have ep' := BinaryTensor.compEquiv ep φ
  rw [twist_comp, hd] at ep'
  exact ⟨(twistEquiv _ e).trans ep'⟩

end Langlands.BaseChange
