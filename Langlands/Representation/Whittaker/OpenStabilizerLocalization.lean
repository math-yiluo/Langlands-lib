import Langlands.Representation.Whittaker.OpenStabilizer
import Langlands.Representation.Jacquet.LocalizationTransport
import Langlands.Representation.Tensor.CharacterLocalization

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear Geometric Jacquet.Localization

universe uK uV

variable {n : ℕ} (B : BlockShape n) (K : Type uK) [Field K]
variable {V : Fin B.length → Type uV}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

private def unipotentProductEquiv :
    (∀ i, upperUnipotent (B.size i) K) ≃*
      Subgroup.pi Set.univ (fun i => upperUnipotent (B.size i) K) where
  toFun m := ⟨fun i => (m i).val, fun i _ => (m i).property⟩
  invFun m i := ⟨m.val i, m.property i (Set.mem_univ i)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private def localizationGroupEquiv :
    (⊤ : Subgroup (openStabilizer B K)) ≃*
      Subgroup.pi Set.univ (fun i => upperUnipotent (B.size i) K) :=
  Subgroup.topEquiv.trans
    ((openStabilizerEquiv B K).trans (unipotentProductEquiv B K))

variable (π : ∀ i, Representation ℂ (Langlands.GeneralLinear (B.size i) K) (V i))
variable (ψ : AddChar K ℂ)

/-- The character quotient of the actual block-reversal stabilizer action
is the finite tensor of the original block character quotients. -/
def openStabilizerLocalizationEquiv :
    Coinvariants
        (((FiniteTensor.external π).comp (B.leviProjection K)).comp
          (stabilizerToInducing (B.parabolic K) (upperUnipotent n K)
            (B.reverseMatrix K)⁻¹))
        (⊤ : Subgroup (openStabilizer B K))
        (((entrywiseCharacter ψ n).comp (openStabilizer B K).subtype).comp
          (⊤ : Subgroup (openStabilizer B K)).subtype) ≃ₗ[ℂ]
      PiTensorProduct ℂ (fun i =>
        Coinvariants (π i) (upperUnipotent (B.size i) K)
          (entrywiseCharacter ψ (B.size i))) := by
  let e := transportEquiv
    (((FiniteTensor.external π).comp (B.leviProjection K)).comp
      (stabilizerToInducing (B.parabolic K) (upperUnipotent n K)
        (B.reverseMatrix K)⁻¹))
    (FiniteTensor.external π)
    (⊤ : Subgroup (openStabilizer B K))
    (Subgroup.pi Set.univ (fun i => upperUnipotent (B.size i) K))
    (((entrywiseCharacter ψ n).comp (openStabilizer B K).subtype).comp
      (⊤ : Subgroup (openStabilizer B K)).subtype)
    (FiniteTensor.productCharacter (fun i => upperUnipotent (B.size i) K)
      (fun i => entrywiseCharacter ψ (B.size i)))
    (localizationGroupEquiv B K)
    (LinearEquiv.refl ℂ (PiTensorProduct ℂ V))
    (fun q v => by
      change FiniteTensor.external π
        (B.leviProjection K
          (stabilizerToInducing (B.parabolic K) (upperUnipotent n K)
            (B.reverseMatrix K)⁻¹ q.val)) v =
        FiniteTensor.external π (fun i => (openStabilizerEquiv B K q.val i).val) v
      rw [openStabilizerEquiv_leviProjection])
    (fun q => by
      exact openStabilizerEquiv_character B K ψ q.val)
  exact e.trans (FiniteTensor.characterLocalizationEquiv π
    (fun i => upperUnipotent (B.size i) K)
    (fun i => entrywiseCharacter ψ (B.size i)))

@[simp]
theorem openStabilizerLocalizationEquiv_mk_tprod (v : ∀ i, V i) :
    openStabilizerLocalizationEquiv B K π ψ
      (mk
        (((FiniteTensor.external π).comp (B.leviProjection K)).comp
          (stabilizerToInducing (B.parabolic K) (upperUnipotent n K)
            (B.reverseMatrix K)⁻¹))
        (⊤ : Subgroup (openStabilizer B K))
        (((entrywiseCharacter ψ n).comp (openStabilizer B K).subtype).comp
          (⊤ : Subgroup (openStabilizer B K)).subtype)
        (PiTensorProduct.tprod ℂ v)) =
      PiTensorProduct.tprod ℂ (fun i =>
        mk (π i) (upperUnipotent (B.size i) K)
          (entrywiseCharacter ψ (B.size i)) (v i)) := by
  exact FiniteTensor.characterLocalizationEquiv_mk_tprod π
    (fun i => upperUnipotent (B.size i) K)
    (fun i => entrywiseCharacter ψ (B.size i)) v

end Langlands.Whittaker
