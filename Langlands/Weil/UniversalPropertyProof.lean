import Langlands.Weil.UniversalProperty

/-! # Universal properties of the generic integer-Frobenius pullback -/

namespace Langlands.Weil

universe u v

/-- Compatible algebraic and continuous homomorphisms factor uniquely through
the generic Weil pullback, with exactly the accepted hypotheses. -/
theorem universalProperty : UniversalProperty.{u, v} := by
  intro Γ _ _ φ
  constructor
  · intro H _ a b hab
    let h : H →* Pullback φ :=
      (a.prod b).codRestrict (pullbackSubgroup φ) (fun x => by
        change φ (a x) = frobenius (b x)
        exact DFunLike.congr_fun hab x)
    refine ⟨h, ⟨?_, ?_⟩, ?_⟩
    · ext x
      rfl
    · ext x
      rfl
    · intro k hk
      apply MonoidHom.ext
      intro x
      apply Subtype.ext
      exact Prod.ext (DFunLike.congr_fun hk.1 x) (DFunLike.congr_fun hk.2 x)
  · intro H _ _ a b hab
    let h : H →ₜ* Pullback φ :=
      { toMonoidHom :=
          (a.toMonoidHom.prod b.toMonoidHom).codRestrict (pullbackSubgroup φ)
            (fun x => by
              change φ (a x) = frobenius (b x)
              exact DFunLike.congr_fun hab x)
        continuous_toFun := (a.continuous.prodMk b.continuous).subtype_mk _ }
    refine ⟨h, ⟨?_, ?_⟩, ?_⟩
    · ext x
      rfl
    · ext x
      rfl
    · intro k hk
      apply ContinuousMonoidHom.ext
      intro x
      apply Subtype.ext
      exact Prod.ext (DFunLike.congr_fun hk.1 x) (DFunLike.congr_fun hk.2 x)

end Langlands.Weil
