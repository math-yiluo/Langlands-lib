import Langlands.Representation.Hecke.CompactInductionModels
import Langlands.Representation.Category.Contragredient

/-! # Normalized induction from a cocompact closed subgroup and duality (Renard IV.2.1)

Renard 2026, IV.2.1, (IV.2.1.1)–(IV.2.1.2) (printed p.97 / PDF p.103). For a closed subgroup
`H` of a t.d. group `G` with `H \ G` compact, normalized induction is
`i_H^G τ = ind_H^G(τ ⊗ δ_{H\G}^{1/2})`, with the positive square root of the relative modular
character `δ_{H\G}`, and it commutes with contragredients and hermitian contragredients:
`(i_H^G τ)~ = i_H^G(τ̃)` and `(i_H^G τ)^h = i_H^G(τ^h)`.
-/

noncomputable section

universe uG v

open CategoryTheory

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.2.1, (IV.2.1.1)–(IV.2.1.2): let `G` be a Hausdorff, locally compact,
nonarchimedean group and `H` a closed subgroup with `H \ G` compact, and let `δ` be the
relative modular character `δ_{H\G}` of `H`. Then `δ` has a smooth square root `χ` with
positive real values; and for every such `χ`, normalized compact induction
`i = ind_H^G(· ⊗ χ)` satisfies `(i τ)~ ≅ i(τ̃)` naturally in `τ`, and, for every model `σ` of
`τ^h` (a `ℂ`-antilinear `H`-equivariant bijection `σ ≃ τ̃`), `i σ` is a model of `(i τ)^h`. -/
def CompactQuotientNormalizedInductionDualityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
    [LocallyCompactSpace G] [T2Space G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ [LocallyCompactSpace H] [CompactSpace (Induction.LeftQuotient H)],
      let δ : Induction.SmoothCharacter ℂ H :=
        Hecke.Homomorphism.relativeModularCharacter H.subtype continuous_subtype_val
      let IsHalfModulus : Induction.SmoothCharacter ℂ H → Prop := fun χ =>
        (∀ h : H, ∃ r : ℝ, 0 < r ∧ ((χ.toMonoidHom h : ℂˣ) : ℂ) = r) ∧
          ∀ h : H, ((χ.toMonoidHom h : ℂˣ) : ℂ) ^ 2 = ((δ.toMonoidHom h : ℂˣ) : ℂ)
      (∃ χ, IsHalfModulus χ) ∧
        ∀ χ, IsHalfModulus χ →
          let i : SmoothRep.{0, uG, v} ℂ H ⥤ SmoothRep.{0, uG, max uG v} ℂ G :=
            SmoothRep.toRep ⋙ Induction.normalizedCompactInductionFunctor H χ
          Nonempty (i.op ⋙ SmoothRep.contragredientFunctor ≅
              SmoothRep.contragredientFunctor ⋙ i) ∧
            ∀ (τ σ : SmoothRep.{0, uG, v} ℂ H) (e : σ ≃ₗ⋆[ℂ] SmoothDual τ.representation),
              (∀ (h : H) (x : σ),
                e (σ.representation h x) = smoothContragredient τ.representation h (e x)) →
              ∃ E : i.obj σ ≃ₗ⋆[ℂ] SmoothDual (i.obj τ).representation,
                ∀ (g : G) (x : i.obj σ),
                  E ((i.obj σ).representation g x) =
                    smoothContragredient (i.obj τ).representation g (E x)

end Langlands.Renard.CompactRepresentation
