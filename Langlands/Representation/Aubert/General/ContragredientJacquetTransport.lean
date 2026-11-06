import Langlands.Representation.Aubert.General.ContragredientTransport

/-! # Transport of Jacquet–contragredient isomorphisms along Levi identifications

The smooth contragredient commutes naturally with pullback along a topological group
isomorphism. Consequently a natural isomorphism `π~_U ≅ (π_O)~` between normalized Jacquet
functors of two closed subgroups `U` and `O` normalized by a common subgroup `M` transports
to the functors followed by pullback along an identification `H ≃ₜ* M`. The Levi subgroup
used for `U` may be given by a different but equal subgroup term, with an identification
having the same values in the ambient group.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uG uH uM uV

open SmoothRep

section Pullback

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The smooth contragredient commutes with pullback along a topological group
isomorphism, naturally in the representation: the components are
`contragredientPullbackIso`, which keep each linear functional. -/
def contragredientPullbackNatIso (e : H ≃ₜ* G) :
    (pullbackFunctor.{uG, uH, uV} e).op ⋙ contragredientFunctor.{0, uH, uV} ≅
      contragredientFunctor.{0, uG, uV} ⋙ pullbackFunctor e :=
  NatIso.ofComponents (fun A => contragredientPullbackIso e A.unop)
    (fun f => contragredientPullbackIso_natural e f.unop)

@[simp]
theorem contragredientPullbackNatIso_hom_app (e : H ≃ₜ* G)
    (A : (SmoothRep.{0, uG, uV} ℂ G)ᵒᵖ) :
    (contragredientPullbackNatIso e).hom.app A = (contragredientPullbackIso e A.unop).hom :=
  rfl

end Pullback

section Whisker

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type uM} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
  {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- A natural isomorphism `D ⋙ J' ≅ J.op ⋙ D` between functors to smooth
representations of `M` stays one after composing both functors with pullback along
`e : H ≃ₜ* M`. -/
def contragredientCompPullbackIso
    (J' J : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uM, uV} ℂ M) (e : H ≃ₜ* M)
    (α : contragredientFunctor.{0, uG, uV} ⋙ J' ≅ J.op ⋙ contragredientFunctor.{0, uM, uV}) :
    contragredientFunctor.{0, uG, uV} ⋙ (J' ⋙ pullbackFunctor e) ≅
      (J ⋙ pullbackFunctor e).op ⋙ contragredientFunctor.{0, uH, uV} :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight α (pullbackFunctor e) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft J.op (contragredientPullbackNatIso e).symm ≪≫
    (Functor.associator _ _ _).symm

end Whisker

section Jacquet

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Transport of a Jacquet–contragredient isomorphism along Levi identifications. Let
`U` and `O` be closed subgroups normalized by `M₂`, and suppose that
`π ↦ r_U(π~)` and `π ↦ (r_O π)~` are naturally isomorphic as functors to smooth
representations of `M₂`. Let `M₁ = M₂` be the Levi subgroup used for `U`, and let
`e₁ : H ≃ₜ* M₁` and `e₂ : H ≃ₜ* M₂` have the same values in `G`. Then
`π ↦ e₁^*(r_U(π~))` and `π ↦ (e₂^*(r_O π))~` are naturally isomorphic. -/
theorem nonempty_contragredient_normalizedJacquet_pullback_iso
    (U O : Subgroup G) {M₁ M₂ : Subgroup G} (hM : M₁ = M₂)
    (hU : IsClosed (U : Set G)) (hO : IsClosed (O : Set G))
    (hMU₁ : M₁ ≤ Subgroup.normalizer (U : Set G))
    (hMO₂ : M₂ ≤ Subgroup.normalizer (O : Set G))
    (e₁ : H ≃ₜ* M₁) (e₂ : H ≃ₜ* M₂) (he : ∀ x, (e₁ x : G) = e₂ x)
    (hiso : ∀ hMU₂ : M₂ ≤ Subgroup.normalizer (U : Set G),
      Nonempty (contragredientFunctor.{0, uG, uV} ⋙
          normalizedJacquetFunctor.{uG, uV} U M₂ hU hMU₂ ≅
        (normalizedJacquetFunctor.{uG, uV} O M₂ hO hMO₂).op ⋙
          contragredientFunctor.{0, uG, uV})) :
    Nonempty (contragredientFunctor.{0, uG, uV} ⋙
        (normalizedJacquetFunctor.{uG, uV} U M₁ hU hMU₁ ⋙ pullbackFunctor e₁) ≅
      (normalizedJacquetFunctor.{uG, uV} O M₂ hO hMO₂ ⋙ pullbackFunctor e₂).op ⋙
        contragredientFunctor.{0, uH, uV}) := by
  subst hM
  obtain rfl : e₁ = e₂ := ContinuousMulEquiv.ext fun x => Subtype.ext (he x)
  obtain ⟨α⟩ := hiso hMU₁
  exact ⟨contragredientCompPullbackIso _ _ e₁ α⟩

end Jacquet

end Langlands.Aubert.General
