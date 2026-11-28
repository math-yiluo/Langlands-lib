import Langlands.BushnellKutzko.GLSimpleTypes
import Langlands.BushnellKutzko.TypeContainment
import Langlands.Representation.Compact.FiniteMean

/-! # Injectivity of the Hecke operators of a simple type of kind (a) -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uG uW uV uF uρ uπ

/-- The Hecke operator of `x ∈ G` and `Θ : W → W` on maps `Φ : W → V`, normalized as a mean over
`J`: the mean of the orbit of `π(x) ∘ Φ ∘ Θ` under the action `j ↦ π(j) ∘ (-) ∘ ρ(j)⁻¹` of `J`
on `W →ₗ[ℂ] V`. -/
def typeHeckeMean {G : Type uG} [Group G] {J : Subgroup G} {W : Type uW} {V : Type uV}
    [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ J W) (π : Representation ℂ G V) (x : G) (Θ : W →ₗ[ℂ] W)
    (Φ : W →ₗ[ℂ] V) : W →ₗ[ℂ] V :=
  Compact.orbitMean (Representation.linHom ρ (π.comp J.subtype)) (π x ∘ₗ Φ ∘ₗ Θ)

/-- **BK93 (5.6.6), with (4.1)–(4.2) and (5.5.11): injectivity of the Hecke operators of a
simple type of kind (a).** Let `(J, ρ)` be a simple type in `GL_n(F)` exhibited by data of kind
(a) (`IsSimpleTypeData ψF S q e`, transported along `toLin`). For every `x ∈ GL_n(F)` whose
image in `Aut_F(F^n)` lies in `B_β^× = centralizerUnitGroup S.b`, every nonzero intertwiner
`Θ ∈ I_x(ρ)` and every smooth complex representation `π` of `GL_n(F)`, the Hecke operator of
`x` and `Θ` is injective on `Hom_J(ρ, π)`: if `typeHeckeMean ρ π x Θ Φ = 0` then `Φ = 0`. -/
def PositiveDepthTypeHeckeInjectivityStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ), 0 < n → ∀ (ψF : AddChar F ℂ)
    (J : Subgroup (GeneralLinear n F)) (ρ : SmoothRep.{0, uF, uρ} ℂ J)
    (S : Stratum 𝒪[F] F (Fin n → F)) (q : S.DefiningSequenceChoice) (e : ℕ),
    IsSimpleTypeData (W := (ρ : Type uρ)) ψF S q e (glRepresentationToAut ρ) →
    ∀ x : GeneralLinear n F, Matrix.GeneralLinearGroup.toLin x ∈ centralizerUnitGroup S.b →
    ∀ Θ : intertwiningSpace ρ.representation ρ.representation x, Θ ≠ 0 →
    ∀ (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F))
      (Φ : ρ.representation.IntertwiningMap (π.representation.comp J.subtype)),
      typeHeckeMean ρ.representation π.representation x Θ.toLinearMap Φ.toLinearMap = 0 →
        Φ = 0

end Langlands.BushnellKutzko
