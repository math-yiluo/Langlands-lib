import Langlands.Representation.Induction.Parabolic
import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Geometric.RefinementFunctors

/-!
# Natural normalized first adjointness

Coherent families of evaluation isomorphisms
`Hom(π, i(σ)) ≃ Hom(r(π), σ)` for the actual standard GL and refined
product-Levi functors, natural in both variables.
-/

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV uW

/-- Natural evaluation reciprocity for actual standard GL parabolics. -/
def StandardNaturalFirstAdjointnessClause : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n),
      letI := T.generalLinearTopologicalGroup n
      letI := T.leviTopologicalGroup B
      ∃ E : ∀ (π : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
          (σ : Rep.{uW} ℂ (B.Levi F.Carrier)), IsSmooth π.ρ → IsSmooth σ.ρ →
          (π.ρ.IntertwiningMap (T.normalizedParabolicInduced B σ.ρ) ≃ₗ[ℂ]
            (T.normalizedJacquet B π.ρ).IntertwiningMap σ.ρ),
        (∀ (π : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
          (σ : Rep.{uW} ℂ (B.Levi F.Carrier)) (hπ : IsSmooth π.ρ) (hσ : IsSmooth σ.ρ)
          (f : π.ρ.IntertwiningMap (T.normalizedParabolicInduced B σ.ρ)) (v : π.V),
          E π σ hπ hσ f (B.jacquetMk π.ρ v) =
            Induction.eval (B.parabolic F.Carrier)
              (twist (T.parabolicHalfModulus B) (σ.ρ.comp (B.leviProjection F.Carrier)))
              (f v) 1) ∧
        (∀ (π π' : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
          (σ : Rep.{uW} ℂ (B.Levi F.Carrier))
          (hπ : IsSmooth π.ρ) (hπ' : IsSmooth π'.ρ) (hσ : IsSmooth σ.ρ)
          (a : π'.ρ.IntertwiningMap π.ρ)
          (f : π.ρ.IntertwiningMap (T.normalizedParabolicInduced B σ.ρ))
          (x : B.JacquetModule π'.ρ),
          E π' σ hπ' hσ (f.comp a) x =
            ((E π σ hπ hσ f).comp (T.normalizedJacquetMap B a)) x) ∧
        (∀ (π : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
          (σ σ' : Rep.{uW} ℂ (B.Levi F.Carrier))
          (hπ : IsSmooth π.ρ) (hσ : IsSmooth σ.ρ) (hσ' : IsSmooth σ'.ρ)
          (b : σ.ρ.IntertwiningMap σ'.ρ)
          (f : π.ρ.IntertwiningMap (T.normalizedParabolicInduced B σ.ρ))
          (x : B.JacquetModule π.ρ),
          E π σ' hπ hσ' ((T.normalizedParabolicInducedMap B b).comp f) x =
            (b.comp (E π σ hπ hσ f)) x)

/-- Natural evaluation reciprocity for arbitrary refined product-Levi inputs. -/
def RefinedNaturalFirstAdjointnessClause : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n) (S : BlockRefinement B),
      letI := T.leviTopologicalGroup B
      ∃ E : ∀ (π : Rep.{uV} ℂ (B.Levi F.Carrier))
          (σ : Rep.{uW} ℂ (refinedLevi F.Carrier B S)), IsSmooth π.ρ → IsSmooth σ.ρ →
          (π.ρ.IntertwiningMap (T.normalizedRefinedInduced B S σ.ρ) ≃ₗ[ℂ]
            (T.normalizedRefinedJacquet B S π.ρ).IntertwiningMap σ.ρ),
        (∀ (π : Rep.{uV} ℂ (B.Levi F.Carrier))
          (σ : Rep.{uW} ℂ (refinedLevi F.Carrier B S))
          (hπ : IsSmooth π.ρ) (hσ : IsSmooth σ.ρ)
          (f : π.ρ.IntertwiningMap (T.normalizedRefinedInduced B S σ.ρ)) (v : π.V),
          E π σ hπ hσ f (refinedJacquetMk B S π.ρ v) =
            Induction.eval (refinedParabolic F.Carrier B S)
              (twist (T.refinedParabolicHalfModulus B S)
                (σ.ρ.comp (refinedLeviProjection F.Carrier B S)))
              (f v) 1) ∧
        (∀ (π π' : Rep.{uV} ℂ (B.Levi F.Carrier))
          (σ : Rep.{uW} ℂ (refinedLevi F.Carrier B S))
          (hπ : IsSmooth π.ρ) (hπ' : IsSmooth π'.ρ) (hσ : IsSmooth σ.ρ)
          (a : π'.ρ.IntertwiningMap π.ρ)
          (f : π.ρ.IntertwiningMap (T.normalizedRefinedInduced B S σ.ρ))
          (x : RefinedJacquetModule B S π'.ρ),
          E π' σ hπ' hσ (f.comp a) x =
            ((E π σ hπ hσ f).comp (T.normalizedRefinedJacquetMap B S a)) x) ∧
        (∀ (π : Rep.{uV} ℂ (B.Levi F.Carrier))
          (σ σ' : Rep.{uW} ℂ (refinedLevi F.Carrier B S))
          (hπ : IsSmooth π.ρ) (hσ : IsSmooth σ.ρ) (hσ' : IsSmooth σ'.ρ)
          (b : σ.ρ.IntertwiningMap σ'.ρ)
          (f : π.ρ.IntertwiningMap (T.normalizedRefinedInduced B S σ.ρ))
          (x : RefinedJacquetModule B S π.ρ),
          E π σ' hπ hσ' ((T.normalizedRefinedInducedMap B S b).comp f) x =
            (b.comp (E π σ hπ hσ f)) x)

/-- The standard and refined natural normalized first-adjointness families. -/
def NaturalNormalizedFirstAdjointnessStatement : Prop :=
  StandardNaturalFirstAdjointnessClause.{uF, uV, uW} ∧
    RefinedNaturalFirstAdjointnessClause.{uF, uV, uW}

end Langlands.Parabolic
