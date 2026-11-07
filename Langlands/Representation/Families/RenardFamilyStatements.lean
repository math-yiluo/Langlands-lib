import Langlands.Representation.Smooth.Definitions
import Langlands.Topology.LocallyProfinite
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Renard VI.8.1 and VI.8.4: statements for general algebraic families

A family over `B` is a `B`-linear representation `ρ : Representation B G V`, so the
actions of `G` and `B` commute. Smoothness and flatness are separate hypotheses.
Compact open subgroups are open subgroups with compact carrier.
-/

open TensorProduct Langlands.Topology

namespace Langlands.Renard.AlgebraicFamily

/-- Proof step of the VI.8.1 Proposition: for every `B`-module `E`, the natural map
`E ⊗[B] V^K → E ⊗[B] V` is injective and its range is `(E ⊗[B] V)^K`, where `G` acts on
`E ⊗[B] V` through the second factor. -/
def FixedTensorComparisonStatement.{uB, uG, uV, uE} : Prop :=
  ∀ (B : Type uB) [CommRing B] [Algebra ℂ B] [IsNoetherianRing B]
    [Algebra.FiniteType ℂ B] [IsReduced B]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    IsLocallyProfinite G →
      ∀ (V : Type uV) [AddCommGroup V] [Module B V] (ρ : Representation B G V),
        IsSmooth ρ →
          ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
            ∀ (E : Type uE) [AddCommGroup E] [Module B E],
              Function.Injective ((fixedVectors ρ K.toSubgroup).subtype.lTensor E) ∧
                LinearMap.range ((fixedVectors ρ K.toSubgroup).subtype.lTensor E) =
                  fixedVectors ((Representation.trivial B G E).tprod ρ) K.toSubgroup

/-- VI.8.1 Remark: for a smooth family, `V` is flat over `B` if and only if every
compact-open fixed module `V^K` is flat over `B`. -/
def FlatnessCriterionStatement.{uB, uG, uV} : Prop :=
  ∀ (B : Type uB) [CommRing B] [Algebra ℂ B] [IsNoetherianRing B]
    [Algebra.FiniteType ℂ B] [IsReduced B]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    IsLocallyProfinite G →
      ∀ (V : Type uV) [AddCommGroup V] [Module B V] (ρ : Representation B G V),
        IsSmooth ρ →
          (Module.Flat B V ↔
            ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
              Module.Flat B (fixedVectors ρ K.toSubgroup))

/-- VI.8.1 Proposition: a smooth family is an admissible `(G, B)`-module (flat, with
finitely generated compact-open fixed modules) if and only if every compact-open fixed
module is finitely generated and projective over `B`. -/
def AdmissibilityCriterionStatement.{uB, uG, uV} : Prop :=
  ∀ (B : Type uB) [CommRing B] [Algebra ℂ B] [IsNoetherianRing B]
    [Algebra.FiniteType ℂ B] [IsReduced B]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    IsLocallyProfinite G →
      ∀ (V : Type uV) [AddCommGroup V] [Module B V] (ρ : Representation B G V),
        IsSmooth ρ →
          ((Module.Flat B V ∧
              ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
                Module.Finite B (fixedVectors ρ K.toSubgroup)) ↔
            ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
              Module.Finite B (fixedVectors ρ K.toSubgroup) ∧
                Module.Projective B (fixedVectors ρ K.toSubgroup))

/-- VI.8.1 Lemma: the specialization of an admissible `(G, B)`-module at a point
`χ : B →ₐ[ℂ] ℂ` is admissible. The specialization is `ℂ ⊗[B] V`, with `B` acting on `ℂ`
through `χ` and `g` acting by the base change of `ρ g`. -/
def SpecializationAdmissibilityStatement.{uB, uG, uV} : Prop :=
  ∀ (B : Type uB) [CommRing B] [Algebra ℂ B] [IsNoetherianRing B]
    [Algebra.FiniteType ℂ B] [IsReduced B]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    IsLocallyProfinite G →
      ∀ (V : Type uV) [AddCommGroup V] [Module B V] (ρ : Representation B G V),
        IsSmooth ρ → Module.Flat B V →
          (∀ K : OpenSubgroup G, IsCompact (K : Set G) →
            Module.Finite B (fixedVectors ρ K.toSubgroup)) →
            ∀ χ : B →ₐ[ℂ] ℂ,
              letI : Algebra B ℂ := χ.toRingHom.toAlgebra
              IsAdmissible ((Module.End.baseChangeHom B ℂ V).toMonoidHom.comp ρ)

/-- VI.8.4 Theorem: a `B`-module is finitely generated and projective if and only if
there are finitely many elements generating the unit ideal at each of which the
localization is a finitely generated free module over the localized ring. -/
def LocalFreeCoverStatement.{uB, uM} : Prop :=
  ∀ (B : Type uB) [CommRing B] [Algebra ℂ B] [IsNoetherianRing B]
    [Algebra.FiniteType ℂ B] [IsReduced B]
    (M : Type uM) [AddCommGroup M] [Module B M],
    (Module.Finite B M ∧ Module.Projective B M) ↔
      ∃ (r : ℕ) (f : Fin r → B), Ideal.span (Set.range f) = ⊤ ∧
        ∀ i : Fin r,
          Module.Finite (Localization.Away (f i))
              (LocalizedModule (Submonoid.powers (f i)) M) ∧
            Module.Free (Localization.Away (f i))
              (LocalizedModule (Submonoid.powers (f i)) M)

/-- The five statements above. -/
def Statements.{uB, uG, uV, uE, uM} : Prop :=
  FixedTensorComparisonStatement.{uB, uG, uV, uE} ∧
    FlatnessCriterionStatement.{uB, uG, uV} ∧
      AdmissibilityCriterionStatement.{uB, uG, uV} ∧
        SpecializationAdmissibilityStatement.{uB, uG, uV} ∧
          LocalFreeCoverStatement.{uB, uM}

end Langlands.Renard.AlgebraicFamily
