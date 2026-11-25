import Langlands.Geometry.Analytic.LocalActionLifts

/-! # Statement: lifts of near-identity automorphisms to compact quasi-étale spaces -/

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

/-- Existence in Berkovich's Key Lemma 7.2 (Invent. Math. 115, 1994) for the cartesian square
with `Y = X`, `φ = 1_X`, `V = U`, `g = f` and `ψ = 1_U`. Let `f : U ⟶ X` be quasi-étale, with
`U` compact and `X` Hausdorff. For every finite set `E` of test triples on `U` there is a finite
set `D` of test triples on `X` such that every automorphism `σ` of `X` that is `D`-near the
identity is covered by an endomorphism `ψ` of `U` (`ψ ≫ f = f ≫ σ`) that is `E`-near the
identity. -/
def QuasiEtaleAutomorphismLiftStatement (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] : Prop :=
  ∀ (X U : LocalizedCategory.{u, v, v} (K := K)) (f : U ⟶ X),
    T2Space (localizedSpaceFunctor.obj X) → quasiEtale f → IsCompactSpace U →
      ∀ E : Finset (TestTriple (presentationOf U)),
        ∃ D : Finset (TestTriple (presentationOf X)), ∀ σ : Aut X,
          (∀ τ ∈ D, σ ∈ nearIdentity τ) →
            ∃ ψ : U ⟶ U, ψ ≫ f = f ≫ σ.asIso.hom ∧ ∀ τ ∈ E, IsNear τ ψ (𝟙 U)

end Langlands.Analytic.SaturatedAtlasPresentation
