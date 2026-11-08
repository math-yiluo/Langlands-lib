import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.CategoryTheory.Center.Basic

/-! # Representations of finite type are `ℨ(G)`-admissible (Renard VI.10.7, Theorem)

For a smooth representation `(τ, E)` of `G(F)` of finite type and every compact open subgroup
`K`, the space `E^K` of `K`-fixed vectors is a finitely generated module over the centre
`ℨ(G)` of the category of smooth representations.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.10.7, Theorem: let `τ` be a smooth representation of `G(F)` that is finitely
generated over `ℂ[G(F)]`. Then `τ` is `ℨ(G)`-admissible: for every compact open subgroup `K`
of `G(F)` there are finitely many `K`-fixed vectors `s₁, …, s_n` such that every `K`-fixed
vector is `∑ zᵢ · sᵢ` with `zᵢ` in the centre `ℨ(G) = CatCenter` of the category of smooth
representations, acting on `τ` through `zᵢ.app τ`. -/
def FiniteTypeCenterAdmissibleStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (τ : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      Module.Finite (MonoidAlgebra ℂ (rationalPoints G)) τ.representation.asModule →
      ∀ K : OpenSubgroup (rationalPoints G), IsCompact (K : Set (rationalPoints G)) →
        ∃ (n : ℕ) (s : Fin n → τ),
          (∀ i, ∀ g ∈ K, τ.representation g (s i) = s i) ∧
          ∀ x : τ, (∀ g ∈ K, τ.representation g x = x) →
            ∃ z : Fin n → CatCenter (SmoothRep.{0, u, v} ℂ (rationalPoints G)),
              x = ∑ i, SmoothRep.hom ((z i).app τ) (s i)

end Langlands.Aubert.General.RepresentedParabolic
