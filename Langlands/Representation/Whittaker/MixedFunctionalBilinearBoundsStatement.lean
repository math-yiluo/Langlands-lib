import Langlands.Representation.Filtration.MixedBilinear
import Langlands.Representation.Whittaker.FiniteLengthBilinearBounds

/-! Uniform targets assembling mixed bilinear bounds from unique functional
factors and finite exceptional sets, over two independent ambient groups. -/

namespace Langlands.MixedBilinear

universe uG uH uI uS uZ uV uW

/-- Unique functional positions in two supplied actual filtrations, over two
independent groups, reduce pairwise detection and pairwise length bounds to
total mixed length at most one. -/
def UniqueFunctionalFactorsLengthBoundStatement : Prop :=
  ∀ (G : Type uG) [Group G] (H : Type uH) [Group H] (I : Type uI)
    (U : Subgroup G) (θ : U →* ℂˣ) (U' : Subgroup H) (θ' : U' →* ℂˣ)
    (A : Rep.{uV} ℂ G) (B : Rep.{uW} ℂ H) (m n : ℕ)
    (f : ObjectRepFiltration A m) (g : ObjectRepFiltration B n)
    (a : I → G) (b : I → H) (η : I → ℂ),
    (∃! i : Fin m,
      Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ) →
    (∃! j : Fin n,
      Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ) →
    (∀ i j,
      length a b η (f.gradedRepresentation i).ρ (g.gradedRepresentation j).ρ ≠ 0 →
        Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ ∧
        Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ) →
    (∀ i j,
      Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ →
      Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ →
      length a b η (f.gradedRepresentation i).ρ (g.gradedRepresentation j).ρ ≤ 1) →
    length a b η A.ρ B.ρ ≤ 1

/-- With unique functional positions, pairwise control outside one finite
exceptional set for each actual graded pair yields one finite exceptional set,
chosen before the parameter, outside which total mixed length is at most one. -/
def UniqueFunctionalFactorsFiniteExceptionStatement : Prop :=
  ∀ (G : Type uG) [Group G] (H : Type uH) [Group H] (I : Type uI)
    (U : Subgroup G) (θ : U →* ℂˣ) (U' : Subgroup H) (θ' : U' →* ℂˣ)
    (A : Rep.{uV} ℂ G) (B : Rep.{uW} ℂ H) (m n : ℕ)
    (f : ObjectRepFiltration A m) (g : ObjectRepFiltration B n)
    (a : I → G) (b : I → H) (S : Type uS) (Z : Type uZ)
    (z : S → Z) (χ : S → I → ℂ),
    (∃! i : Fin m,
      Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ) →
    (∃! j : Fin n,
      Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ) →
    (∀ i j, ∃ E : Finset Z, ∀ s : S, z s ∉ E →
      (length a b (χ s) (f.gradedRepresentation i).ρ (g.gradedRepresentation j).ρ ≠ 0 →
        Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ ∧
        Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ) ∧
      (Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ →
        Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ →
        length a b (χ s) (f.gradedRepresentation i).ρ
          (g.gradedRepresentation j).ρ ≤ 1)) →
    ∃ E : Finset Z, ∀ s : S, z s ∉ E → length a b (χ s) A.ρ B.ρ ≤ 1

/-- Smoothness and one-dimensional total functional spaces over both groups
replace the unique-position hypotheses of the finite-exception target. -/
def FunctionalEquivFiniteExceptionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Type uH) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (I : Type uI) (U : Subgroup G), Jacquet.Localization.IsLimitOfCompactSubgroups U →
    ∀ (θ : U →* ℂˣ), IsLocallyConstant (fun u : U => (θ u : ℂ)) →
    ∀ (U' : Subgroup H), Jacquet.Localization.IsLimitOfCompactSubgroups U' →
    ∀ (θ' : U' →* ℂˣ), IsLocallyConstant (fun u : U' => (θ' u : ℂ)) →
    ∀ (A : Rep.{uV} ℂ G) (B : Rep.{uW} ℂ H) (m n : ℕ)
      (f : ObjectRepFiltration A m) (g : ObjectRepFiltration B n)
      (a : I → G) (b : I → H) (S : Type uS) (Z : Type uZ)
      (z : S → Z) (χ : S → I → ℂ),
      IsSmooth A.ρ → IsSmooth B.ρ →
      (Whittaker.functionals U θ A.ρ ≃ₗ[ℂ] ℂ) →
      (Whittaker.functionals U' θ' B.ρ ≃ₗ[ℂ] ℂ) →
      (∀ i j, ∃ E : Finset Z, ∀ s : S, z s ∉ E →
        (length a b (χ s) (f.gradedRepresentation i).ρ (g.gradedRepresentation j).ρ ≠ 0 →
          Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ ∧
          Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ) ∧
        (Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ →
          Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ →
          length a b (χ s) (f.gradedRepresentation i).ρ
            (g.gradedRepresentation j).ρ ≤ 1)) →
      ∃ E : Finset Z, ∀ s : S, z s ∉ E → length a b (χ s) A.ρ B.ρ ≤ 1

/-- Pairwise control on smooth irreducibles of the first group and admissible
irreducibles of the second group suffices for finite-length representations
with one-dimensional total functional spaces, given compact-open cofinality
in the second group and admissibility of the second total representation. -/
def AdmissibleSecondFiniteLengthExceptionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Type uH) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (I : Type uI) (U : Subgroup G), Jacquet.Localization.IsLimitOfCompactSubgroups U →
    ∀ (θ : U →* ℂˣ), IsLocallyConstant (fun u : U => (θ u : ℂ)) →
    ∀ (U' : Subgroup H), Jacquet.Localization.IsLimitOfCompactSubgroups U' →
    ∀ (θ' : U' →* ℂˣ), IsLocallyConstant (fun u : U' => (θ' u : ℂ)) →
    (∀ L : OpenSubgroup H, ∃ K : OpenSubgroup H, IsCompact (K : Set H) ∧ K ≤ L) →
    ∀ (A : Rep.{uV} ℂ G) (B : Rep.{uW} ℂ H)
      (a : I → G) (b : I → H) (S : Type uS) (Z : Type uZ)
      (z : S → Z) (χ : S → I → ℂ),
      IsSmooth A.ρ → IsAdmissible B.ρ →
      IsFiniteLength (MonoidAlgebra ℂ G) A.ρ.asModule →
      IsFiniteLength (MonoidAlgebra ℂ H) B.ρ.asModule →
      (Whittaker.functionals U θ A.ρ ≃ₗ[ℂ] ℂ) →
      (Whittaker.functionals U' θ' B.ρ ≃ₗ[ℂ] ℂ) →
      (∀ (C : Rep.{uV} ℂ G) (D : Rep.{uW} ℂ H),
        IsSmooth C.ρ → IsAdmissible D.ρ →
        Representation.IsIrreducible C.ρ → Representation.IsIrreducible D.ρ →
        ∃ E : Finset Z, ∀ s : S, z s ∉ E →
          (length a b (χ s) C.ρ D.ρ ≠ 0 →
            Whittaker.HasFunctional (N := U) (θ := θ) C.ρ ∧
            Whittaker.HasFunctional (N := U') (θ := θ') D.ρ) ∧
          (Whittaker.HasFunctional (N := U) (θ := θ) C.ρ →
            Whittaker.HasFunctional (N := U') (θ := θ') D.ρ →
            length a b (χ s) C.ρ D.ρ ≤ 1)) →
      ∃ E : Finset Z, ∀ s : S, z s ∉ E → length a b (χ s) A.ρ B.ρ ≤ 1

/-- The four uniform separate-group functional-factor and finite-exception
assembly targets, at the same independent universe levels. -/
def FunctionalFactorAssemblyStatement : Prop :=
  UniqueFunctionalFactorsLengthBoundStatement.{uG, uH, uI, uV, uW} ∧
    UniqueFunctionalFactorsFiniteExceptionStatement.{uG, uH, uI, uS, uZ, uV, uW} ∧
      FunctionalEquivFiniteExceptionStatement.{uG, uH, uI, uS, uZ, uV, uW} ∧
        AdmissibleSecondFiniteLengthExceptionStatement.{uG, uH, uI, uS, uZ, uV, uW}

end Langlands.MixedBilinear
