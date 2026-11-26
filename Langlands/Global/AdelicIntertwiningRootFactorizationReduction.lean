import Langlands.Global.AdelicRootHyperplaneContinuationStatement
import Langlands.Analysis.Meromorphic.RootHyperplanePoles

/-! # Root-hyperplane continuation of intertwining operators from a root factorization

Bernstein–Lapid, Theorem 2.3 (3) and (6), number field case. Section 8.6 derives the location
of the singularities of `M(w, λ)φ` from two facts: for an elementary symmetry `s_α` the
operator `M(s_α, λ)` depends on `λ` only through `⟨λ, α^∨⟩`, and a general `w` is a product of
elementary symmetries, whose operators multiply. On a finite-dimensional space of automorphic
forms this makes the coefficients of `M(w, λ)φ` sums of products of scalar functions, each of
which depends on `λ` only through one root form.

`IntertwiningRootFactorizationStatement` asserts that some continuation of `M(w, λ)φ` has
coefficients of this shape. `intertwiningRootFactorizationReduction` proves that it implies
`IntertwiningRootHyperplaneContinuationStatement`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- A continuation of intertwining operators whose coefficients factor through root forms
(derived from Bernstein–Lapid, Theorem 2.3 (3) and §8.6, number field case). In the setting of
`IntertwiningRootHyperplaneContinuationStatement` there are finitely many functions `ψ i` on
`G(𝔸)` and scalar functions `coeff i`, meromorphic in linear coordinates with one domain `D`,
such that `M(w, λ)φ g = ∑ i, coeff i λ * ψ i g` for `Re λ` sufficiently regular, and on `D`
every `coeff i` is a sum `∑ j, ∏ t, fac i j t` of products of factors of two kinds: functions
holomorphic on all of `X^*(P) ⊗ ℂ` in every linear coordinate system, and functions meromorphic
with domain `D` that are invariant on `D` under translation by the kernel of the root form
`λ ↦ B(λ|_A, β)` of one root `β` of `A` in the unipotent radical of `P`. -/
def IntertwiningRootFactorizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine Q.X.left] [IsAffine V.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (q : Q ⟶ G) [IsClosedImmersion q.hom.hom.left] (iV : V ⟶ Q) (l' : M' ⟶ Q)
    [IsClosedImmersion (iV ≫ q).hom.hom.left] (π' : Q ⟶ M')
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    IsParabolicSubgroup q → LeviSubgroup.IsGeometricUnipotentRadical iV →
    IsRationalLeviSubgroup l' → IsIso (subgroupMultiplication l' iV) → l' ≫ π' = 𝟙 M' →
    IsWeylConjugation p l q l' w c →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hK' : IsIwasawaCompact q K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
        (K.comap (ofInfinite F G).toMonoidHom) rho φ →
      ∃ (k : ℕ) (ψ : Fin k → AdelicGroupPoints F G → ℂ)
        (coeff : Fin k → ComplexCharacterParameter F P → ℂ)
        (D : Set (ComplexCharacterParameter F P)),
        (∀ i, IsMeromorphicInCoordinatesOn (coeff i) D) ∧
        (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
          hK.intertwiningOperator hK' iU l iV c π' w φ lam g = ∑ i, coeff i lam * ψ i g) ∧
        ∃ (J n : ℕ) (fac : Fin k → Fin J → Fin n → ComplexCharacterParameter F P → ℂ),
          (∀ i j t,
            (∀ (m : ℕ) (e : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P),
              Differentiable ℂ (fac i j t ∘ e)) ∨
            (IsMeromorphicInCoordinatesOn (fac i j t) D ∧
              ∃ β ∈ r.unipotentRoots, ∀ x ∈ D, ∀ ν : ComplexCharacterParameter F P,
                r.rootFunctional hA hT β ν = 0 → x + ν ∈ D →
                  fac i j t (x + ν) = fac i j t x)) ∧
          ∀ i, ∀ x ∈ D, coeff i x = ∑ j, ∏ t, fac i j t x

/-- The reduction: a continuation of `M(w, λ)φ` whose coefficients factor through root forms
is a continuation with singularities along root hyperplanes. -/
def IntertwiningRootFactorizationReductionStatement : Prop :=
  IntertwiningRootFactorizationStatement.{u} →
    IntertwiningRootHyperplaneContinuationStatement.{u}

/-- **Root factorization gives root-hyperplane singularities.** Each factor has poles along
the hyperplanes of the unipotent root forms (an entire factor has none; an invariant factor
by the one-variable criterion `hasRootHyperplanePoles_of_kernel_invariant`), so do the
coefficients, and one root set, exponent and neighborhood serve for every point `g`
(`exists_rootPoleData_sum_mul`). -/
theorem intertwiningRootFactorizationReduction :
    IntertwiningRootFactorizationReductionStatement.{u} := by
  intro hfac F _ _ G P M U Q M' V A _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT q _ iV l' _ π' w c
    hG hU hq hV hl' hmul hπ hw K hK hK' N d rho hsmooth hcalc φ hKmax hrho hφ
  obtain ⟨k, ψ, coeff, D, hmer, hreg, J, n, fac, hfacts, hsum⟩ :=
    hfac F G P M U Q M' V A p iU l a r hA hT q iV l' π' w c hG hU hq hV hl' hmul hπ hw K hK hK'
      rho hsmooth hcalc φ hKmax hrho hφ
  refine ⟨k, ψ, coeff, D, hmer, hreg, fun m e s₀ => ?_⟩
  have hfactor : ∀ i j t, HasRootHyperplanePoles (r.rootFunctional hA hT) r.unipotentRoots
      (fac i j t) D := by
    intro i j t
    rcases hfacts i j t with hent | ⟨hm, β, hβ, hinv⟩
    · exact hasRootHyperplanePoles_of_differentiable hent
    · exact hasRootHyperplanePoles_of_kernel_invariant hm hβ hinv
  have hcoeff : ∀ i, HasRootHyperplanePoles (r.rootFunctional hA hT) r.unipotentRoots
      (coeff i) D := by
    intro i
    have hprod : ∀ j, HasRootHyperplanePoles (r.rootFunctional hA hT) r.unipotentRoots
        (fun x => ∏ t, fac i j t x) D := fun j =>
      HasRootHyperplanePoles.finset_prod Finset.univ fun t _ => hfactor i j t
    exact (HasRootHyperplanePoles.finset_sum Finset.univ fun j _ => hprod j).congr
      fun x hx => (hsum i x hx).symm
  exact exists_rootPoleData_sum_mul hcoeff ψ m e s₀

end Langlands.Global
