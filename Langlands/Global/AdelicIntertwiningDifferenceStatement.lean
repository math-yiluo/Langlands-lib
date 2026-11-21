import Langlands.Global.AdelicIntertwiningContinuationStatement
import Langlands.Global.AdelicLocalFinitenessStatement

/-! # The difference operator of Bernstein–Lapid §8.5

Bernstein–Lapid §8.5 recover `M(w, λ)φ` from the constant term along `Q` of the Eisenstein
series `E(φ, λ)`. For a regular `a ∈ A_Q`, a difference operator `D(λ)`, a polynomial in the
translation by `a` whose roots are entire in `λ`, annihilates all terms of the constant-term
formula (6.17), twisted by `-wλ`, except `M(w, λ)φ`; and `M(w, λ)φ` itself is annihilated by a
fixed polynomial `f` in the same translation, whose roots are generically different from those
of `D(λ)`. `IntertwiningConstantTermDifferenceStatement` states these facts. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Polynomial
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- The difference-operator input of Bernstein–Lapid §8.5. In the setting of
`IntertwiningMeromorphicContinuationStatement`, there are a point `t ∈ G(𝔸)` (BL's regular
`a ∈ A_Q`), a polynomial `f`, and finitely many functions `root j` on `X^*(P) ⊗ ℂ`, entire in
linear coordinates, such that

* at some parameter `λ₀` no `root j λ₀` is a root of `f`;
* for some `R₀` and every `R₀`-regular `λ`, the polynomial `f` in left translation by `t`
  annihilates `M(w, λ)φ`, and the polynomial `∏ j (X - root j λ)` in left translation by `t`
  annihilates `m_Q^{-wλ} · C_Q E(φ, λ) - M(w, λ)φ`, where `C_Q` is the constant term along the
  unipotent radical `V` of `Q`. -/
def IntertwiningConstantTermDifferenceStatement : Prop :=
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
      ∃ (t : AdelicGroupPoints F G) (f : ℂ[X]) (k : ℕ)
        (root : Fin k → ComplexCharacterParameter F P → ℂ),
        (∀ (j : Fin k) (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P),
          Differentiable ℂ (root j ∘ e)) ∧
        (∃ lam₀ : ComplexCharacterParameter F P, ∀ j, f.eval (root j lam₀) ≠ 0) ∧
        ∃ R₀ : ℝ, ∀ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT R₀ lam →
          IsTranslationPolynomialSolution t f
            (hK.intertwiningOperator hK' iU l iV c π' w φ lam) ∧
          IsTranslationPolynomialSolution t (∏ j, (X - C (root j lam)))
            (fun x => hK'.heightPower (-weylParameter l c π' lam) x *
                subgroupConstantTerm F (iV ≫ q) (hK.eisensteinSeries φ lam) x -
              hK.intertwiningOperator hK' iU l iV c π' w φ lam x)

end Langlands.Global
