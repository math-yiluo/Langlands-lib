import Langlands.Global.AdelicIntertwiningContinuationStatement
import Langlands.Analysis.Meromorphic.FiniteDimensionalValues

/-! # Reduction of the meromorphic continuation of intertwining operators

Bernstein–Lapid, Theorem 2.3 (3), number field case, says that `λ ↦ M(w, λ)φ` takes values in a
finite-dimensional subspace of `𝒜_Q` and continues meromorphically. This file splits the
published `IntertwiningMeromorphicContinuationStatement` along these two assertions:

* `IntertwiningFiniteSpanStatement` (Bernstein–Lapid §8.2, Lemma (finiteness of intertwining
  operators)): for regular `λ` the functions `M(w, λ)φ` lie in the span of finitely many
  automorphic forms on `V(𝔸)M'(F) \ G(𝔸)`;
* `IntertwiningWeakMeromorphicContinuationStatement` (Bernstein–Lapid §8.5): `λ ↦ M(w, λ)φ`
  continues to a function on `X^*(P) ⊗ ℂ` that is meromorphic, in linear coordinates, with values
  in the space of all functions on `G(𝔸)` with the topology of pointwise convergence.

`intertwiningMeromorphicContinuationReduction` proves that together they imply
`IntertwiningMeromorphicContinuationStatement`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Finiteness of intertwining operators (Bernstein–Lapid §8.2, the Lemma deduced from
Harish-Chandra's finiteness theorem). In the setting of
`IntertwiningMeromorphicContinuationStatement`, there are finitely many automorphic forms `ψ i`
on `V(𝔸)M'(F) \ G(𝔸)` and a real `R₀` such that `M(w, λ)φ` lies in the complex span of the `ψ i`
whenever `λ` is `R₀`-regular. -/
def IntertwiningFiniteSpanStatement : Prop :=
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
      ∃ (k : ℕ) (ψ : Fin k → AdelicGroupPoints F G → ℂ),
        (∀ i, IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F q iV l')
          (K.comap (ofInfinite F G).toMonoidHom) rho (ψ i)) ∧
        ∃ R₀ : ℝ, ∀ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT R₀ lam →
          hK.intertwiningOperator hK' iU l iV c π' w φ lam ∈ Submodule.span ℂ (Set.range ψ)

/-- Meromorphic continuation of intertwining operators in the topology of pointwise convergence
(Bernstein–Lapid §8.5). In the setting of `IntertwiningMeromorphicContinuationStatement`, there
are a function `E` from `X^*(P) ⊗ ℂ` to the functions on `G(𝔸)` and a set `D` such that `E` is
meromorphic in linear coordinates with domain of holomorphy `D`, for the product topology on
`G(𝔸) → ℂ`, and `E λ = M(w, λ)φ` whenever `λ` is `R₀`-regular, for some real `R₀`. -/
def IntertwiningWeakMeromorphicContinuationStatement : Prop :=
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
      ∃ (E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
        (D : Set (ComplexCharacterParameter F P)),
        IsMeromorphicInCoordinatesOn E D ∧
        ∃ R₀ : ℝ, ∀ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT R₀ lam →
          E lam = hK.intertwiningOperator hK' iU l iV c π' w φ lam

/-- The two statements above imply `IntertwiningMeromorphicContinuationStatement`. -/
def IntertwiningMeromorphicContinuationReductionStatement : Prop :=
  IntertwiningFiniteSpanStatement.{u} → IntertwiningWeakMeromorphicContinuationStatement.{u} →
    IntertwiningMeromorphicContinuationStatement.{u}

/-- Regularity of a parameter is monotone in the threshold. -/
private theorem isRegularParameter_mono {F : Type u} [Field F] [NumberField F]
    {G P M : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
    {r : ParabolicRootPresentation p l a}
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    {hA : IsSplitTorus A.toGrp} {hT : IsSplitTorus r.data.T.toGrp} {R R' : ℝ}
    {lam : ComplexCharacterParameter F P} (h : r.IsRegularParameter hA hT R' lam)
    (hR : R ≤ R') : r.IsRegularParameter hA hT R lam :=
  fun α hα => lt_of_le_of_lt hR (h α hα)

/-- Proof of the reduction. Take `R₀` the larger of the two thresholds. On the `R₀`-regular
parameters the meromorphic family `E` equals `M(w, λ)φ`, which lies in the span of the `ψ i`;
`exists_meromorphic_expansion_of_mem_span` passes to a linearly independent subfamily of the
`ψ i` and writes the coefficients as continuous linear functionals (finitely many point
evaluations) of `E λ`, which are meromorphic with the domain of holomorphy of `E`. -/
theorem intertwiningMeromorphicContinuationReduction :
    IntertwiningMeromorphicContinuationReductionStatement.{u} := by
  intro hfin hweak F _ _ G P M U Q M' V A _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT q _ iV l' _ π' w c
    hG hU hQ hV hl' hiso hπ hW K hK hK' N d rho hsmooth hcalc φ hmax hrho hφ
  obtain ⟨k, ψ, hψ, R₁, hR₁⟩ := hfin F G P M U Q M' V A p iU l a r hA hT q iV l' π' w c
    hG hU hQ hV hl' hiso hπ hW K hK hK' rho hsmooth hcalc φ hmax hrho hφ
  obtain ⟨E, D, hE, R₂, hR₂⟩ := hweak F G P M U Q M' V A p iU l a r hA hT q iV l' π' w c
    hG hU hQ hV hl' hiso hπ hW K hK hK' rho hsmooth hcalc φ hmax hrho hφ
  obtain ⟨m, ψ', coeff, hψ', hcoeff, hexp⟩ :=
    exists_meromorphic_expansion_of_mem_span
      (IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F q iV l')
        (K.comap (ofInfinite F G).toMonoidHom) rho) ψ hψ hE
      (S := {lam | r.IsRegularParameter hA hT (max R₁ R₂) lam}) (fun lam hlam => by
        rw [hR₂ lam (isRegularParameter_mono hlam (le_max_right R₁ R₂))]
        exact hR₁ lam (isRegularParameter_mono hlam (le_max_left R₁ R₂)))
  refine ⟨m, ψ', coeff, D, hψ', hcoeff, max R₁ R₂, fun lam hlam g => ?_⟩
  rw [← hR₂ lam (isRegularParameter_mono hlam (le_max_right R₁ R₂))]
  exact hexp lam hlam g

end Langlands.Global
