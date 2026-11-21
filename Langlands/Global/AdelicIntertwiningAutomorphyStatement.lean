import Langlands.Global.AdelicIntertwiningConvergenceStatement

/-! # Uniform automorphy of intertwining operators

Mœglin–Waldspurger II.1.6 (i) and Bernstein–Lapid §2.2: for an automorphic form `φ` on
`U(𝔸)M(F) \ G(𝔸)` and `Re λ` sufficiently regular, `M(w, λ)φ` is an automorphic form on
`V(𝔸)M'(F) \ G(𝔸)`. The proof of the Lemma in Bernstein–Lapid §8.2 uses moreover that one ideal
of finite codimension in the center `𝔷` of the enveloping algebra annihilates `M(w, λ)φ` for all
such `λ`.

This file states these facts for the published operator `IsIwasawaCompact.intertwiningOperator`:

* `IntertwiningUniformAutomorphyStatement`: there are a real `R₀` and an ideal `J` of finite
  codimension in `𝔷` such that, for every `R₀`-regular `λ`, `M(w, λ)φ` satisfies
  `IsAutomorphicFunctionOn` for `V(𝔸)M'(F)` and `J` annihilates all its infinite slices;
* `IntertwiningSmoothSlicesStatement`: for `R₀`-regular `λ`, every infinite slice of
  `M(w, λ)φ` is plot-smooth;
* `IntertwiningModerateGrowthStatement`: for `R₀`-regular `λ`, `M(w, λ)φ` has moderate growth
  for the adelic norm of `rho`;
* `IntertwiningUniformCenterIdealStatement`: one ideal `J` of finite codimension in `𝔷`
  annihilates the smooth infinite slices of `M(w, λ)φ` for all `R₀`-regular `λ`.

The three latter statements are the analytic parts of the first one. Left invariance,
continuity, finiteness under the infinite compact subgroup and the finite level are not stated
here; they follow from the definition of the operator and the convergence theorem. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  InfiniteAdelicGroupPoints

/-- Uniform automorphy of intertwining operators (Mœglin–Waldspurger II.1.6 (i); Bernstein–Lapid
§2.2 and the proof of the Lemma in §8.2). The data are those of
`IntertwiningFiniteSpanStatement`. There are a real `R₀` and an ideal `J` of finite codimension
in the center of the complex enveloping algebra such that, for every `R₀`-regular `λ`, the
function `M(w, λ)φ` is automorphic on `V(𝔸)M'(F) \ G(𝔸)` for the infinite compact subgroup
`K.comap (ofInfinite F G)` and the norm of `rho`, and every element of `J` annihilates every
infinite slice of `M(w, λ)φ`. -/
def IntertwiningUniformAutomorphyStatement : Prop :=
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
      ∃ (R₀ : ℝ) (J : Ideal (AdelicEnvelopingCenter F G hsmooth)),
        Module.Finite ℂ (AdelicEnvelopingCenter F G hsmooth ⧸ J.restrictScalars ℂ) ∧
        ∀ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT R₀ lam →
          IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F q iV l')
            (K.comap (ofInfinite F G).toMonoidHom) rho
            (hK.intertwiningOperator hK' iU l iV c π' w φ lam) ∧
          ∀ z ∈ J, ∀ b : FiniteAdelicGroupPoints F G,
            ∀ h : functionInfiniteSlice F G (hK.intertwiningOperator hK' iU l iV c π' w φ lam) b ∈
                InfinitePlotSmoothFunctions F G,
              plotSmoothCenterAction F G hsmooth hcalc z
                ⟨functionInfiniteSlice F G (hK.intertwiningOperator hK' iU l iV c π' w φ lam) b,
                  h⟩ = 0

/-- Smoothness of intertwining operators in the infinite variable (Mœglin–Waldspurger II.1.6 (i)).
The data are those of `IntertwiningFiniteSpanStatement`. There is a real `R₀` such that, for
every `R₀`-regular `λ`, every infinite slice of `M(w, λ)φ` is plot-smooth. -/
def IntertwiningSmoothSlicesStatement : Prop :=
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
      ∃ R₀ : ℝ, ∀ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT R₀ lam →
        ∀ b : FiniteAdelicGroupPoints F G,
          functionInfiniteSlice F G (hK.intertwiningOperator hK' iU l iV c π' w φ lam) b ∈
            InfinitePlotSmoothFunctions F G

/-- Moderate growth of intertwining operators (Mœglin–Waldspurger II.1.6 (i)). The data are
those of `IntertwiningFiniteSpanStatement`. There is a real `R₀` such that, for every
`R₀`-regular `λ`, `M(w, λ)φ` has moderate growth for the adelic norm of `rho`. -/
def IntertwiningModerateGrowthStatement : Prop :=
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
      ∃ R₀ : ℝ, ∀ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT R₀ lam →
        HasModerateGrowthFunction F G rho (hK.intertwiningOperator hK' iU l iV c π' w φ lam)

/-- A center ideal common to all regular parameters (Bernstein–Lapid, proof of the Lemma in §8.2,
with (6.5)). The data are those of `IntertwiningFiniteSpanStatement`. There are a real `R₀` and
an ideal `J` of finite codimension in the center of the complex enveloping algebra such that,
for every `R₀`-regular `λ`, every element of `J` annihilates every plot-smooth infinite slice of
`M(w, λ)φ`. -/
def IntertwiningUniformCenterIdealStatement : Prop :=
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
      ∃ (R₀ : ℝ) (J : Ideal (AdelicEnvelopingCenter F G hsmooth)),
        Module.Finite ℂ (AdelicEnvelopingCenter F G hsmooth ⧸ J.restrictScalars ℂ) ∧
        ∀ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT R₀ lam →
          ∀ z ∈ J, ∀ b : FiniteAdelicGroupPoints F G,
            ∀ h : functionInfiniteSlice F G (hK.intertwiningOperator hK' iU l iV c π' w φ lam) b ∈
                InfinitePlotSmoothFunctions F G,
              plotSmoothCenterAction F G hsmooth hcalc z
                ⟨functionInfiniteSlice F G (hK.intertwiningOperator hK' iU l iV c π' w φ lam) b,
                  h⟩ = 0

end Langlands.Global
