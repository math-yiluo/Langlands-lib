import Langlands.Global.AdelicIntertwiningOperator
import Langlands.Global.AdelicEisensteinConvergenceStatement

/-! # Absolute convergence of intertwining integrals

Mœglin–Waldspurger II.1.6 (i), (iv) and Bernstein–Lapid §2.2: for `φ ∈ 𝒜_P` and
`w ∈ W(P, Q)` the integral defining `M(w, λ)φ` converges absolutely and locally uniformly in
`g` and `λ` for `Re λ` sufficiently regular in the positive chamber. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Absolute convergence of intertwining integrals (Mœglin–Waldspurger II.1.6 (i), (iv);
Bernstein–Lapid §2.2). The data for `G`, `P = MU`, `r`, `K`, `rho` and `φ` are those of
`EisensteinAbsoluteConvergenceStatement`. Let further `q : Q → G` be a parabolic with geometric
unipotent radical `iV : V → Q` and rational Levi `l' : M' → Q` complementary to it, and let
`(w, c)` present an element of `W(P, Q)`. Then there is `R` such that the integrand
`v ↦ φ_λ(w⁻¹ v g)` on `(V(F) ∩ wU(𝔸)w⁻¹) \ V(𝔸)` is dominated, uniformly for `g` in any compact
set and `λ` in any compact set (in linear coordinates) on which `B(Re λ, α) > R` for every root
`α` of `A` in the unipotent radical of `P`, by one function integrable for the quotient of the
Haar measure of `V(𝔸)` normalized by `vol(V(F) \ V(𝔸)) = 1`. -/
def IntertwiningAbsoluteConvergenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine V.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (q : Q ⟶ G) (iV : V ⟶ Q) (l' : M' ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    IsParabolicSubgroup q → LeviSubgroup.IsGeometricUnipotentRadical iV →
    IsRationalLeviSubgroup l' → IsIso (subgroupMultiplication l' iV) →
    IsWeylConjugation p l q l' w c →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
        (K.comap (ofInfinite F G).toMonoidHom) rho φ →
      ∃ R : ℝ, ∀ C : Set (AdelicGroupPoints F G), IsCompact C →
        ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P)
          (Λ : Set (Fin n → ℂ)), IsCompact Λ →
          (∀ s ∈ Λ, r.IsRegularParameter hA hT R (e s)) →
          ∃ b : LeftCosetSpace
              (intertwiningRationalSubgroup F p iU (iV ≫ q) (innerAdelicPoint F G w)) → ℝ,
            Integrable b (intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w)) ∧
            ∀ x, ∀ g ∈ C, ∀ s ∈ Λ,
              ‖hK.intertwiningIntegrand iU (iV ≫ q) w φ (e s) g x‖ ≤ b x

end Langlands.Global
