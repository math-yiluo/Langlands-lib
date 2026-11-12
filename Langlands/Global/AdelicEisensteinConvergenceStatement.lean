import Langlands.Global.AdelicEisensteinSeries
import Langlands.Global.AdelicParabolicQuotient
import Langlands.Automorphic.GroupSchemeInvariantForms
import Langlands.GroupScheme.Rational.ParabolicRootPresentation
import Langlands.Representation.Plancherel.AmbientCharacterFormNaturality
import Langlands.Global.AdelicIwasawaStatement

/-! # Absolute convergence of Eisenstein series

Mœglin–Waldspurger II.1.5 and Bernstein–Lapid §2.2: for `φ ∈ 𝒜_P` the series
`E(g, φ, λ)` converges absolutely and locally uniformly in `g` and `λ` for `Re λ`
sufficiently regular in the positive chamber. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {P : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}

/-- Restriction of real character parameters along `s : A → P`, from `X^*(P) ⊗ ℝ` to the
real character space `X^*(A) ⊗ ℝ` of the commutative group scheme `A`. -/
def realParameterRestriction (s : A.toGrp ⟶ P) :
    RealCharacterParameter F P →ₗ[ℝ] RealTorusSpace.Vstar A :=
  AlgebraTensorModule.map LinearMap.id
    ((rationalCharacters.equivCharacterLattice A).toAddMonoidHom.comp
      (characterRestrict s)).toIntLinearMap

variable {G M : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

/-- The relative roots of the split component `A` that occur in the unipotent radical: the
nonzero restrictions to `A` of the positive relative roots of the presentation. -/
def _root_.Langlands.GroupScheme.ParabolicRootPresentation.unipotentRoots
    (r : ParabolicRootPresentation p l a) : Set (characterLattice A) :=
  {α | α ≠ 0 ∧ ∃ χ ∈ positiveRelativeRoots r.data.i r.data.ν, r.data.f ≫ χ = α}

/-- A complex parameter `λ` of `P` is `R`-regular when `R < B(Re λ|_A, α)` for every root `α`
of `A` in the unipotent radical, where `B` is the positive definite form on `X^*(A) ⊗ ℝ`
induced from the presentation's maximal split torus and `Re λ` is restricted from `P` to `A`. -/
def _root_.Langlands.GroupScheme.ParabolicRootPresentation.IsRegularParameter
    (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) (R : ℝ)
    (lam : ComplexCharacterParameter F P) : Prop :=
  ∀ α ∈ r.unipotentRoots,
    R < Langlands.Plancherel.weylInducedCharacterForm hA hT r.data.f r.data.i
      (realParameterRestriction (a ≫ l) (parameterRealPart F P lam)) ((1 : ℝ) ⊗ₜ[ℤ] α)

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Absolute convergence of Eisenstein series (Mœglin–Waldspurger II.1.5, Bernstein–Lapid
§2.2). Let `G` be a connected reductive group over a number field, `p : P → G` a parabolic
with unipotent radical `iU : U → P` and rational Levi `l : M → P` presented through the split
component `a : A → M` by `r`, `K` a maximal compact subgroup with `P(𝔸)K = G(𝔸)`, and `φ`
an automorphic form on `U(𝔸)M(F) \ G(𝔸)` for the archimedean part of `K` and a closed matrix
embedding `rho`. Then there is `R` such that the Eisenstein terms are dominated, uniformly for
`g` in any compact set and `λ` in any compact set (in linear coordinates) on which
`B(Re λ, α) > R` for every root `α` of `A` in the unipotent radical, by one summable
function on `P(F) \ G(F)`. Here `B` is the existing Weyl-induced positive form on
`X^*(A) ⊗ ℝ` and `Re λ` is restricted from `P` to `A`. -/
def EisensteinAbsoluteConvergenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
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
          ∃ b : ParabolicRationalCosets F p → ℝ, Summable b ∧
            ∀ c : ParabolicRationalCosets F p, ∀ g ∈ C, ∀ s ∈ Λ,
              ‖hK.eisensteinTerm φ (e s) g c‖ ≤ b c

end Langlands.Global
