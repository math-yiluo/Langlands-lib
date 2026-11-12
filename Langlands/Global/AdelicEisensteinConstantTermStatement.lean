import Langlands.Global.AdelicIntertwiningConvergenceStatement

/-! # Constant terms of Eisenstein series

Bernstein–Lapid Lemma 6.10 (6.17) and Mœglin–Waldspurger II.1.7: for `φ ∈ 𝒜_P`, `λ`
sufficiently regular and a parabolic `Q = M_Q V`,
`E_Q(g, φ, λ) = ∑_w ∑_{γ ∈ Q_w(F) \ Q(F)} [M(w, λ) C_{P, P_w} φ]_{wλ}(γ g)`,
the sum running over representatives `w` of `Q(F) \ G(F) / P(F)`, with
`P_w = (P ∩ w⁻¹ Q w) U_P` and `Q_w = (Q ∩ w P w⁻¹) V`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable (F : Type u) [Field F] [NumberField F]
variable {G H H' : GroupScheme (Spec (CommRingCat.of F))}

/-- The rational points `H(F)` of `j : H → G`, as the subgroup of `G(𝔸_F)` given by the image of
the principal points of `H` under `j`. -/
def rationalImage (j : H ⟶ G) : Subgroup (AdelicGroupPoints F G) :=
  ((map F H G j).toMonoidHom.comp (rational F H)).range

/-- The coset space `H'(F) \ H(F)` of right cosets of `H'(F) ∩ H(F)` in `H(F)`, for
`j' : H' → G` and `j : H → G`. -/
abbrev RelativeRationalCosets (j' : H' ⟶ G) (j : H ⟶ G) :=
  Quotient (QuotientGroup.rightRel ((rationalImage F j').subgroupOf (rationalImage F j)))

section ConstantTerm

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine H.X.left]

/-- The constant term `∫_{H(F) \ H(𝔸)} f(h g) dh` of a function `f` on `G(𝔸)` along a closed
subgroup `j : H → G`, with `f` evaluated at the chosen representative `h ∈ H(𝔸)` of each class;
it is `0` where the integrand is not integrable. The measure is the quotient Haar measure `μ` of
`H(F) \ H(𝔸)` scaled by `μ(univ)⁻¹` (`normalizedRationalQuotientHaarMeasure`). It has total mass
one when `μ` is finite, in particular when `H(F) \ H(𝔸)` is compact, as for the unipotent groups
used below. When `μ` has infinite mass the scaled measure, and hence this integral, is `0`. -/
def subgroupConstantTerm (j : H ⟶ G) [IsClosedImmersion j.hom.hom.left]
    (f : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) : ℂ :=
  haveI : IsClosed (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j) :
      Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  ∫ x, f (((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :
      AdelicGroupPoints F G) * g)
    ∂AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G (SubgroupFunctor.range j)

end ConstantTerm

variable {F}

/-- Restriction of complex parameters along `f : P' → P`, from `X^*(P) ⊗ ℂ` to `X^*(P') ⊗ ℂ`:
on characters it is `χ ↦ χ ∘ f`. -/
def parameterRestrict (f : H' ⟶ H) :
    ComplexCharacterParameter F H →ₗ[ℂ] ComplexCharacterParameter F H' :=
  AlgebraTensorModule.map LinearMap.id (characterRestrict f).toIntLinearMap

variable {P Q U V P' Q' : GroupScheme (Spec (CommRingCat.of F))}

variable (F) in
/-- The rational points `w i` form a set of representatives of the double cosets
`Q(F) \ G(F) / P(F)`: every `z ∈ G(F)` lies in `Q(F) w_i P(F)` for exactly one `i`. -/
def IsDoubleCosetRepresentatives {I : Type*} (q : Q ⟶ G) (p : P ⟶ G)
    (w : I → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)) : Prop :=
  ∀ z ∈ rationalSubgroup F G, ∃! i, ∃ x ∈ rationalImage F q, ∃ y ∈ rationalImage F p,
    z = x * innerAdelicPoint F G (w i) * y

/-- The parabolics `f : P' → P` and `g' : Q' → Q` are the groups `P_w = (P ∩ w⁻¹ Q w) U` and
`Q_w = (Q ∩ w P w⁻¹) V` of the geometric lemma (Bernstein–Lapid Lemma 6.7), for parabolics
`P = M U` and `Q = M_Q V` of `G` with unipotent radicals `iU : U → P`, `iV : V → Q` and a rational
point `w`. They are determined through their rational points in `G(𝔸_F)`:
`P'(F) = (P(F) ∩ w⁻¹ Q(F) w) U(F)` and `Q'(F) = (Q(F) ∩ w P(F) w⁻¹) V(F)`. -/
structure IsGeometricLemmaDatum (p : P ⟶ G) (iU : U ⟶ P) (q : Q ⟶ G) (iV : V ⟶ Q)
    (f : P' ⟶ P) (g' : Q' ⟶ Q) (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) : Prop where
  rationalImage_left : rationalImage F (f ≫ p) =
    (rationalImage F p ⊓
        (rationalImage F q).map (MulAut.conj (innerAdelicPoint F G w)⁻¹).toMonoidHom) ⊔
      rationalImage F (iU ≫ p)
  rationalImage_right : rationalImage F (g' ≫ q) =
    (rationalImage F q ⊓
        (rationalImage F p).map (MulAut.conj (innerAdelicPoint F G w)).toMonoidHom) ⊔
      rationalImage F (iV ≫ q)

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Constant terms of Eisenstein series (Bernstein–Lapid Lemma 6.10 (6.17),
Mœglin–Waldspurger II.1.7). The data for `G`, `P = MU`, `r`, `K`, `rho` and `φ` are those of
`EisensteinAbsoluteConvergenceStatement`. Let further `q : Q → G` be a parabolic with geometric
unipotent radical `iV : V → Q`, let `w i` (`i` in a finite type) be rational representatives of
`Q(F) \ G(F) / P(F)`, and for each `i` let `f i : P_i → P` and `g' i : Q_i → Q` be the parabolics
`P_{w_i}`, `Q_{w_i}` of the geometric lemma, with geometric unipotent radicals `iU' i`, `iV' i`,
and let `K` also satisfy `P_i(𝔸)K = G(𝔸)`. Then there is `R` such that for every `λ` with
`B(Re λ, α) > R` for every root `α` of `A` in the unipotent radical of `P` and every `g`, the
constant term of `E(φ, λ)` along `V` at `g` is
`∑_i ∑_{γ ∈ Q_i(F) \ Q(F)} ∫_{(V_i(F) ∩ w_i U_i(𝔸) w_i⁻¹) \ V_i(𝔸)} (C_{U_i} φ)_λ(w_i⁻¹ v γ g) dv`,
where `C_{U_i} φ` is the constant term of `φ` along the unipotent radical `U_i` of `P_i`, its
twist by `λ` uses the Iwasawa height of `P_i` and the restriction of `λ` to `P_i`, and the
integrals are those defining `[M(w_i, λ) C_{U_i} φ]_{w_i λ}`. The conclusion also asserts that
these integrands are integrable and the inner sums converge absolutely. -/
def EisensteinConstantTermStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U Q V : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine V.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (q : Q ⟶ G) (iV : V ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (I : Type u) [Fintype I] (w : I → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
    (P' U' Q' V' : I → GroupScheme (Spec (CommRingCat.of F)))
    [∀ i, IsAffine (P' i).X.left] [∀ i, IsAffine (U' i).X.left] [∀ i, IsAffine (V' i).X.left]
    (f : ∀ i, P' i ⟶ P) (iU' : ∀ i, U' i ⟶ P' i) (g' : ∀ i, Q' i ⟶ Q)
    (iV' : ∀ i, V' i ⟶ Q' i)
    [∀ i, IsClosedImmersion (f i ≫ p).hom.hom.left]
    [∀ i, IsClosedImmersion (iU' i ≫ f i ≫ p).hom.hom.left]
    [∀ i, IsClosedImmersion (iV' i ≫ g' i ≫ q).hom.hom.left],
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    IsParabolicSubgroup q → LeviSubgroup.IsGeometricUnipotentRadical iV →
    IsDoubleCosetRepresentatives F q p w →
    (∀ i, IsParabolicSubgroup (f i ≫ p)) →
    (∀ i, LeviSubgroup.IsGeometricUnipotentRadical (iU' i)) →
    (∀ i, IsParabolicSubgroup (g' i ≫ q)) →
    (∀ i, LeviSubgroup.IsGeometricUnipotentRadical (iV' i)) →
    (∀ i, IsGeometricLemmaDatum p iU q iV (f i) (g' i) (w i)) →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hK' : ∀ i, IsIwasawaCompact (f i ≫ p) K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
        (K.comap (ofInfinite F G).toMonoidHom) rho φ →
      ∃ R : ℝ, ∀ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT R lam →
        ∀ g : AdelicGroupPoints F G,
          (∀ (i : I) (c : RelativeRationalCosets F (g' i ≫ q) q),
            Integrable
              ((hK' i).intertwiningIntegrand (iU' i) (iV' i ≫ g' i ≫ q) (w i)
                (subgroupConstantTerm F (iU' i ≫ f i ≫ p) φ) (parameterRestrict (f i) lam)
                (((Quotient.out c : rationalImage F q) : AdelicGroupPoints F G) * g))
              (intertwiningMeasure F (f i ≫ p) (iU' i) (iV' i ≫ g' i ≫ q)
                (innerAdelicPoint F G (w i)))) ∧
          (∀ i : I, Summable fun c : RelativeRationalCosets F (g' i ≫ q) q =>
            (hK' i).intertwiningIntegral (iU' i) (iV' i ≫ g' i ≫ q) (w i)
              (subgroupConstantTerm F (iU' i ≫ f i ≫ p) φ) (parameterRestrict (f i) lam)
              (((Quotient.out c : rationalImage F q) : AdelicGroupPoints F G) * g)) ∧
          subgroupConstantTerm F (iV ≫ q) (hK.eisensteinSeries φ lam) g =
            ∑ i : I, ∑' c : RelativeRationalCosets F (g' i ≫ q) q,
              (hK' i).intertwiningIntegral (iU' i) (iV' i ≫ g' i ≫ q) (w i)
                (subgroupConstantTerm F (iU' i ≫ f i ≫ p) φ) (parameterRestrict (f i) lam)
                (((Quotient.out c : rationalImage F q) : AdelicGroupPoints F G) * g)

end Langlands.Global
