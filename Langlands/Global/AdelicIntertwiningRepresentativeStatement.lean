import Langlands.Global.AdelicIntertwiningContinuationStatement

/-! # The intertwining operator depends only on the element of `W(P, Q)`

Bernstein–Lapid 2024, §2.1–§2.2: `W(P, Q)` is the set of cosets `wM(F)` with `w ∈ G(F)` and
`wMw⁻¹ = M'`, and `M(w, λ)` is attached to such a coset (Mœglin–Waldspurger II.1.6 (i): it
depends only on the double coset `M'(F) w M(F)`). In the Library an element of `W(P, Q)` is
presented by a pair `(w, c)` with `IsWeylConjugation p l q l' w c`, and the coset is not formed.
Two presentations of the same element induce the same map `λ ↦ wλ`; conversely, two
presentations with the same map `λ ↦ wλ` differ by an element of `M(F)`, because `w₁⁻¹ w₂`
normalizes `M` and acts trivially on its rational characters, hence centralizes the split
component `A_M`, whose centralizer is `M`.

The proposition below states the resulting independence: presentations `(w₁, c₁)`, `(w₂, c₂)` of
elements of `W(P, Q)` with the same map `λ ↦ wλ` give the same intertwining operator on
automorphic forms on `U(𝔸)M(F) \ G(𝔸)`, at every parameter and every point. It is a premise:
neither the coset argument nor the invariance of the integral is proved here. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Independence of the intertwining operator from the presentation of the Weyl element
(Bernstein–Lapid 2024, §2.1–§2.2; Mœglin–Waldspurger II.1.6 (i)). Let `P = MU` and `Q = M'V` be
parabolics of a connected reductive `G` over a number field, with rational Levi subgroups and
unipotent radicals, `π'` a Levi projection of `Q`, and `(w₁, c₁)`, `(w₂, c₂)` two Weyl
conjugations from `P` to `Q` with `weylParameter l c₁ π' = weylParameter l c₂ π'`. Then for `K`
maximal compact with `P(𝔸)K = Q(𝔸)K = G(𝔸)` and every automorphic form `φ` on
`U(𝔸)M(F) \ G(𝔸)`, `M(w₁, λ)φ(g) = M(w₂, λ)φ(g)` for all `λ` and `g`. -/
def IntertwiningRepresentativeIndependenceStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine Q.X.left] [IsAffine V.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (q : Q ⟶ G) [IsClosedImmersion q.hom.hom.left] (iV : V ⟶ Q) (l' : M' ⟶ Q)
    [IsClosedImmersion (iV ≫ q).hom.hom.left] (π' : Q ⟶ M')
    (w₁ w₂ : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c₁ c₂ : M' ⟶ M),
    IsConnectedReductive G →
    IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical iU →
    IsRationalLeviSubgroup l → IsIso (subgroupMultiplication l iU) →
    IsParabolicSubgroup q → LeviSubgroup.IsGeometricUnipotentRadical iV →
    IsRationalLeviSubgroup l' → IsIso (subgroupMultiplication l' iV) → l' ≫ π' = 𝟙 M' →
    IsWeylConjugation p l q l' w₁ c₁ → IsWeylConjugation p l q l' w₂ c₂ →
    weylParameter l c₁ π' = weylParameter l c₂ π' →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hK' : IsIwasawaCompact q K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
        (K.comap (ofInfinite F G).toMonoidHom) rho φ →
      ∀ (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G),
        hK.intertwiningOperator hK' iU l iV c₁ π' w₁ φ lam g =
          hK.intertwiningOperator hK' iU l iV c₂ π' w₂ φ lam g

end Langlands.Global
