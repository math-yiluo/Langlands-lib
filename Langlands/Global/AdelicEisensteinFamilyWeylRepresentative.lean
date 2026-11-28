import Langlands.Global.AdelicEisensteinFamilyRegularComparison
import Langlands.Global.AdelicIntertwiningRepresentativeProof

/-! # The family comparison under a change of Weyl representative -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

variable {F : Type u} [Field F] [NumberField F]
  {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  {A A' : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [IsAffine Q.X.left] [IsAffine V.X.left]

omit [IsAffineHom G.X.hom] in
/-- The intertwining operator depends only on the element of `W(P, Q)` presented by the Weyl
representative: two presentations `(w₁, c₁)` and `(w₂, c₂)` with the same parameter map give
the same operator on functions invariant under `U(𝔸) M(F)`. -/
theorem _root_.Langlands.Global.AdelicGroupPoints.IsIwasawaCompact.intertwiningOperator_eq_of_weylParameter_eq
    {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
    {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] {iV : V ⟶ Q} {l' : M' ⟶ Q}
    [IsClosedImmersion (iV ≫ q).hom.hom.left] {π' : Q ⟶ M'}
    {w₁ w₂ : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c₁ c₂ : M' ⟶ M}
    (hG : IsConnectedReductive G) (hp : IsParabolicSubgroup p)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) (hl : IsRationalLeviSubgroup l)
    (hπ' : l' ≫ π' = 𝟙 M') (hw₁ : IsWeylConjugation p l q l' w₁ c₁)
    (hw₂ : IsWeylConjugation p l q l' w₂ c₂)
    (hpar : weylParameter (F := F) l c₁ π' = weylParameter l c₂ π')
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
    (hK' : IsIwasawaCompact q K) {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK.intertwiningOperator hK' iU l iV c₁ π' w₁ φ lam g =
      hK.intertwiningOperator hK' iU l iV c₂ π' w₂ φ lam g := by
  obtain ⟨y, hy⟩ := hw₁.exists_levi_of_weylParameter_eq hG hp hl hπ' hw₂ hpar
  unfold IsIwasawaCompact.intertwiningOperator
  rw [hpar]
  congr 1
  rw [hy]
  simpa only [Grp.comp_hom_hom, Category.assoc] using
    (hK.intertwiningIntegral_mul_rational_parabolic (iV ≫ q) w₁ (y ≫ l.hom.hom) hl hU hφ
      lam g).symm

/-- **Change of Weyl representative.** If `(w₁, c₁)` and `(w₂, c₂)` present the same element of
`W(P, Q)` (equal parameter maps), the family comparison for `(w₂, c₂)` implies the family
comparison for `(w₁, c₁)`: the intertwining operators agree, and so do the transported
parameters. -/
theorem FamilyRegularComparison.of_weylRepresentative
    {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
    {a : A.toGrp ⟶ M} {r : ParabolicRootPresentation p l a}
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    {hA : IsSplitTorus A.toGrp} {hT : IsSplitTorus r.data.T.toGrp}
    {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] {iV : V ⟶ Q} {l' : M' ⟶ Q}
    [IsClosedImmersion (iV ≫ q).hom.hom.left]
    {a' : A'.toGrp ⟶ M'} {r' : ParabolicRootPresentation q l' a'}
    [Mono r'.data.i.hom.hom.left] [Fintype (relativeWeylGroup r'.data.i)]
    [Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left]
    {hA' : IsSplitTorus A'.toGrp} {hT' : IsSplitTorus r'.data.T.toGrp} {π' : Q ⟶ M'}
    {w₁ w₂ : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c₁ c₂ : M' ⟶ M}
    (hG : IsConnectedReductive G) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hπ' : l' ≫ π' = 𝟙 M') (hw₁ : IsWeylConjugation p l q l' w₁ c₁)
    (hw₂ : IsWeylConjugation p l q l' w₂ c₂)
    (hpar : weylParameter (F := F) l c₁ π' = weylParameter l c₂ π')
    {K : Subgroup (AdelicGroupPoints F G)} {hK : IsIwasawaCompact p K}
    {hK' : IsIwasawaCompact q K} {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
    {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {hcalc : AdelicDifferentialCommutator F G hsmooth}
    (h : FamilyRegularComparison.{u, v, w} iU l r hA hT iV l' r' hA' hT' π' w₂ c₂ hK hK' rho
      hsmooth hcalc) :
    FamilyRegularComparison.{u, v, w} iU l r hA hT iV l' r' hA' hT' π' w₁ c₁ hK hK' rho hsmooth
      hcalc := by
  intro Ix _ φ b Db hφ hb EP DP hEP hEPser Jx _ ψ coeff D hψ hcoeff hint R
  have hop : ∀ x lam g, hK.intertwiningOperator hK' iU l iV c₁ π' w₁ (φ x) lam g =
      hK.intertwiningOperator hK' iU l iV c₂ π' w₂ (φ x) lam g := fun x lam g =>
    hK.intertwiningOperator_eq_of_weylParameter_eq hG r.isCompatible.parabolic hU
      r.isCompatible.levi hπ' hw₁ hw₂ hpar hK' (hφ x).1 lam g
  obtain ⟨R₁, hR₁⟩ := hint
  obtain ⟨m, e, O, hO, hOne, hOx⟩ := h φ b Db hφ hb EP DP hEP hEPser ψ coeff D hψ hcoeff
    ⟨R₁, fun lam hlam g => by simpa only [hop] using hR₁ lam hlam g⟩ R
  exact ⟨m, e, O, hO, hOne, fun x hx => by rw [hpar]; exact hOx x hx⟩

end Langlands.Global
