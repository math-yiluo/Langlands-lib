import Langlands.Global.AdelicEisensteinFunctionalEquationRegularComparisonStatement
import Langlands.Analysis.Meromorphic.ScalarIdentity

/-! # The regular-patch Eisenstein comparison for finite families, for fixed group data -/

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

/-- The comparison on a regular patch for finite families of inducing forms, for fixed data:
closed immersions `p : P ⟶ G`, `q : Q ⟶ G` with root presentations `r` of `(p, l, a)` and `r'`
of `(q, l', a')`, morphisms `iU : U ⟶ P` and `iV : V ⟶ Q` (with `iV ≫ q` a closed immersion),
a morphism `π' : Q ⟶ M'`, a rational point `w` of `G` with a morphism `c : M' ⟶ M`, a subgroup
`K` of `G(𝔸)` with Iwasawa coverage `hK` for `p` and `hK'` for `q`, and a matrix
representation `rho`. The only closed-immersion conditions are those on `p`, `q` and
`iV ≫ q` in the binders. No radical, Levi-retraction or Weyl-conjugation condition is part of
the predicate, and neither is the condition that `rho` be a closed embedding.

The predicate says: if the `φ v` are automorphic for `parabolicQuotientSubgroup F p iU l`, `EP`
is meromorphic and equals `∑ v, b v λ · E(φ v, λ)` for regular `λ`, the `ψ i` are automorphic
for `parabolicQuotientSubgroup F q iV l'`, and `∑ v, b v λ · M(w, λ)(φ v) = ∑ i, coeff i λ · ψ i`
for regular `λ`, then on a nonempty open patch where `wλ` is as regular as required,
`EP λ = ∑ i, coeff i λ · E(ψ i, wλ)`. -/
def FamilyRegularComparison
    {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] (iV : V ⟶ Q) (l' : M' ⟶ Q)
    [IsClosedImmersion (iV ≫ q).hom.hom.left]
    {a' : A'.toGrp ⟶ M'} (r' : ParabolicRootPresentation q l' a')
    [Mono r'.data.i.hom.hom.left] [Fintype (relativeWeylGroup r'.data.i)]
    [Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left]
    (hA' : IsSplitTorus A'.toGrp) (hT' : IsSplitTorus r'.data.T.toGrp) (π' : Q ⟶ M')
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M)
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
    (hK' : IsIwasawaCompact q K) {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) : Prop :=
  ∀ {Ix : Type v} [Fintype Ix] (φ : Ix → AdelicGroupPoints F G → ℂ)
    (b : Ix → ComplexCharacterParameter F P → ℂ) (Db : Set (ComplexCharacterParameter F P)),
    (∀ v, IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho (φ v)) →
    (∀ v, IsMeromorphicInCoordinatesOn (b v) Db) →
    ∀ (EP : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
      (DP : Set (ComplexCharacterParameter F P)),
      (∀ g, IsMeromorphicInCoordinatesOn (fun lam => EP lam g) DP) →
      (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
        EP lam g = ∑ v, b v lam * hK.eisensteinSeries (φ v) lam g) →
    ∀ {Jx : Type w} [Fintype Jx] (ψ : Jx → AdelicGroupPoints F G → ℂ)
      (coeff : Jx → ComplexCharacterParameter F P → ℂ)
      (D : Set (ComplexCharacterParameter F P)),
      (∀ i, IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F q iV l')
        (K.comap (ofInfinite F G).toMonoidHom) rho (ψ i)) →
      (∀ i, IsMeromorphicInCoordinatesOn (coeff i) D) →
      (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
        ∑ v, b v lam * hK.intertwiningOperator hK' iU l iV c π' w (φ v) lam g =
          ∑ i, coeff i lam * ψ i g) →
    ∀ R : ℝ,
      ∃ (m : ℕ) (e : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P)
        (O : Set (Fin m → ℂ)), IsOpen O ∧ O.Nonempty ∧
        ∀ x ∈ O, r'.IsRegularParameter hA' hT' R (weylParameter l c π' (e x)) ∧
          ∀ g : AdelicGroupPoints F G,
            EP (e x) g = ∑ i, coeff i (e x) * hK'.eisensteinSeries (ψ i) (weylParameter l c π' (e x)) g

namespace FamilyRegularComparison

variable {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
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
  {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : M' ⟶ M}
  {K : Subgroup (AdelicGroupPoints F G)} {hK : IsIwasawaCompact p K}
  {hK' : IsIwasawaCompact q K} {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
  {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  {hcalc : AdelicDifferentialCommutator F G hsmooth}

omit [IsAffine P.X.left] in
/-- The comparison for one inducing form is the case of a family with one member and
coefficient `1`. -/
theorem single
    (h : FamilyRegularComparison.{u, 0, 0} iU l r hA hT iV l' r' hA' hT' π' w c hK hK' rho
      hsmooth hcalc)
    (φ : AdelicGroupPoints F G → ℂ)
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho φ)
    (EP : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
    (DP : Set (ComplexCharacterParameter F P))
    (hEP : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => EP lam g) DP)
    (hEPser : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
      EP lam = hK.eisensteinSeries φ lam)
    (k : ℕ) (ψ : Fin k → AdelicGroupPoints F G → ℂ)
    (coeff : Fin k → ComplexCharacterParameter F P → ℂ) (D : Set (ComplexCharacterParameter F P))
    (hψ : ∀ i, IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F q iV l')
      (K.comap (ofInfinite F G).toMonoidHom) rho (ψ i))
    (hcoeff : ∀ i, IsMeromorphicInCoordinatesOn (coeff i) D)
    (hint : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
      hK.intertwiningOperator hK' iU l iV c π' w φ lam g = ∑ i, coeff i lam * ψ i g)
    (R : ℝ) :
    ∃ (m : ℕ) (e : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P)
      (O : Set (Fin m → ℂ)), IsOpen O ∧ O.Nonempty ∧
      ∀ x ∈ O, r'.IsRegularParameter hA' hT' R (weylParameter l c π' (e x)) ∧
        ∀ g : AdelicGroupPoints F G,
          EP (e x) g = ∑ i, coeff i (e x) *
            hK'.eisensteinSeries (ψ i) (weylParameter l c π' (e x)) g := by
  have hone : IsMeromorphicInCoordinatesOn
      (fun _ : ComplexCharacterParameter F P => (1 : ℂ)) Set.univ :=
    ⟨(hEP 1).1, fun n e => by
      have h1 : DifferentiableOn ℂ (fun _ : Fin n → ℂ => (1 : ℂ)) Set.univ :=
        differentiableOn_const 1
      exact ⟨isOpen_univ, dense_univ, isHolomorphicOn_iff_differentiableOn_scalar.mpr h1,
        fun x => ⟨Set.univ, isOpen_univ, isConnected_univ, Set.mem_univ x, fun _ => 1,
          fun _ => 1, h1.mdifferentiableOn, ⟨x, Set.mem_univ x, one_ne_zero⟩,
          isHolomorphicOn_iff_differentiableOn_scalar.mpr h1, fun _ _ => one_smul _ _⟩⟩⟩
  obtain ⟨Rp, hRp⟩ := hEPser
  obtain ⟨Ri, hRi⟩ := hint
  exact h (Ix := Fin 1) (fun _ => φ) (fun _ _ => 1) Set.univ (fun _ => hφ) (fun _ => hone) EP DP
    hEP ⟨Rp, fun lam hlam g => by simp only [Finset.univ_unique, Finset.sum_singleton, one_mul,
      hRp lam hlam]⟩ ψ coeff D hψ hcoeff
    ⟨Ri, fun lam hlam g => by simp only [Finset.univ_unique, Finset.sum_singleton, one_mul,
      hRi lam hlam g]⟩ R

end FamilyRegularComparison

end Langlands.Global
