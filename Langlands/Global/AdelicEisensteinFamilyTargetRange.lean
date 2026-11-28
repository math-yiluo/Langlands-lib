import Langlands.Global.AdelicEisensteinFamilySourceRange

/-! # The family comparison under a change of presentation of the target parabolic -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

variable {F : Type u} [Field F] [NumberField F]
  {G P M U Q₁ M₁ V₁ Q₂ M₂ V₂ : GroupScheme (Spec (CommRingCat.of F))}
  {A T A₁ A₂ : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [IsAffine Q₁.X.left] [IsAffine V₁.X.left] [IsAffine Q₂.X.left]
  [IsAffine V₂.X.left]

omit [IsAffine P.X.left] in
/-- **Change of presentation of the target parabolic.** Let `q₁ : Q₁ → G` and `q₂ : Q₂ → G` be
identified by an isomorphism `e : Q₂ ≅ Q₁` over `G`, with the same radical and Levi images,
and with root presentations `r₁`, `r₂` whose regularity thresholds are comparable along `e`.
If the transported parameters correspond by restriction along `e`, the family comparison for
`q₂` implies the family comparison for `q₁`. -/
theorem FamilyRegularComparison.of_targetRange
    {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
    {a : A.toGrp ⟶ M} {r : ParabolicRootPresentation p l a}
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    {hA : IsSplitTorus A.toGrp} {hT : IsSplitTorus r.data.T.toGrp}
    {q₁ : Q₁ ⟶ G} [IsClosedImmersion q₁.hom.hom.left] {iV₁ : V₁ ⟶ Q₁} {l₁ : M₁ ⟶ Q₁}
    [IsClosedImmersion (iV₁ ≫ q₁).hom.hom.left] {a₁ : A₁.toGrp ⟶ M₁}
    {q₂ : Q₂ ⟶ G} [IsClosedImmersion q₂.hom.hom.left] {iV₂ : V₂ ⟶ Q₂} {l₂ : M₂ ⟶ Q₂}
    [IsClosedImmersion (iV₂ ≫ q₂).hom.hom.left] {a₂ : A₂.toGrp ⟶ M₂}
    (r₁ : ParabolicRootPresentation q₁ l₁ a₁) (r₂ : ParabolicRootPresentation q₂ l₂ a₂)
    [Mono r₁.data.i.hom.hom.left] [Fintype (relativeWeylGroup r₁.data.i)]
    [Mono (CommGroupScheme.groupHom r₁.data.f).hom.hom.left]
    [Mono r₂.data.i.hom.hom.left] [Fintype (relativeWeylGroup r₂.data.i)]
    [Mono (CommGroupScheme.groupHom r₂.data.f).hom.hom.left]
    (hA₁ : IsSplitTorus A₁.toGrp) (hT₁ : IsSplitTorus r₁.data.T.toGrp)
    (hA₂ : IsSplitTorus A₂.toGrp) (hT₂ : IsSplitTorus r₂.data.T.toGrp)
    {π₁ : Q₁ ⟶ M₁} {π₂ : Q₂ ⟶ M₂}
    {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c₁ : M₁ ⟶ M} {c₂ : M₂ ⟶ M}
    (e : Q₂ ≅ Q₁) (he : e.hom ≫ q₁ = q₂)
    (hrange : SubgroupFunctor.range q₁ = SubgroupFunctor.range q₂)
    (hV : SubgroupFunctor.range (iV₁ ≫ q₁) = SubgroupFunctor.range (iV₂ ≫ q₂))
    (hM : SubgroupFunctor.range (l₁ ≫ q₁) = SubgroupFunctor.range (l₂ ≫ q₂))
    (hW : ∀ lam, weylParameter l c₂ π₂ lam = parameterRestrict e.hom (weylParameter l c₁ π₁ lam))
    (hcomp : ∀ R : ℝ, ∃ R' : ℝ, ∀ mu : ComplexCharacterParameter F Q₁,
      r₂.IsRegularParameter hA₂ hT₂ R' (parameterRestrict e.hom mu) →
        r₁.IsRegularParameter hA₁ hT₁ R mu)
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
    (hK₁ : IsIwasawaCompact q₁ K) (hK₂ : IsIwasawaCompact q₂ K)
    {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
    {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {hcalc : AdelicDifferentialCommutator F G hsmooth}
    (h : FamilyRegularComparison.{u, v, w} iU l r hA hT iV₂ l₂ r₂ hA₂ hT₂ π₂ w c₂ hK hK₂ rho
      hsmooth hcalc) :
    FamilyRegularComparison.{u, v, w} iU l r hA hT iV₁ l₁ r₁ hA₁ hT₁ π₁ w c₁ hK hK₁ rho
      hsmooth hcalc := by
  classical
  intro Ix _ φ b Db hφ hb EP DP hEP hEPser Jx _ ψ coeff D hψ hcoeff hint R
  obtain ⟨R', hR'⟩ := hcomp R
  have hquot : parabolicQuotientSubgroup F q₁ iV₁ l₁ = parabolicQuotientSubgroup F q₂ iV₂ l₂ :=
    parabolicQuotientSubgroup_eq_of_range_eq hV hM
  have hE (ψ₀ : AdelicGroupPoints F G → ℂ) (mu : ComplexCharacterParameter F Q₁)
      (g : AdelicGroupPoints F G) :
      hK₁.eisensteinSeries ψ₀ mu g = hK₂.eisensteinSeries ψ₀ (parameterRestrict e.hom mu) g :=
    hK₁.eisensteinSeries_eq_of_range_eq hK₂ e.hom he hrange ψ₀ mu g
  have hH (mu : ComplexCharacterParameter F Q₁) (g : AdelicGroupPoints F G) :
      hK₂.heightPower (parameterRestrict e.hom mu) g = hK₁.heightPower mu g := by
    subst he
    exact hK₁.heightPower_restrict e.hom hK₂ mu g
  have hI (φ₀ : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P)
      (g : AdelicGroupPoints F G) :
      hK.intertwiningOperator hK₁ iU l iV₁ c₁ π₁ w φ₀ lam g =
        hK.intertwiningOperator hK₂ iU l iV₂ c₂ π₂ w φ₀ lam g := by
    unfold IsIwasawaCompact.intertwiningOperator
    rw [hW lam, ← LinearMap.map_neg (parameterRestrict e.hom) (weylParameter l c₁ π₁ lam), hH,
      hK.intertwiningIntegral_eq_of_range_eq_of_twist hK iU iU (iV₁ ≫ q₁) (iV₂ ≫ q₂) rfl hV w
        φ₀ lam lam rfl g]
  have hψ₂ : ∀ i₀, IsAutomorphicFunctionOn F G hsmooth hcalc
      (parabolicQuotientSubgroup F q₂ iV₂ l₂) (K.comap (ofInfinite F G).toMonoidHom) rho (ψ i₀) :=
    fun i₀ => hquot ▸ hψ i₀
  obtain ⟨Ri, hRi⟩ := hint
  obtain ⟨m, e₀, O, hO, hOne, hOx⟩ := h φ b Db hφ hb EP DP hEP hEPser ψ coeff D hψ₂ hcoeff
    ⟨Ri, fun lam hlam g => by
      rw [← hRi lam hlam g]
      exact Finset.sum_congr rfl fun x _ => by rw [hI]⟩ R'
  refine ⟨m, e₀, O, hO, hOne, fun x hx => ⟨?_, fun g => ?_⟩⟩
  · refine hR' _ ?_
    rw [← hW]
    exact (hOx x hx).1
  · rw [(hOx x hx).2 g]
    refine Finset.sum_congr rfl fun i₀ _ => ?_
    rw [hE, ← hW]

end Langlands.Global
