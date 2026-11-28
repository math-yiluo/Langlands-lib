import Langlands.Global.AdelicEisensteinFamilyRegularComparison
import Langlands.Global.AdelicEisensteinParabolicRangeTransport
import Langlands.Global.AdelicEisensteinRegularityParabolicTransport

/-! # The family comparison under a change of presentation of the inducing parabolic -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

section Restrict

variable {F : Type u} [Field F] {H H' H'' : GroupScheme (Spec (CommRingCat.of F))}

theorem parameterRestrict_id :
    parameterRestrict (F := F) (𝟙 H) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a χ => simp [parameterRestrict, characterRestrict_id]
  | add x y hx hy => rw [map_add, hx, hy, map_add]

theorem parameterRestrict_comp (g : H'' ⟶ H') (f : H' ⟶ H) :
    parameterRestrict (F := F) (g ≫ f) = (parameterRestrict g).comp (parameterRestrict f) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a χ => simp [parameterRestrict, characterRestrict_comp]
  | add x y hx hy => rw [map_add, hx, hy, map_add]

/-- Restriction of complex parameters along an isomorphism is a linear equivalence. -/
def parameterRestrictEquiv (e : H' ≅ H) :
    ComplexCharacterParameter F H ≃ₗ[ℂ] ComplexCharacterParameter F H' :=
  LinearEquiv.ofLinearMap (parameterRestrict e.hom) (parameterRestrict e.inv)
    (by rw [← parameterRestrict_comp, e.hom_inv_id, parameterRestrict_id])
    (by rw [← parameterRestrict_comp, e.inv_hom_id, parameterRestrict_id])

@[simp] theorem parameterRestrictEquiv_apply (e : H' ≅ H) (lam : ComplexCharacterParameter F H) :
    parameterRestrictEquiv e lam = parameterRestrict e.hom lam := rfl

end Restrict

variable {F : Type u} [Field F] [NumberField F]
  {G P₁ M₁ U₁ P₂ M₂ U₂ Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  {T A₁ A₂ A' : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P₁.X.left] [IsAffine P₂.X.left] [IsAffine Q.X.left] [IsAffine V.X.left]

/-- **Change of presentation of the inducing parabolic.** Let `p₁ : P₁ → G` and `p₂ : P₂ → G`
be identified by an isomorphism `e : P₂ ≅ P₁` over `G`, with the same radical and Levi images,
and presented by the same maximal split torus, chamber and simple roots. Parameters correspond
by restriction along `e`. If the Weyl data correspond, the family comparison for `p₂` implies
the family comparison for `p₁`. -/
theorem FamilyRegularComparison.of_sourceRange
    (hG : IsConnectedReductive G)
    {p₁ : P₁ ⟶ G} [IsClosedImmersion p₁.hom.hom.left] {iU₁ : U₁ ⟶ P₁} {l₁ : M₁ ⟶ P₁}
    {a₁ : A₁.toGrp ⟶ M₁}
    {p₂ : P₂ ⟶ G} [IsClosedImmersion p₂.hom.hom.left] {iU₂ : U₂ ⟶ P₂} {l₂ : M₂ ⟶ P₂}
    {a₂ : A₂.toGrp ⟶ M₂}
    {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] [Fintype (relativeWeylGroup i)]
    {ν : cocharacterLattice T} {J : Set (characterLattice T)} {f₁ : A₁ ⟶ T} {f₂ : A₂ ⟶ T}
    [Mono (CommGroupScheme.groupHom f₁).hom.hom.left]
    [Mono (CommGroupScheme.groupHom f₂).hom.hom.left]
    (hp₁ : ParabolicRootPresentationData.IsCompatible ⟨T, i, ν, J, f₁⟩ p₁ l₁ a₁)
    (hp₂ : ParabolicRootPresentationData.IsCompatible ⟨T, i, ν, J, f₂⟩ p₂ l₂ a₂)
    (hA₁ : IsSplitTorus A₁.toGrp) (hA₂ : IsSplitTorus A₂.toGrp) (hT : IsSplitTorus T.toGrp)
    {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] {iV : V ⟶ Q} {l' : M' ⟶ Q}
    [IsClosedImmersion (iV ≫ q).hom.hom.left]
    {a' : A'.toGrp ⟶ M'} {r' : ParabolicRootPresentation q l' a'}
    [Mono r'.data.i.hom.hom.left] [Fintype (relativeWeylGroup r'.data.i)]
    [Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left]
    {hA' : IsSplitTorus A'.toGrp} {hT' : IsSplitTorus r'.data.T.toGrp} {π' : Q ⟶ M'}
    {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c₁ : M' ⟶ M₁} {c₂ : M' ⟶ M₂}
    (e : P₂ ≅ P₁) (he : e.hom ≫ p₁ = p₂)
    (hrange : SubgroupFunctor.range p₁ = SubgroupFunctor.range p₂)
    (hU : SubgroupFunctor.range (iU₁ ≫ p₁) = SubgroupFunctor.range (iU₂ ≫ p₂))
    (hM : SubgroupFunctor.range (l₁ ≫ p₁) = SubgroupFunctor.range (l₂ ≫ p₂))
    (hW : ∀ lam, weylParameter l₂ c₂ π' (parameterRestrict e.hom lam) = weylParameter l₁ c₁ π' lam)
    {K : Subgroup (AdelicGroupPoints F G)} (hK₁ : IsIwasawaCompact p₁ K)
    (hK₂ : IsIwasawaCompact p₂ K) (hK' : IsIwasawaCompact q K)
    {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
    {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {hcalc : AdelicDifferentialCommutator F G hsmooth}
    (h : FamilyRegularComparison.{u, v, w} iU₂ l₂
      (⟨⟨T, i, ν, J, f₂⟩, hp₂⟩ : ParabolicRootPresentation p₂ l₂ a₂) hA₂ hT iV l' r' hA' hT' π'
      w c₂ hK₂ hK' rho hsmooth hcalc) :
    FamilyRegularComparison.{u, v, w} iU₁ l₁
      (⟨⟨T, i, ν, J, f₁⟩, hp₁⟩ : ParabolicRootPresentation p₁ l₁ a₁) hA₁ hT iV l' r' hA' hT' π'
      w c₁ hK₁ hK' rho hsmooth hcalc := by
  classical
  intro Ix _ φ b Db hφ hb EP DP hEP hEPser Jx _ ψ coeff D hψ hcoeff hint R
  let tr : ComplexCharacterParameter F P₁ ≃ₗ[ℂ] ComplexCharacterParameter F P₂ :=
    parameterRestrictEquiv e
  have hreg (R₀ : ℝ) (lam : ComplexCharacterParameter F P₁) :=
    eisensteinRegularityParabolicTransport F G P₁ M₁ P₂ M₂ T A₁ A₂ i ν J f₁ f₂ p₁ l₁ a₁ p₂ l₂ a₂
      hp₁ hp₂ hA₁ hA₂ hT hG e.hom he R₀ lam
  have hquot : parabolicQuotientSubgroup F p₁ iU₁ l₁ = parabolicQuotientSubgroup F p₂ iU₂ l₂ :=
    parabolicQuotientSubgroup_eq_of_range_eq hU hM
  have hE (φ₀ : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P₁)
      (g : AdelicGroupPoints F G) :
      hK₁.eisensteinSeries φ₀ lam g = hK₂.eisensteinSeries φ₀ (tr lam) g :=
    hK₁.eisensteinSeries_eq_of_range_eq hK₂ e.hom he hrange φ₀ lam g
  have hI (φ₀ : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P₁)
      (g : AdelicGroupPoints F G) :
      hK₁.intertwiningOperator hK' iU₁ l₁ iV c₁ π' w φ₀ lam g =
        hK₂.intertwiningOperator hK' iU₂ l₂ iV c₂ π' w φ₀ (tr lam) g := by
    unfold IsIwasawaCompact.intertwiningOperator
    rw [show tr lam = parameterRestrict e.hom lam from rfl, hW lam,
      hK₁.intertwiningIntegral_eq_of_range_eq_of_twist hK₂ iU₁ iU₂ (iV ≫ q) (iV ≫ q) hU rfl w
        φ₀ lam (parameterRestrict e.hom lam)
        (hK₁.parameterTwist_restrict_of_comp_eq hK₂ e.hom he φ₀ lam) g]
  -- the data for `p₂`
  let b₂ (x : Ix) (mu : ComplexCharacterParameter F P₂) : ℂ := b x (tr.symm mu)
  let EP₂ (mu : ComplexCharacterParameter F P₂) : AdelicGroupPoints F G → ℂ := EP (tr.symm mu)
  let coeff₂ (i₀ : Jx) (mu : ComplexCharacterParameter F P₂) : ℂ := coeff i₀ (tr.symm mu)
  have hφ₂ : ∀ x, IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p₂ iU₂ l₂)
      (K.comap (ofInfinite F G).toMonoidHom) rho (φ x) := fun x => hquot ▸ hφ x
  obtain ⟨Rp, hRp⟩ := hEPser
  obtain ⟨Ri, hRi⟩ := hint
  obtain ⟨m, e₂, O, hO, hOne, hOx⟩ := h φ b₂ (tr.symm ⁻¹' Db) hφ₂
    (fun x => (hb x).comp_linearEquiv tr.symm) EP₂ (tr.symm ⁻¹' DP)
    (fun g => (hEP g).comp_linearEquiv tr.symm)
    ⟨Rp, fun mu hmu g => by
      have hlam : (⟨⟨T, i, ν, J, f₁⟩, hp₁⟩ : ParabolicRootPresentation p₁ l₁ a₁).IsRegularParameter
          hA₁ hT Rp (tr.symm mu) := by
        refine (hreg _ (tr.symm mu)).mp ?_
        rw [show parameterRestrict e.hom (tr.symm mu) = mu from tr.apply_symm_apply mu]
        exact hmu
      simp only [EP₂, b₂]
      rw [hRp _ hlam g]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hE, LinearEquiv.apply_symm_apply]⟩
    ψ coeff₂ (tr.symm ⁻¹' D) hψ (fun i₀ => (hcoeff i₀).comp_linearEquiv tr.symm)
    ⟨Ri, fun mu hmu g => by
      have hlam : (⟨⟨T, i, ν, J, f₁⟩, hp₁⟩ : ParabolicRootPresentation p₁ l₁ a₁).IsRegularParameter
          hA₁ hT Ri (tr.symm mu) := by
        refine (hreg _ (tr.symm mu)).mp ?_
        rw [show parameterRestrict e.hom (tr.symm mu) = mu from tr.apply_symm_apply mu]
        exact hmu
      simp only [b₂, coeff₂]
      rw [← hRi _ hlam g]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hI, LinearEquiv.apply_symm_apply]⟩ R
  refine ⟨m, e₂.trans tr.symm, O, hO, hOne, fun x hx => ?_⟩
  have hy : parameterRestrict e.hom (tr.symm (e₂ x)) = e₂ x := tr.apply_symm_apply (e₂ x)
  have hWy : weylParameter l₂ c₂ π' (e₂ x) = weylParameter l₁ c₁ π' (tr.symm (e₂ x)) := by
    rw [← hW, hy]
  change r'.IsRegularParameter hA' hT' R (weylParameter l₁ c₁ π' (tr.symm (e₂ x))) ∧
    ∀ g, EP (tr.symm (e₂ x)) g = ∑ i₀, coeff i₀ (tr.symm (e₂ x)) *
      hK'.eisensteinSeries (ψ i₀) (weylParameter l₁ c₁ π' (tr.symm (e₂ x))) g
  rw [← hWy]
  exact hOx x hx

end Langlands.Global
