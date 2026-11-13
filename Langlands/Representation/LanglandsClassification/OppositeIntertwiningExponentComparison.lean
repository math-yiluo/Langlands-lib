import Langlands.Representation.LanglandsClassification.CrossLeviPieceWeylParameter
import Langlands.Representation.LanglandsClassification.LanglandsTripletRegularityProof
import Langlands.Representation.Intertwining.CentralActionQuotientFiniteness

/-! # Exponent comparison from a nonzero map into an opposite induction -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands

/-- An intertwining map between two representations whose action kernels, for the same
group algebra `ℂ[B]` acting through `φ`, are comaximal is zero. -/
theorem IntertwiningMap.eq_zero_of_groupAlgebraKernel_sup_eq_top
    {H B V W : Type*} [Group H] [CommGroup B]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ H V} {τ : Representation ℂ H W}
    (f : ρ.IntertwiningMap τ) (φ : B →* H)
    (h : groupAlgebraKernel ρ φ ⊔ groupAlgebraKernel τ φ = ⊤) : f = 0 := by
  have h1 : (1 : MonoidAlgebra ℂ B) ∈ groupAlgebraKernel ρ φ ⊔ groupAlgebraKernel τ φ := by
    rw [h]
    exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp h1
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  have hv : v = Representation.asAlgebraHom (ρ.comp φ) x v +
      Representation.asAlgebraHom (ρ.comp φ) y v := by
    rw [← LinearMap.add_apply, ← map_add, hxy, map_one, Module.End.one_apply]
  change f v = 0
  rw [hv, map_add, (mem_groupAlgebraKernel_iff ρ φ x).mp hx,
    intertwining_groupAlgebra_apply f φ y v, (mem_groupAlgebraKernel_iff τ φ y).mp hy]
  simp

end Langlands

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme RealTorusSpace

set_option backward.isDefEq.respectTransparency false in
/-- One half of the comparison in Renard VII.4.2 (ii). Let `(P₁, σ₁, ψ₁)` and
`(P₂, σ₂, ψ₂)` be Langlands triplets for the same choices `(T, i, ν, D)`, and let `Q₂` be
an actual parabolic opposite to `P₂` with the same Levi `M₂`. If some intertwining map
`i_{P₁}^G(σ₁ ⊗ ψ₁) → i_{Q₂}^G(σ₂ ⊗ ψ₂)` is nonzero, then there is a relative Weyl element
`w` such that `res_{f₂}(w ŷ₁) - res_{f₂}(ŷ₂)` lies in the nonnegative restricted root cone
of the second triplet. Here `ŷⱼ` is the full real parameter of `ψⱼ` on `T`. -/
theorem exists_weyl_sub_mem_nonnegCone_of_oppositeIntertwining :
    ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI := hG.smooth
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      [Mono i.hom.hom.left] (ν : cocharacterLattice T) (D : RelativeRootReflectionData i)
      (P₁ M₁ U₁ : GroupScheme (Spec (CommRingCat.of k)))
      (A₁ : CommGroupScheme (Spec (CommRingCat.of k)))
      (p₁ : P₁ ⟶ G) (l₁ : M₁ ⟶ P₁) (r₁ : U₁ ⟶ P₁) (a₁ : A₁.toGrp ⟶ M₁)
      (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
      (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
      (hmul₁ : IsIso (subgroupMultiplication l₁ r₁)) (ha₁ : IsSplitComponent a₁)
      (J₁ : Set (characterLattice T)) (f₁ : A₁ ⟶ T)
      (σ₁ : letI := leviPointTopology l₁ hl₁; SmoothRep.{0, u, v} ℂ (rationalPoints M₁))
      (ψ₁ : leviUnramifiedCharacters l₁ hl₁)
      (P₂ M₂ : GroupScheme (Spec (CommRingCat.of k)))
      (A₂ : CommGroupScheme (Spec (CommRingCat.of k)))
      (p₂ : P₂ ⟶ G) (l₂ : M₂ ⟶ P₂) (a₂ : A₂.toGrp ⟶ M₂)
      (hp₂ : IsParabolicSubgroup p₂) (hl₂ : IsRationalLeviSubgroup l₂)
      (ha₂ : IsSplitComponent a₂)
      (J₂ : Set (characterLattice T)) (f₂ : A₂ ⟶ T)
      (σ₂ : letI := leviPointTopology l₂ hl₂; SmoothRep.{0, u, v} ℂ (rationalPoints M₂))
      (ψ₂ : leviUnramifiedCharacters l₂ hl₂)
      (Q₂ V₂ : GroupScheme (Spec (CommRingCat.of k)))
      (q₂ : Q₂ ⟶ G) (lQ₂ : M₂ ⟶ Q₂) (rQ₂ : V₂ ⟶ Q₂)
      (hq₂ : IsParabolicSubgroup q₂) (hlQ₂ : IsRationalLeviSubgroup lQ₂)
      (hrQ₂ : LeviSubgroup.IsGeometricUnipotentRadical rQ₂)
      (hmulQ₂ : IsIso (subgroupMultiplication lQ₂ rQ₂)),
      lQ₂ ≫ q₂ = l₂ ≫ p₂ →
      pointImage p₂ ⊓ pointImage q₂ = pointImage (l₂ ≫ p₂) →
      ∀ (hT₁ : IsLanglandsTriplet i ν D p₁ l₁ a₁ hp₁ hl₁ ha₁ J₁ f₁ σ₁ ψ₁)
        (hT₂ : IsLanglandsTriplet i ν D p₂ l₂ a₂ hp₂ hl₂ ha₂ J₂ f₂ σ₂ ψ₂),
        letI : TopologicalSpace (rationalPoints M₁) := leviPointTopology l₁ hl₁
        haveI : NonarchimedeanGroup (rationalPoints M₁) :=
          leviPoints_nonarchimedeanGroup p₁ l₁ hp₁ hl₁
        letI : TopologicalSpace (rationalPoints M₂) := leviPointTopology l₂ hl₂
        haveI : NonarchimedeanGroup (rationalPoints M₂) :=
          leviPoints_nonarchimedeanGroup p₂ l₂ hp₂ hl₂
        let τ₁ := σ₁.twist ψ₁.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ₁)
        let τ₂ := σ₂.twist ψ₂.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ₂)
        ∀ t : ((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj τ₁).representation.IntertwiningMap
            ((leviInductionFunctor q₂ lQ₂ rQ₂ hq₂ hrQ₂ hlQ₂ hmulQ₂).obj τ₂).representation,
          t ≠ 0 →
          ∃ w : relativeWeylGroup i,
            rationalCharacterRestrictReal (CommGroupScheme.groupHom f₂)
                (relativeWeylFullRealAction i w
                  (leviUnramifiedFullRealPart
                    (⟨⟨T, i, ν, J₁, f₁⟩, hT₁.1⟩ : ParabolicRootPresentation p₁ l₁ a₁) ψ₁)) -
              rationalCharacterRestrictReal (CommGroupScheme.groupHom f₂)
                (leviUnramifiedFullRealPart
                  (⟨⟨T, i, ν, J₂, f₂⟩, hT₂.1⟩ : ParabolicRootPresentation p₂ l₂ a₂) ψ₂) ∈
              (⟨⟨T, i, ν, J₂, f₂⟩, hT₂.1⟩ : ParabolicRootPresentation p₂ l₂ a₂).nonnegCone := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ T i _ ν D P₁ M₁ U₁ A₁ p₁ l₁ r₁ a₁ hp₁ hl₁ hr₁ hmul₁ ha₁ J₁ f₁ σ₁ ψ₁
    P₂ M₂ A₂ p₂ l₂ a₂ hp₂ hl₂ ha₂ J₂ f₂ σ₂ ψ₂
    Q₂ V₂ q₂ lQ₂ rQ₂ hq₂ hlQ₂ hrQ₂ hmulQ₂ hLevi₂ hOpp₂ hT₁ hT₂
  have := hl₁.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M₁) := leviPointTopology l₁ hl₁
  have : LocallyCompactSpace (rationalPoints M₁) := leviPoints_locallyCompactSpace p₁ l₁ hp₁ hl₁
  have : NonarchimedeanGroup (rationalPoints M₁) := leviPoints_nonarchimedeanGroup p₁ l₁ hp₁ hl₁
  have := hl₂.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M₂) := leviPointTopology l₂ hl₂
  have : LocallyCompactSpace (rationalPoints M₂) := leviPoints_locallyCompactSpace p₂ l₂ hp₂ hl₂
  have : NonarchimedeanGroup (rationalPoints M₂) := leviPoints_nonarchimedeanGroup p₂ l₂ hp₂ hl₂
  let : TopologicalSpace (rationalPoints A₂.toGrp) :=
    RationalPointFamily.splitComponentPointTopology ha₂
  intro τ₁ τ₂ t ht
  let pres₁ : ParabolicRootPresentation p₁ l₁ a₁ := ⟨⟨T, i, ν, J₁, f₁⟩, hT₁.1⟩
  let pres₂ : ParabolicRootPresentation p₂ l₂ a₂ := ⟨⟨T, i, ν, J₂, f₂⟩, hT₂.1⟩
  obtain ⟨presQ⟩ := parabolicRootPresentationExistence k G hG Q₂ M₂ A₂ q₂ lQ₂ a₂ hq₂ hlQ₂ ha₂
  have hpoints : (SubgroupFunctor.range p₂).carrier (Over.mk (𝟙 _)) ⊓
      (SubgroupFunctor.range q₂).carrier (Over.mk (𝟙 _)) =
      (SubgroupFunctor.range (l₂ ≫ p₂)).carrier (Over.mk (𝟙 _)) := by
    simpa only [pointImage_eq_range_carrier] using hOpp₂
  have hirr₁ : τ₁.IsIrreducible :=
    (SmoothRep.isIrreducible_twist_iff ψ₁.val.toMonoidHom
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ₁) σ₁).mpr hT₁.2.1
  have hadm₁ : τ₁.IsAdmissible :=
    (SmoothRep.isAdmissible_twist_iff ψ₁.val.toMonoidHom
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ₁) σ₁).mpr hT₁.2.2.1.isAdmissible
  -- Frobenius reciprocity for `Q₂`.
  obtain ⟨e, -⟩ := leviFrobeniusReciprocity.{u, v, max u v} k G hG Q₂ M₂ V₂ q₂ lQ₂ rQ₂
    hq₂ hlQ₂ hrQ₂ hmulQ₂ ((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj τ₁) τ₂
  have hΦ : e t ≠ 0 := by
    intro h
    apply ht
    apply e.injective
    rw [h, map_zero]
  -- The scalar split-component character of `τ₂`.
  let c := normalizedTemperedTwistSplitCharacter hl₂.isConnectedReductive a₂ ha₂ σ₂
    hT₂.2.2.1 hT₂.2.1 ψ₂.val.toMonoidHom
  have hscalar : ∀ b, (τ₂.representation.comp (rationalPoints.map a₂)) b =
      (c.val b : ℂ) • (1 : Module.End ℂ τ₂) := by
    intro b
    apply LinearMap.ext
    intro x
    exact c.property.1 b x
  have : Module.Finite ℂ (PQFiniteActionRegularity.actionQuotient
      (τ₂.representation.comp (rationalPoints.map a₂))) :=
    CentralActionQuotient.finite_actionQuotient_of_scalar _ (fun b => (c.val b : ℂ)) hscalar
  -- The geometric lemma for `P₁` and `Q₂`.
  obtain ⟨m, c₀, z, -, E, perm, s, hs⟩ :=
    representedGeometricLemma.{u, v} k G hG P₁ M₁ U₁ Q₂ M₂ V₂ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
      q₂ lQ₂ rQ₂ hq₂ hlQ₂ hrQ₂ hmulQ₂
  let φA := rationalPoints.map a₂
  let Iτ := groupAlgebraKernel τ₂.representation φA
  have hnot : Iτ ⊔ ⨅ j, groupAlgebraKernel
      (((fun j => (E (perm j)).pieceFunctor) j).obj τ₁).ρ φA ≠ ⊤ := by
    intro htop
    rw [← PQFilteredKernels.sup_kernel_eq_top_iff_pieceKernels s τ₁ φA
      (fun j => (E (perm j)).pieceFunctor) (fun j => (hs j).some)] at htop
    apply hΦ
    apply IntertwiningMap.eq_zero_of_groupAlgebraKernel_sup_eq_top (e t) φA
    rw [sup_comm]
    exact htop
  obtain ⟨j, hj⟩ : ∃ j, Iτ ⊔ groupAlgebraKernel ((E (perm j)).pieceFunctor.obj τ₁).ρ φA ≠ ⊤ := by
    by_contra hall
    push Not at hall
    apply hnot
    have := Ideal.sup_iInf_eq_top (s := Finset.univ) (fun j _ => hall j)
    simpa only [Finset.mem_univ, iInf_true] using this
  set E₀ := E (perm j)
  obtain ⟨A', a', g, ha', hg⟩ := E₀.exists_isSplitComponent_factor ha₂
  have hb : (g ≫ a') ≫ E₀.lQ' ≫ E₀.q' = a₂ := by
    simpa only [Category.assoc] using hg
  let := leviPointTopology E₀.l' E₀.hl'
  have hJ := arbitraryParabolicJacquetAdmissibility k M₁ hl₁.isConnectedReductive
    E₀.P' E₀.M' E₀.N' E₀.p' E₀.l' E₀.r' E₀.hp' E₀.hl' E₀.hr' E₀.hmul' τ₁ hadm₁
  have hJ' : ((leviJacquetFunctor E₀.p' E₀.l' E₀.r' E₀.hp' E₀.hr' E₀.hl' E₀.hmul').obj
      τ₁).IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv
      ((jacquetFunctor E₀.p' E₀.l' E₀.r' E₀.hp' E₀.hr' E₀.hl' E₀.hmul').obj τ₁).representation
      (leviPointsEquiv E₀.p' E₀.l' E₀.hp' E₀.hl') hJ
  have hfg := leviJacquetFiniteType.{u, v} k M₁ hl₁.isConnectedReductive E₀.P' E₀.M' E₀.N'
    E₀.p' E₀.l' E₀.r' E₀.hp' E₀.hl' E₀.hr' E₀.hmul' τ₁
    (moduleFinite_asModule_of_isIrreducible τ₁.representation hirr₁)
  have : Module.Finite ℂ (PQFiniteActionRegularity.actionQuotient
      ((E₀.pieceFunctor.obj τ₁).ρ.comp φA)) :=
    E₀.finite_actionQuotient_piece ha₂ (g ≫ a') hb τ₁ hJ' hfg
  -- A common generalized character of the piece and of `τ₂`.
  have hdisj := (PQFiniteActionRegularity.sup_kernels_eq_top_iff
    ((E₀.pieceFunctor.obj τ₁).ρ.comp φA) (τ₂.representation.comp φA)).not.mp (by
      rw [sup_comm]
      exact hj)
  obtain ⟨χ, hχE, hχτ⟩ := Set.not_disjoint_iff.mp hdisj
  have hχc : χ = c.val :=
    CentralActionQuotient.eq_of_isGeneralizedEigencharacter_of_scalar _ c.val hscalar χ hχτ
  have hreal : Plancherel.SplitTorus.normalizedRealPart ha₂.isCentralSplitTorus.1.1 χ =
      leviUnramifiedRealPart l₂ hl₂ a₂ ha₂ ψ₂ := by
    rw [hχc]
    exact c.property.2
  -- The cone estimate for the piece.
  have hxQ := E₀.normalizedRealPart_sub_unramifiedPieceRealPart_mem_nonnegCone
      ha₂ ha' (Additive.ofMul g) hg presQ
      (relativeRootNegation k G hG presQ.data.T presQ.data.i presQ.isCompatible.maximalSplit)
      σ₁ ψ₁ hT₁.2.2.1 hJ' χ hχE
  have hxP := pres₂.neg_mem_nonnegCone_of_opposite presQ hG hLevi₂ hpoints hxQ
  -- The Weyl parameter of the piece.
  have hiL : pres₂.leviTorusHom ≫ lQ₂ ≫ q₂ = pres₁.data.i := by
    rw [hLevi₂]
    exact pres₂.leviTorusHom_comp
  obtain ⟨w, hw⟩ := E₀.exists_normalizedRealPart_piece_eq_weyl_crossLevi pres₁
    pres₂.leviTorusHom hiL ha₂ f₂ pres₂.factor_comp_leviTorusHom (g ≫ a') hb ψ₁
  refine ⟨w, ?_⟩
  have hU : E₀.unramifiedPieceRealPart ha₂ a' (Additive.ofMul g) ψ₁ =
      rationalCharacterRestrictReal (CommGroupScheme.groupHom f₂)
        (relativeWeylFullRealAction i w (leviUnramifiedFullRealPart pres₁ ψ₁)) := by
    rw [← hw]
    simp only [GeometricLemmaIntersectionDatum.unramifiedPieceRealPart, Category.assoc]
    rfl
  have heq : rationalCharacterRestrictReal (CommGroupScheme.groupHom f₂)
        (relativeWeylFullRealAction i w (leviUnramifiedFullRealPart pres₁ ψ₁)) -
      rationalCharacterRestrictReal (CommGroupScheme.groupHom f₂)
        (leviUnramifiedFullRealPart pres₂ ψ₂) =
      -(Plancherel.SplitTorus.normalizedRealPart ha₂.isCentralSplitTorus.1.1 χ -
        E₀.unramifiedPieceRealPart ha₂ a' (Additive.ofMul g) ψ₁) := by
    rw [hU, hreal, restrict_leviUnramifiedFullRealPart pres₂ ψ₂]
    abel
  rw [heq]
  exact hxP

end Langlands.Aubert.General.RepresentedParabolic
