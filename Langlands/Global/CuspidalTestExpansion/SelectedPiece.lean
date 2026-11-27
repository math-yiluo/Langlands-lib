import Langlands.Global.CuspidalTestExpansion.PieceProperties
import Langlands.Global.CuspidalTestExpansion.StabilizerTransitivity
import Langlands.Global.CuspidalTestExpansion.FullPiece

/-! # The selected Bruhat piece is the constant term of the selected intertwining integral -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions
  RepresentationGrowth EisensteinConstantTerm

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G fam.i fam.ν

set_option maxHeartbeats 4000000 in
/-- Assume `GeometricLemmaUnfoldingStatement`, `J ≤ Q`, `0 < N`, and let `φ` be continuous and
left invariant under `U_I(𝔸) M_I(F)`, with a summable nonnegative majorant
`‖φ_λ(γ_c g)‖ ≤ b c · H(g)^d` (`d ≥ 0`) of the Eisenstein terms over `P_I(F) \ G(F)`. Then the
constant term along `P_J` of the selected intertwining integral `M(n)φ` (target radical `U_Q`)
is the intertwining integral of the Bruhat piece of `n` for the pair `(I, J)`, whose target is
all of `P_J`. -/
theorem selectedPiece_constantTerm (hGLU : GeometricLemmaUnfoldingStatement.{u})
    {I Q J I₁ J₁ I₂ Q₂ : Idx} {n n' : normalizerPoints fam.i}
    [IsClosedImmersion (fam.p I).hom.hom.left]
    (pc : StandardBruhatPiece fam I J I₁ J₁ n') (hn : n = n') (hJ₁ : J = J₁)
    (pcQ : StandardBruhatPiece fam I Q I₂ Q₂ n) (hI₂ : I = I₂) (hQ₂ : Q = Q₂) (hJQ : J ≤ Q)
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (fam.p I) K)
    (hK₁ : IsIwasawaCompact (pc.source.inclusion ≫ fam.p I) K)
    (hK₂ : IsIwasawaCompact (pcQ.source.inclusion ≫ fam.p I) K)
    {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    {φ : AdelicGroupPoints F G → ℂ} (hφc : Continuous φ)
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (fam.p I) (fam.iU I) (fam.l I)) φ)
    (lam : ComplexCharacterParameter F (fam.P I))
    (b : ParabolicRationalCosets F (fam.p I) → ℝ) (d : ℝ) (hb : Summable b)
    (hb0 : ∀ x, 0 ≤ b x) (hd : 0 ≤ d)
    (hbound : ∀ g x, ‖hK.eisensteinTerm φ lam g x‖ ≤ b x * adelicHeight F G rho g ^ d)
    (y : AdelicGroupPoints F G) :
    fam.constantTerm J (hK.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q) n.val φ lam) y =
      hK₁.intertwiningIntegral (fam.iU I₁) (fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J) n'.val
        (subgroupConstantTerm F (fam.iU I₁ ≫ pc.source.inclusion ≫ fam.p I) φ)
        (parameterRestrict pc.source.inclusion lam) y := by
  subst hn hJ₁ hI₂ hQ₂
  set Φ := hK.parameterTwist φ lam with hΦdef
  obtain ⟨hΦU, hΦP⟩ := fam.parameterTwist_isLeftInvariant hK hφ lam
  have hΦc : Continuous Φ := hK.continuous_parameterTwist hφc lam
  set wA := innerAdelicPoint F G n.val with hwA
  have hw : wA ∈ rationalSubgroup F G := ⟨_, (innerAdelicPoint_eq_rational F G n.val).symm⟩
  -- integrability of the stabilizer integrands
  have hint : ∀ X : Idx, ∀ z, Integrable
      (eisensteinStabilizerIntegrand (fam.p I) (fam.p X) (fam.iU X) wA Φ z)
      (stabilizerMeasure F (fam.p I) (fam.iU X ≫ fam.p X) wA) := by
    intro X
    have hVr := (fam.isUnipotentRadical X).1
    have : IsAffineHom (fam.U X).X.hom := IsClosedSubgroup.isAffineHom hVr.isClosedSubgroup
    have : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G
        (SubgroupFunctor.range (fam.iU X ≫ fam.p X))) :=
      AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F (fam.iU X ≫ fam.p X)
        hVr.smooth hVr.connectedSpace hVr.isUnipotent
    obtain ⟨B, hBint, hB0, hBbd⟩ := eisensteinUnfoldingGlobalMajorant hK (fam.iU X ≫ fam.p X)
      n.val rho (iU := fam.iU I) (l := fam.l I) hN hVr.smooth hVr.connectedSpace hVr.isUnipotent
      (fam.isCompatible I).levi (fam.isUnipotentRadical I) φ hφ lam b d hb hb0 hd hbound
    exact (eisensteinStabilizerContinuity (fam.p I) (fam.p X) (fam.iU X) wA rho hN Φ hΦc hΦP B d
      hBint hB0 hd (fun v g => hBbd v g)).1
  -- the selected intertwining integral is the stabilizer integral along `U_Q`
  have hPPQ := fam.pieceIntegral_properties hGLU pcQ hK hK₂ rho hN hφc hφ lam b d hb hb0 hd
    hbound
  have hCφ : subgroupConstantTerm F (fam.iU I ≫ pcQ.source.inclusion ≫ fam.p I) φ = φ := by
    rw [subgroupConstantTerm_congr_hom (by rw [pcQ.source.inclusion_comp]) φ]
    funext g
    have : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G
        (SubgroupFunctor.range (fam.iU I ≫ fam.p I))) := fam.compactSpace_radicalRationalQuotient I
    have hprob := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure
      F G (SubgroupFunctor.range (fam.iU I ≫ fam.p I))
    unfold subgroupConstantTerm
    have hc : ∀ x : AdelicSubgroupPoints.RationalQuotient F G
        (SubgroupFunctor.range (fam.iU I ≫ fam.p I)),
        φ (((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G
          (SubgroupFunctor.range (fam.iU I ≫ fam.p I))) : AdelicGroupPoints F G) * g) = φ g :=
      fun x => hφ _ (Subgroup.mem_sup_left (Quotient.out x).2) g
    simp only [hc, integral_const, Measure.real_def, measure_univ, ENNReal.toReal_one, one_smul]
  have hIntQ : ∀ z, hK.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q) n.val φ lam z =
      stabilizerIntegral (fam.p I) (fam.p Q) (fam.iU Q) wA Φ z := by
    intro z
    have h1 : hK₂.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ pcQ.target.inclusion ≫ fam.p Q) n.val
        (subgroupConstantTerm F (fam.iU I ≫ pcQ.source.inclusion ≫ fam.p I) φ)
        (parameterRestrict pcQ.source.inclusion lam) z =
        stabilizerIntegral (fam.p I) (fam.p Q) (fam.iU Q) wA Φ z := hPPQ.2.1 z
    rw [hCφ] at h1
    rw [← h1]
    exact (hK₂.intertwiningIntegral_eq_of_range_eq_of_twist hK (fam.iU I) (fam.iU I) _ _
      (by rw [pcQ.source.inclusion_comp]) (by rw [pcQ.target.inclusion_comp]) n.val φ _ lam
      (hK.parameterTwist_restrict_of_comp_eq hK₂ pcQ.source.inclusion rfl φ lam).symm z).symm
  -- the piece is the stabilizer integral along `U_J`
  have hPP := fam.pieceIntegral_properties hGLU pc hK hK₁ rho hN hφc hφ lam b d hb hb0 hd hbound
  have hPJ : hK₁.intertwiningIntegral (fam.iU I₁) (fam.iU J ≫ pc.target.inclusion ≫ fam.p J) n.val
      (subgroupConstantTerm F (fam.iU I₁ ≫ pc.source.inclusion ≫ fam.p I) φ)
      (parameterRestrict pc.source.inclusion lam) y =
      stabilizerIntegral (fam.p I) (fam.p J) (fam.iU J) wA Φ y := hPP.2.1 y
  -- `U_J(F) ⊆ (U_J(F) ∩ nP_I(F)n⁻¹) U_Q(F)` from the geometric lemma for `(I, Q)`
  have hNQ : (SubgroupFunctor.range (fam.iU Q)).IsNormal := (fam.isUnipotentRadical Q).1.isNormal
  have hNJ : (SubgroupFunctor.range (fam.iU J)).IsNormal := (fam.isUnipotentRadical J).1.isNormal
  have hle := fam.radical_le_of_le hJQ
  have hnorm := fam.radical_isNormalizedBy_of_le hJQ
  have hdec : ∀ δ ∈ AdelicSubgroupPoints.rationalSubgroup F G
      (SubgroupFunctor.range (fam.iU J ≫ fam.p J)),
      ∃ a ∈ stabilizerRationalSubgroup F (fam.p I) (fam.iU J ≫ fam.p J) wA,
        ∃ t : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (fam.iU Q ≫ fam.p Q)),
          t ∈ AdelicSubgroupPoints.rationalSubgroup F G
            (SubgroupFunctor.range (fam.iU Q ≫ fam.p Q)) ∧
          (δ : AdelicGroupPoints F G) = (a : AdelicGroupPoints F G) * (t : AdelicGroupPoints F G) := by
    intro δ hδ
    have hδr : (δ : AdelicGroupPoints F G) ∈ rationalImage F (fam.iU J ≫ fam.p J) :=
      (mem_rationalSubgroup_range_iff _ δ).mp hδ
    have hδQ : (δ : AdelicGroupPoints F G) ∈ rationalImage F (pcQ.target.inclusion ≫ fam.p Q) := by
      refine rationalImage_le_of_range_le (fam.iU J ≫ fam.p J) _ ?_ hδr
      rw [pcQ.target.inclusion_comp]
      exact (SubgroupFunctor.range_le_of_factor (fam.iU J) rfl).trans
        ((fam.le_iff_range_le J Q).mp hJQ)
    rw [pcQ.geometry.rationalImage_right] at hδQ
    obtain ⟨a, ha, v, hv, hav⟩ := exists_mul_of_mem_sup
      (A := rationalImage F (fam.p Q) ⊓
        (rationalImage F (fam.p I)).map (MulAut.conj wA).toMonoidHom)
      (V := rationalImage F (fam.iU Q ≫ fam.p Q))
      (fun a ha v hv => conj_mem_rationalImage (fam.p Q) (fam.iU Q) hNQ ha.1 hv) hδQ
    have hvJ : v ∈ rationalImage F (fam.iU J ≫ fam.p J) :=
      rationalImage_le_of_range_le _ _ hle hv
    have haJ : a ∈ rationalImage F (fam.iU J ≫ fam.p J) := by
      have : a = (δ : AdelicGroupPoints F G) * v⁻¹ := by rw [hav, mul_inv_cancel_right]
      rw [this]
      exact mul_mem hδr (inv_mem hvJ)
    let a' : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (fam.iU J ≫ fam.p J)) :=
      ⟨a, rationalImage_le_adelicPoints _ haJ⟩
    let t : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (fam.iU Q ≫ fam.p Q)) :=
      ⟨v, rationalImage_le_adelicPoints _ hv⟩
    refine ⟨a', ?_, t, (mem_rationalSubgroup_range_iff _ t).mpr hv, hav⟩
    rw [mem_stabilizerRationalSubgroup_iff]
    exact ⟨(mem_rationalSubgroup_range_iff _ a').mpr haJ, (mem_map_conj_iff _ _ _).mp ha.2⟩
  have := fam.compactSpace_radicalRationalQuotient Q
  have := fam.compactSpace_radicalRationalQuotient J
  rw [show hK.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q) n.val φ lam =
    stabilizerIntegral (fam.p I) (fam.p Q) (fam.iU Q) wA Φ from funext hIntQ, hPJ]
  exact subgroupConstantTerm_stabilizerIntegral_of_le (fam.p I) (fam.p Q) (fam.iU Q) (fam.p J)
    (fam.iU J) hNQ hNJ hle hnorm wA hw hdec rho hN hΦc hΦP b d hb hb0 hd hbound (hint Q) y
    (hint J y)

end Langlands.Global.StandardParabolicFamily
