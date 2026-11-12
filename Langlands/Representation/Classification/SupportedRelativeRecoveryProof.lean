import Langlands.Representation.Classification.RelativeRecoveryStatement
import Langlands.Representation.Classification.RelativeRegularComparisonProof
import Langlands.Representation.Exponents.ActualQuotientRealBlock
import Langlands.Representation.CuspidalSupport.NormalRestrictionCovariance

/-! Supported recovery from actual finite-series counts and quotient maps. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity RelativeRegularComparison

universe uG uA uB uC uT uF uV uM uW uX uZ

namespace SupportedRelativeRecoveryProof

/-- Actual series descend through a surjection, and the resulting count is bounded. -/
private theorem count_of_surjective
    {G : Type uG} [Monoid G] (A : Rep.{uA} ℂ G) (C : Rep.{uC} ℂ G)
    (τ : Rep.{uT} ℂ G) (q : A.ρ.IntertwiningMap C.ρ)
    (hq : Function.Surjective q) (m : ℕ)
    (hm : HasJordanHolderMultiplicity A τ m) :
    ∃ c : ℕ, HasJordanHolderMultiplicity C τ c ∧ c ≤ m := by
  let K := Rep.of q.ker.toRepresentation
  let i : K.ρ.IntertwiningMap A.ρ :=
    { toLinearMap := q.ker.toSubmodule.subtype
      isIntertwining' _ := rfl }
  have hex : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap :=
    Submodule.range_subtype _
  obtain ⟨a, c, _, hc, hac⟩ := jordanHolderShortExactDecomposition ℂ G
    K A C τ i q (Submodule.injective_subtype _) hq hex m hm
  exact ⟨c, hc, by omega⟩

private def equalSubrepresentationEquiv {G : Type uG} [Group G]
    (C : Rep.{uC} ℂ G) {U V : Subrepresentation C.ρ} (h : U = V) :
    U.toRepresentation.Equiv V.toRepresentation := by
  cases h
  exact Representation.Equiv.refl _

/-- Inequivalent simple subrepresentations give an injection of their product. -/
private theorem product_embedding
    {G : Type uG} [Group G]
    (A : Rep.{uA} ℂ G) (B : Rep.{uB} ℂ G) (C : Rep.{uC} ℂ G)
    (hA : Representation.IsIrreducible A.ρ)
    (hB : Representation.IsIrreducible B.ρ)
    (hne : ¬ Nonempty (A.ρ.Equiv B.ρ))
    (i : A.ρ.IntertwiningMap C.ρ) (j : B.ρ.IntertwiningMap C.ρ)
    (hi : Function.Injective i) (hj : Function.Injective j) :
    ∃ f : (A.ρ.prod B.ρ).IntertwiningMap C.ρ, Function.Injective f := by
  obtain ⟨ei⟩ := MultiplicityAdditivityProof.source_equiv_range i hi
  obtain ⟨ej⟩ := MultiplicityAdditivityProof.source_equiv_range j hj
  have hai : IsAtom i.range := NormalRestrictionOrbit.isAtom_of_isIrreducible
    i.range (LengthTwo.isIrreducible_of_equiv ei hA)
  have haj : IsAtom j.range := NormalRestrictionOrbit.isAtom_of_isIrreducible
    j.range (LengthTwo.isIrreducible_of_equiv ej hB)
  have hij : i.range ≠ j.range := by
    intro he
    exact hne ⟨(ei.trans (equalSubrepresentationEquiv C he)).trans ej.symm⟩
  have hdis : Disjoint i.toLinearMap.range j.toLinearMap.range :=
    disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule
      (disjoint_iff.mp (hai.disjoint_of_ne haj hij)))
  let f : (A.ρ.prod B.ρ).IntertwiningMap C.ρ :=
    i.comp (Representation.IntertwiningMap.fst ℂ _ _) +
      j.comp (Representation.IntertwiningMap.snd ℂ _ _)
  refine ⟨f, (injective_iff_map_eq_zero f).mpr ?_⟩
  rintro ⟨a, b⟩ hab
  change i a + j b = 0 at hab
  obtain ⟨ha, hb⟩ := Submodule.disjoint_iff_add_eq_zero.mp hdis
    ⟨a, rfl⟩ ⟨b, rfl⟩ hab
  exact Prod.ext ((map_eq_zero_iff i hi).mp ha) ((map_eq_zero_iff j hj).mp hb)

end SupportedRelativeRecoveryProof

set_option maxHeartbeats 1000000 in
/-- A supported tempered coarse input is recovered from a common irreducible
outer quotient, even when the competing supported quotient is not tempered. -/
theorem glSupportedRelativeRecovery :
    GLSupportedRelativeRecoveryStatement.{uF,uV,uM,uW,uX,uZ} := by
  intro p _ F T
  let := T.topology
  dsimp only
  intro n hn B Q R S h ω hωirr hωcusp hωunit v₀ hv₀
    σ hσirr hσsq hqσ π hπirr hπtemp hqmid hqfine
    θ hθirr hθadm hqθ t ht J hJirr hqπJ hqθJ
  by_contra hne
  obtain ⟨hωBirr, hωBcusp⟩ :=
    RelativeRegularComparisonProof.transport_irreducible_cuspidal T h ω hωirr hωcusp
  let τ := fineTwist T B S (h ▸ ω) (h ▸ v₀) t
  let πt := Rep.of (T.leviRealPowerTwist B t π.ρ)
  let θt := Rep.of (T.leviRealPowerTwist B t θ.ρ)
  let I := CuspidalJacquetMultiplicity.induced T B πt
  let O := CuspidalJacquetMultiplicity.oppositeJacquet T B J
  let C := Rep.of (T.normalizedComposedOppositeJacquet B S J.ρ)
  obtain ⟨m, hmpos, hmπ, hmI, _⟩ := glRelativeRegularComparison.{uF,uV,uM,uW}
    p F T n hn B Q R S h ω hωirr hωcusp hωunit v₀ hv₀
      σ hσirr hσsq hqσ π hπirr hπtemp hqmid hqfine t ht
  obtain ⟨_, _, Mθ, hMθ⟩ :=
    glSupportedAmbientJacquetLengthReduction.{uF,uV,uX} p F T n hn
      (CuspidalSupport.cuspidalInductionLength.{uF,uV} F T n)
      B S (h ▸ ω) hωBirr hωBcusp (h ▸ v₀) θ hθadm hqθ t
  obtain ⟨mθ, hmθpos, hmθ, _⟩ :=
    glSupportedRelativeJacquetPositiveBound.{uF,uV,uX} p F T n hn B S (h ▸ ω)
      hωBirr hωBcusp (h ▸ v₀) θ hθirr hθadm hqθ t Mθ hMθ
  obtain ⟨qπ, hqπ⟩ := hqπJ
  obtain ⟨qθ, hqθ⟩ := hqθJ
  have hπtadm : IsAdmissible πt.ρ :=
    (T.isAdmissible_leviRealPowerTwist_iff B t π.ρ).mpr hπtemp.isAdmissible
  have hθtadm : IsAdmissible θt.ρ :=
    (T.isAdmissible_leviRealPowerTwist_iff B t θ.ρ).mpr hθadm
  have hπtirr : Representation.IsIrreducible πt.ρ :=
    (T.isIrreducible_leviRealPowerTwist_iff B t π.ρ).mpr hπirr
  have hθtirr : Representation.IsIrreducible θt.ρ :=
    (T.isIrreducible_leviRealPowerTwist_iff B t θ.ρ).mpr hθirr
  have hJadm := ((relativeCosocleAdmissibility p F T n B π).2.2
    hπtemp.isAdmissible t).2.2 J qπ hqπ
  have hOadm : IsAdmissible O.ρ :=
    Parabolic.isAdmissible_standardOppositeJacquet F T B J.V J.ρ hJadm
  let := hJirr
  have hJnt : Nontrivial J.V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) J.ρ.asModule
  obtain ⟨i, hi₀⟩ := ActualQuotientRealBlock.nonzeroAdjunctionMap
    T hn B πt J hJnt qπ hqπ hπtadm hJadm
  obtain ⟨j, hj₀⟩ := ActualQuotientRealBlock.nonzeroAdjunctionMap
    T hn B θt J hJnt qθ hqθ hθtadm hJadm
  have hi : Function.Injective i := by
    let := hπtirr
    exact (Representation.IsIrreducible.injective_or_eq_zero i).resolve_right hi₀
  have hj : Function.Injective j := by
    let := hθtirr
    exact (Representation.IsIrreducible.injective_or_eq_zero j).resolve_right hj₀
  have hnet : ¬ Nonempty (πt.ρ.Equiv θt.ρ) := by
    rintro ⟨e⟩
    exact hne ⟨(untwistIntertwining (T.leviRealPowerCharacter B t)
      e.toIntertwiningMap).ofBijective e.bijective⟩
  obtain ⟨k, hk⟩ := SupportedRelativeRecoveryProof.product_embedding
    πt θt O hπtirr hθtirr hnet i j hi hj
  have hJk := T.normalizedRefinedOppositeJacquetMap_injective B S k hOadm.1 hk
  obtain ⟨Eprod, _⟩ := T.normalizedRefinedOppositeJacquet_binary_product B S πt.ρ θt.ρ
  obtain ⟨Etrans, _⟩ := Parabolic.normalizedOppositeRefinementTransitivity
    p F T n B S J
  let f : ((innerJacquet T B S πt).ρ.prod
      (innerJacquet T B S θt).ρ).IntertwiningMap C.ρ :=
    Etrans.toIntertwiningMap.comp
      ((T.normalizedRefinedOppositeJacquetMap B S k).comp Eprod.symm.toIntertwiningMap)
  have hf : Function.Injective f :=
    Etrans.injective.comp (hJk.comp Eprod.symm.injective)
  let q : (ambientJacquet T B S πt).ρ.IntertwiningMap C.ρ :=
    T.normalizedComposedOppositeJacquetMap B S qπ
  have hq : Function.Surjective q :=
    coinvariants_map_surjective (Jacquet.restrictMap qπ
      (Parabolic.composedOppositeUnipotent F.Carrier B S)) hqπ
  obtain ⟨mJ, hmJ, hmJle⟩ := SupportedRelativeRecoveryProof.count_of_surjective
    (ambientJacquet T B S πt) C τ q hq m hmI
  have hprod := jordanHolderProductAdditivity ℂ (refinedLevi F.Carrier B S)
    (innerJacquet T B S πt) (innerJacquet T B S θt) τ m mθ hmπ hmθ
  have hle := jordanHolderInjectiveMonotonicity ℂ (refinedLevi F.Carrier B S)
    (Rep.of ((innerJacquet T B S πt).ρ.prod (innerJacquet T B S θt).ρ))
    C τ f hf (m + mθ) mJ hprod hmJ
  omega

end Langlands
