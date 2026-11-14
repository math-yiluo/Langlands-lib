import Langlands.BruhatTits.IntegralModels.IntegralOppositeNecessity
import Langlands.BruhatTits.IntegralModels.IntegralTorusGenericRoots
import Langlands.BruhatTits.IntegralModels.CommonTorusQuotientMaximality
import Langlands.BruhatTits.IntegralModels.ReductiveQuotientExistence
import Langlands.GroupScheme.IntegralModel.KernelCentralizerOppositeSufficiency
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # Integral opposite factors and the actual radical preimage -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

/-- Opposite factors of a nonidentity integral root point are integral
exactly when its actual quotient reduction is nonidentity. -/
theorem integralOppositeFactors : IntegralOppositeFactorsStatement.{u} := by
  intro F _ _ _ _ G hG S i hi D T Q hT hQ
  let : HenselianLocalRing ↥𝒪[F] := henselianLocalRing_integer
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : Smooth D.neutral.group.X.hom := D.neutral_smooth
  have hiK : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).obj T.torus)
      (D.neutral.genericHom T.inclusion) := T.genericHom_isMaximalSplitTorus hi
  let : IsClosedImmersion (D.neutral.genericHom T.inclusion).hom.hom.left := hiK.1.2
  let : Mono (D.neutral.genericHom T.inclusion).hom.hom.left := inferInstance
  have hiRaw : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).obj T.torus)
      ((baseChange (Spec.algebraMap ↥𝒪[F] F)).map T.inclusion) :=
    (IsMaximalSplitTorus.comp_iso_iff _ D.neutral.genericIso).mp hiK
  have hiRes : IsMaximalSplitTorus T.specialFibreInclusion := by
    have hr := isMaximalSplitTorus_residue_of_generic
      (IsLocalRing.residue_surjective : Function.Surjective
        (algebraMap ↥𝒪[F] (IsLocalRing.ResidueField ↥𝒪[F])))
      D.neutral.group (hG.of_iso D.neutral.genericIso) T.torus hT.1 T.inclusion hT.2 hiRaw
    simpa only [IntegralTorusData.specialFibreInclusion, IntegralModel.residueBaseMap,
      IntegralTorusData.specialFibre, IntegralModel.specialFibre, Spec.algebraMap,
      IsLocalRing.ResidueField.algebraMap_eq] using hr
  have hiQ : IsMaximalSplitTorus (T.specialFibreInclusion ≫ Q.projection) := by
    let : Smooth Q.radical.X.hom := hQ.1.smooth
    let : ConnectedSpace Q.radical.X.left := hQ.1.connectedSpace
    let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
    let : IsAffineHom D.neutral.specialFibre.X.hom := by
      change IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
        (IntegralModel.residueBaseMap ↥𝒪[F]))
      infer_instance
    let : LocallyOfFiniteType D.neutral.specialFibre.X.hom := by
      change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
        (IntegralModel.residueBaseMap ↥𝒪[F]))
      infer_instance
    exact (IsMaximalSplitTorus.comp_iff_of_perfect_field_unipotent_kernel
      Q.radicalInclusion hQ.1.isClosedSubgroup hQ.1.isUnipotent
      Q.projection hQ.2.1 T.specialFibreInclusion).mpr hiRes
  intro a ha g hg hg1 hgR g' hg' g'' hg'' hn
  constructor
  · intro hp
    exact T.not_mem_positivePoints_of_integral_oppositeFactors hT.1 Q hQ hG hi
      ha.1 hg hg1 hg' hg'' hn hp.1 hp.2
  · intro hnon
    obtain ⟨x, hx⟩ := (D.neutral.mem_integralPoints g).mp hgR
    have hqx : rationalPoints.map Q.projection (D.neutral.reduction x) ≠ 1 := by
      intro hz
      apply hnon
      apply (Q.mem_positivePoints g).mpr
      refine ⟨x, ?_, hx⟩
      have hr := (mem_range_kernelι_iff Q.projection (D.neutral.reduction x)).mpr hz
      rw [hQ.2.1.2.2.2] at hr
      exact hr
    let χ := (T.genericCharacterEquiv hT.1).symm a
    have hχa : T.genericCharacter χ = a :=
      (T.genericCharacterEquiv hT.1).apply_symm_apply a
    have haK : characterLattice.baseChange (Spec.algebraMap ↥𝒪[F] F) T.torus χ ∈
        relativeRoots (D.neutral.genericHom T.inclusion) :=
      (T.generic_mem_relativeRoots_iff χ).mpr (by rwa [hχa])
    have hxroot : D.neutral.integralPointMap x ∈
        (RelativeRoot.subgroup (D.neutral.genericHom T.inclusion)
          (characterLattice.baseChange (Spec.algebraMap ↥𝒪[F] F) T.torus χ)).carrier
            (Over.mk (𝟙 _)) := by
      rw [T.generic_subgroup_eq χ, hχa, hx]
      exact hg
    have hpK : RelativeRoot.IsOppositeFactorPair (D.neutral.genericHom T.inclusion)
        (characterLattice.baseChange (Spec.algebraMap ↥𝒪[F] F) T.torus χ)
        (D.neutral.integralPointMap x) (g', g'') :=
      (T.generic_isOppositeFactorPair_iff χ _ _).mp (by
        rw [hχa, hx]
        exact ⟨hg', hg'', hn⟩)
    obtain ⟨ν, -, hpos⟩ := RelativeRoot.exists_genericCocharacter_pairing_pos i hi.1.1 ha.1
    obtain ⟨νR, -, hνRpair⟩ := T.exists_integralCocharacter_compatible hT.1 ν
    have hposR : 0 < latticePairing T.torus χ νR := by
      have hp := hνRpair a
      rw [← hχa, T.characterSpecialization_genericCharacter hT.1 χ] at hp
      rw [hχa] at hp
      change latticePairing T.specialFibre
        (characterLattice.baseChange (IntegralModel.residueBaseMap ↥𝒪[F]) T.torus χ)
        (cocharacterLattice.baseChange (IntegralModel.residueBaseMap ↥𝒪[F]) T.torus νR) =
          latticePairing S a ν at hp
      rw [latticePairing_baseChange] at hp
      rwa [hp]
    exact D.neutral.integral_oppositeFactors_of_residueQuotient
      T.inclusion hT.1 χ νR hposR Q.projection hQ.2.2
      (Q.projection_smooth hQ) (SpecialFibreQuotientData.hasSmoothConnectedUnipotentKernel hQ)
      hiQ (relativeRootSystem F G hG _ _ hiK) haK x hxroot (by rwa [hx]) hqx
      (g', g'') hpK

end Langlands.BruhatTits.IntegralModels
