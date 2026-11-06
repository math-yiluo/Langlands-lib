import Langlands.Representation.Exponents.TemperedGroupWeights
import Langlands.Representation.Exponents.ArbitraryParabolicUnitaryJacquetPart
import Langlands.GroupScheme.Rational.SplitComponentProof

/-! # The unitary Jacquet part at the identity parabolic -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance identityUnitaryAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {hG : IsConnectedReductive G} {π : SmoothRep.{0, u, v} ℂ (rationalPoints G)}
  (hπ : IsNormalizedExponentTempered hG π)
  (hp : IsParabolicSubgroup (𝟙 G)) (hl : IsRationalLeviSubgroup (𝟙 G))
  {U : GroupScheme (Spec (CommRingCat.of k))} (r : U ⟶ G)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication (𝟙 G) r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ G}
  (ha : IsSplitComponent a)

include hπ

/-- Every normalized Jacquet weight at the identity parabolic belongs to the
unitary part of a tempered representation. -/
theorem IsNormalizedExponentTempered.normalizedJacquetWeightSpace_identity_le_unitary
    (χ : rationalPoints A.toGrp →* ℂˣ) :
    normalizedJacquetWeightSpace (𝟙 G) (𝟙 G) r hp hl hr hmul ha π χ ≤
      unitaryJacquetPart (𝟙 G) (𝟙 G) r hp hl hr hmul ha π := by
  by_cases hχ : IsNormalizedJacquetExponent (𝟙 G) (𝟙 G) r hp hl hr hmul ha π χ
  · exact normalizedJacquetWeightSpace_le_unitaryJacquetPart
      (𝟙 G) (𝟙 G) r hp hl hr hmul ha π hχ
      (normalizedTemperedFullGroupExponent k G hG π A a hp hl ha U r hr hmul χ hπ hχ).1
  · rw [normalizedJacquetWeightSpace_eq_bot_of_not_isNormalizedJacquetExponent
      (𝟙 G) (𝟙 G) r hp hl hr hmul ha π hχ]
    exact bot_le

/-- The identity normalized Jacquet module of a tempered representation is
entirely its unitary part, for every matching represented radical. -/
theorem IsNormalizedExponentTempered.unitaryJacquetPart_identity_eq_top :
    unitaryJacquetPart (𝟙 G) (𝟙 G) r hp hl hr hmul ha π = ⊤ := by
  have := (isClosed_leviPoints (𝟙 G) (𝟙 G) hp hl).locallyCompactSpace
  let J := (jacquetFunctor (𝟙 G) (𝟙 G) r hp hr hl hmul).obj π
  let sourceMap := rationalPoints.map a
  let targetMap := splitComponentPointsMap ((𝟙 G) ≫ (𝟙 G)) a
  have hsourceMap : ∀ t, sourceMap t ∈ Subgroup.center (rationalPoints G) :=
    ha.isCentralSplitTorus.isCentral.map_mem_center
  have htargetMap : ∀ t, targetMap t ∈ Subgroup.center (pointImage ((𝟙 G) ≫ (𝟙 G))) :=
    splitComponentPointsMap_mem_center ((𝟙 G) ≫ (𝟙 G)) ha
  let f := normalizedJacquetCentralQuotient
    (pointImage (r ≫ 𝟙 G)) (pointImage ((𝟙 G) ≫ (𝟙 G)))
    (isClosed_pointImage_comp (𝟙 G) r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (pointImage_le_normalizer (𝟙 G) (𝟙 G) r hr) π sourceMap targetMap (fun _ => rfl) hsourceMap
  have honto : Function.Surjective f.toLinearMap :=
    Jacquet.Localization.mk_surjective π.representation (pointImage (r ≫ 𝟙 G)) 1
  have hspan := generalizedWeightSpace_iSup_eq_top π.representation sourceMap hsourceMap
    π.isSmooth (CentralDecomposition.admissible_centerFinite π.representation hπ.isAdmissible)
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  change (⊤ : Submodule ℂ J) ≤
    (unitaryJacquetPart (𝟙 G) (𝟙 G) r hp hl hr hmul ha π).toSubmodule
  rw [← LinearMap.range_eq_top.mpr honto, ← Submodule.map_top, ← hspan,
    Submodule.map_iSup]
  refine iSup_le fun χ => Submodule.map_le_iff_le_comap.mpr ?_
  intro x hx
  have hfx : f x ∈ normalizedJacquetWeightSpace (𝟙 G) (𝟙 G) r hp hl hr hmul ha π χ :=
    map_mem_generalizedWeightSpace_of_comp π.representation sourceMap hsourceMap J.representation targetMap htargetMap
      π.isSmooth J.isSmooth f.toLinearMap (fun t => (f.isIntertwining' t).symm) χ hx
  exact hπ.normalizedJacquetWeightSpace_identity_le_unitary hp hl r hr hmul ha χ hfx

/-- The nonunitary identity Jacquet part vanishes for a tempered source. -/
theorem IsNormalizedExponentTempered.nonunitaryJacquetPart_identity_eq_bot :
    nonunitaryJacquetPart (𝟙 G) (𝟙 G) r hp hl hr hmul ha π = ⊥ := by
  apply le_antisymm ?_ bot_le
  refine iSup_le fun χ => iSup_le fun hχ => iSup_le fun hne => ?_
  exact (hne
    (normalizedTemperedFullGroupExponent k G hG π A a hp hl ha U r hr hmul χ hπ hχ).1).elim

/-- The canonical coinvariant projection identifies a tempered representation
linearly with its actual unitary identity Jacquet part. -/
def temperedIdentityUnitaryJacquetEquiv :
    π ≃ₗ[ℂ]
      (SmoothRep.subrepresentation ((jacquetFunctor (𝟙 G) (𝟙 G) r hp hr hl hmul).obj π)
        (unitaryJacquetPart (𝟙 G) (𝟙 G) r hp hl hr hmul ha π)) := by
  let q := Jacquet.Localization.mk π.representation (pointImage (r ≫ 𝟙 G)) 1
  let f := q.codRestrict
    (unitaryJacquetPart (𝟙 G) (𝟙 G) r hp hl hr hmul ha π).toSubmodule
    (fun x => by
      rw [hπ.unitaryJacquetPart_identity_eq_top hp hl r hr hmul ha]
      exact Submodule.mem_top)
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y hxy
    have he := congrArg
      (endpointCoinvariantsEquiv _ (pointImage_identity_radical_eq_bot hG r hr) π)
      (congrArg Subtype.val hxy)
    change endpointCoinvariantsEquiv _ _ π (q x) =
      endpointCoinvariantsEquiv _ _ π (q y) at he
    simpa only [q, endpointCoinvariantsEquiv_mk] using he
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := Jacquet.Localization.mk_surjective π.representation
      (pointImage (r ≫ 𝟙 G)) 1 y
    exact ⟨x, Subtype.ext hx⟩

/-- The equivalence sends a source vector to its literal coinvariant class. -/
@[simp] theorem temperedIdentityUnitaryJacquetEquiv_apply (x : π) :
    (temperedIdentityUnitaryJacquetEquiv hπ hp hl r hr hmul ha x).val =
      Jacquet.Localization.mk π.representation (pointImage (r ≫ 𝟙 G)) 1 x :=
  rfl

/-- A nonzero tempered representation has nonzero unitary identity Jacquet part. -/
theorem IsNormalizedExponentTempered.nontrivial_unitaryJacquetPart_identity
    [Nontrivial π] :
    Nontrivial
      (SmoothRep.subrepresentation ((jacquetFunctor (𝟙 G) (𝟙 G) r hp hr hl hmul).obj π)
        (unitaryJacquetPart (𝟙 G) (𝟙 G) r hp hl hr hmul ha π)) :=
  (temperedIdentityUnitaryJacquetEquiv hπ hp hl r hr hmul ha).toEquiv.symm.nontrivial

omit hp hl r hr hmul ha in
/-- The family used in the minimal-parabolic argument is nonempty: choose an
actual split component and the canonical identity-parabolic radical. -/
theorem IsNormalizedExponentTempered.exists_nontrivial_unitaryJacquetPart
    [Nontrivial π] :
    ∃ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G)
      (ha : IsSplitComponent a),
      Nontrivial
        (SmoothRep.subrepresentation
          ((jacquetFunctor (𝟙 G) (𝟙 G) (kernelUnit G)
            hG.isParabolicSubgroup_id hG.isGeometricUnipotentRadical_kernelUnit
            hG.isRationalLeviSubgroup_id isIso_subgroupMultiplication_id_kernelUnit).obj π)
          (unitaryJacquetPart (𝟙 G) (𝟙 G) (kernelUnit G)
            hG.isParabolicSubgroup_id hG.isRationalLeviSubgroup_id
            hG.isGeometricUnipotentRadical_kernelUnit
            isIso_subgroupMultiplication_id_kernelUnit ha π)) := by
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k G hG).1
  exact ⟨A, a, ha, hπ.nontrivial_unitaryJacquetPart_identity
    hG.isParabolicSubgroup_id hG.isRationalLeviSubgroup_id (kernelUnit G)
    hG.isGeometricUnipotentRadical_kernelUnit
    isIso_subgroupMultiplication_id_kernelUnit ha⟩

end Langlands.Aubert.General.RepresentedParabolic
