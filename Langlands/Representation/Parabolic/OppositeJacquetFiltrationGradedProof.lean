import Langlands.Representation.Parabolic.OppositeJacquetFiltrationGradedStatement
import Langlands.Representation.Parabolic.OppositeRefinementExactnessProof
import Langlands.Representation.Parabolic.FlattenedOppositeUnipotentComparisonProof
import Langlands.Representation.Classification.CuspidalJacquetFunctorExactnessProof
import Langlands.Representation.Filtration.MultiplicityAdditivityProof

noncomputable section

namespace Langlands.Jacquet.OppositeImageGradedProof

universe uG uH uV

variable {G : Type uG} [Group G] {H : Type uH} [Group H]
  (U : Subgroup G) (f : H →* Subgroup.normalizer (U : Set G)) (χ : H →* ℂˣ)
  {A : Rep.{uV} ℂ G}

private abbrev normalizedAction {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :=
  twist χ ((action ρ U (Subgroup.normalizer U) le_rfl).comp f)

private def normalizedMap {V W : Type uV} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (a : ρ.IntertwiningMap σ) :
    (normalizedAction U f χ ρ).IntertwiningMap (normalizedAction U f χ σ) :=
  twistIntertwining χ
    { toLinearMap := (map U (Subgroup.normalizer U) le_rfl a).toLinearMap
      isIntertwining' h :=
        (map U (Subgroup.normalizer U) le_rfl a).isIntertwining' (f h) }

private def stepEmbedding (S : Subrepresentation A.ρ) :
    S.toRepresentation.IntertwiningMap A.ρ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

private def stepInclusion (S T : Subrepresentation A.ρ) (hST : S ≤ T) :
    S.toRepresentation.IntertwiningMap T.toRepresentation where
  toLinearMap := Submodule.inclusion hST
  isIntertwining' _ := rfl

private theorem adjacent_exact {l : ℕ} (s : ObjectRepFiltration A l) (i : Fin l) :
    LinearMap.range
        (stepInclusion (s.subrepresentation i.castSucc) (s.subrepresentation i.succ)
          (s.monotone_subrepresentation (Fin.castSucc_le_succ i))).toLinearMap =
      LinearMap.ker (s.gradedProjection i).hom.toLinearMap := by
  have hpzero (w : (s.subrepresentation i.succ).toSubmodule) :
      (s.gradedProjection i).hom w = 0 ↔ (w : A) ∈ s.subrepresentation i.castSucc :=
    Submodule.Quotient.mk_eq_zero _
  ext w
  change (∃ v, stepInclusion _ _ _ v = w) ↔ (s.gradedProjection i).hom w = 0
  rw [hpzero]
  constructor
  · rintro ⟨v, rfl⟩
    exact v.property
  · intro hw
    exact ⟨⟨w.val, hw⟩, Subtype.ext rfl⟩

private def stepImageMap (S : Subrepresentation A.ρ) :
    (normalizedAction U f χ S.toRepresentation).IntertwiningMap
      (normalizedImageSubrepresentation U f χ A.ρ S).toRepresentation where
  toLinearMap := (normalizedMap U f χ (stepEmbedding S)).toLinearMap.codRestrict
    (normalizedImageSubrepresentation U f χ A.ρ S).toSubmodule (by
      intro q
      obtain ⟨v, rfl⟩ := mk_surjective S.toRepresentation U q
      exact ⟨v.val, v.property, rfl⟩)
  isIntertwining' h := by
    apply LinearMap.ext
    intro q
    apply Subtype.ext
    exact LinearMap.congr_fun
      ((normalizedMap U f χ (stepEmbedding S)).isIntertwining' h) q

variable [TopologicalSpace G] [IsTopologicalGroup G]

private theorem normalizedMap_injective {V W : Type uV}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (hU : ∀ z : Finset U, ∃ K : OpenSubgroup U,
      IsCompact (K : Set U) ∧ ∀ u ∈ z, u ∈ K)
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (a : ρ.IntertwiningMap σ) (ha : Function.Injective a) (hσ : IsSmooth σ) :
    Function.Injective (normalizedMap U f χ a) :=
  coinvariants_map_injective_of_smooth hU (restrictMap a U) ha
    (isSmooth_comp U.subtype continuous_subtype_val hσ)

private def stepImageEquiv
    (hU : ∀ z : Finset U, ∃ K : OpenSubgroup U,
      IsCompact (K : Set U) ∧ ∀ u ∈ z, u ∈ K)
    (hA : IsSmooth A.ρ) (S : Subrepresentation A.ρ) :
    (normalizedAction U f χ S.toRepresentation).Equiv
      (normalizedImageSubrepresentation U f χ A.ρ S).toRepresentation :=
  (stepImageMap U f χ S).ofBijective ⟨by
    intro x y hxy
    exact normalizedMap_injective U f χ hU (stepEmbedding S)
      Subtype.val_injective hA (congrArg Subtype.val hxy), by
    rintro ⟨q, hq⟩
    obtain ⟨v, hv, rfl⟩ := hq
    exact ⟨mk S.toRepresentation U ⟨v, hv⟩, rfl⟩⟩

private theorem adjacent_image_kernel
    (hU : ∀ z : Finset U, ∃ K : OpenSubgroup U,
      IsCompact (K : Set U) ∧ ∀ u ∈ z, u ∈ K)
    (hA : IsSmooth A.ρ) {l : ℕ} (s : ObjectRepFiltration A l) (i : Fin l)
    (y : Coinvariants (s.subrepresentation i.succ).toRepresentation U) :
    normalizedMap U f χ (stepEmbedding (s.subrepresentation i.succ)) y ∈
        normalizedImageSubrepresentation U f χ A.ρ (s.subrepresentation i.castSucc) ↔
      normalizedMap U f χ (s.gradedProjection i).hom y = 0 := by
  let S := s.subrepresentation i.castSucc
  let T := s.subrepresentation i.succ
  let inc := stepInclusion S T (s.monotone_subrepresentation (Fin.castSucc_le_succ i))
  have hex := coinvariants_map_range_eq_ker (restrictMap inc U)
    (restrictMap (s.gradedProjection i).hom U)
    (s.gradedProjection_surjective i) (adjacent_exact s i)
  change LinearMap.range (normalizedMap U f χ inc).toLinearMap =
    LinearMap.ker (normalizedMap U f χ (s.gradedProjection i).hom).toLinearMap at hex
  constructor
  · rintro ⟨v, hv, hvy⟩
    have hz :
        normalizedMap U f χ (stepEmbedding T)
            (normalizedMap U f χ inc (mk S.toRepresentation U ⟨v, hv⟩)) =
          normalizedMap U f χ (stepEmbedding T) y := hvy
    have hinj := normalizedMap_injective U f χ hU (stepEmbedding T)
      Subtype.val_injective hA
    have hy : y ∈ LinearMap.range (normalizedMap U f χ inc).toLinearMap :=
      ⟨mk S.toRepresentation U ⟨v, hv⟩, hinj hz⟩
    rw [hex] at hy
    exact hy
  · intro hy
    have hy' : y ∈ LinearMap.ker
        (normalizedMap U f χ (s.gradedProjection i).hom).toLinearMap := hy
    rw [← hex] at hy'
    obtain ⟨z, rfl⟩ := hy'
    obtain ⟨v, rfl⟩ := mk_surjective S.toRepresentation U z
    exact ⟨v.val, v.property, rfl⟩

/-- Ordinary exactness identifies the grades of the actual normalized images. -/
theorem normalizedImageGraded
    (hU : ∀ z : Finset U, ∃ K : OpenSubgroup U,
      IsCompact (K : Set U) ∧ ∀ u ∈ z, u ∈ K)
    (hA : IsSmooth A.ρ) {l : ℕ} (s : ObjectRepFiltration A l) (i : Fin l) :
    Nonempty (((normalizedImageFiltration U f χ A.ρ s).gradedRepresentation i).ρ.Equiv
      (normalizedAction U f χ (s.gradedRepresentation i).ρ)) := by
  let S := normalizedImageSubrepresentation U f χ A.ρ (s.subrepresentation i.castSucc)
  let T := normalizedImageSubrepresentation U f χ A.ρ (s.subrepresentation i.succ)
  let e := stepImageEquiv U f χ hU hA (s.subrepresentation i.succ)
  let p := normalizedMap U f χ (s.gradedProjection i).hom
  let a : T.toRepresentation.IntertwiningMap
      (normalizedAction U f χ (s.gradedRepresentation i).ρ) :=
    p.comp e.symm.toIntertwiningMap
  change Nonempty ((LengthCriterionProof.quotientRep S T).Equiv
    (normalizedAction U f χ (s.gradedRepresentation i).ρ))
  apply MultiplicityAdditivityProof.quotient_equiv_of_surjective
    (A := Rep.of (normalizedAction U f χ A.ρ))
    (B := Rep.of (normalizedAction U f χ (s.gradedRepresentation i).ρ)) S T a
  · intro x
    change (x : Coinvariants A.ρ U) ∈ S ↔ p (e.symm x) = 0
    have h := adjacent_image_kernel U f χ hU hA s i (e.symm x)
    have he :
        normalizedMap U f χ (stepEmbedding (s.subrepresentation i.succ)) (e.symm x) =
          (x : Coinvariants A.ρ U) := by
      change (e (e.symm x)).val = x.val
      rw [e.apply_symm_apply]
    rwa [he] at h
  · exact (coinvariants_map_surjective (restrictMap (s.gradedProjection i).hom U)
      (s.gradedProjection_surjective i)).comp e.symm.toLinearEquiv.surjective

end Langlands.Jacquet.OppositeImageGradedProof

namespace Langlands.Parabolic

open GeneralLinear Geometric Jacquet.OppositeImageGradedProof

universe uF uV

/-- Both fixed normalized opposite image filtrations have the required grades. -/
theorem normalizedOppositeJacquetFiltrationGraded :
    NormalizedOppositeJacquetFiltrationGradedStatement.{uF, uV} := by
  intro p hp F T n B S
  constructor
  · let := T.topology
    let := T.leviTopologicalGroup B
    intro V hV hMV ρ hρ l s i
    exact normalizedImageGraded (refinedOppositeUnipotent F.Carrier B S)
      (refinedOppositeLeviNormalizer F.Carrier B S)
      (Jacquet.inverseHalfCharacter (T.refinedOppositeLeviModulus B S))
      (T.refinedOppositeUnipotent_finite_containment B S) hρ s i
  · let := T.topology
    let := T.generalLinearTopologicalGroup n
    intro V hV hMV ρ hρ l s i
    have hU : ∀ z : Finset (composedOppositeUnipotent F.Carrier B S),
        ∃ K : OpenSubgroup (composedOppositeUnipotent F.Carrier B S),
          IsCompact (K : Set (composedOppositeUnipotent F.Carrier B S)) ∧
          ∀ u ∈ z, u ∈ K := by
      rw [flattenedOppositeUnipotentComparison F.Carrier n B S]
      exact CuspidalJacquetMultiplicity.oppositeUnipotent_finite_containment T (B.flatten S)
    exact normalizedImageGraded (composedOppositeUnipotent F.Carrier B S)
      (composedOppositeLeviNormalizer F.Carrier B S)
      (Jacquet.inverseHalfCharacter (T.composedOppositeLeviModulus B S)) hU hρ s i

end Langlands.Parabolic
