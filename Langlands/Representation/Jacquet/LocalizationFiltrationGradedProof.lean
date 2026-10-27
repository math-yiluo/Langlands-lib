import Langlands.Representation.Jacquet.LocalizationFiltrationGradedStatement
import Langlands.Representation.Jacquet.LocalizationExactnessProof
import Langlands.Representation.Filtration.MultiplicityAdditivityProof

noncomputable section

namespace Langlands.Jacquet.Localization

universe uG uV

namespace ImageFiltrationGradedProof

variable {G : Type uG} [Group G] {A : Rep.{uV} ℂ G}

private def stepEmbedding (S : Subrepresentation A.ρ) :
    S.toRepresentation.IntertwiningMap A.ρ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

private def stepInclusion (S T : Subrepresentation A.ρ) (hST : S ≤ T) :
    S.toRepresentation.IntertwiningMap T.toRepresentation where
  toLinearMap := Submodule.inclusion hST
  isIntertwining' _ := rfl

private theorem adjacent_exact {n : ℕ} (s : ObjectRepFiltration A n) (i : Fin n) :
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

private def stepImageMap (U : Subgroup G) (θ : U →* ℂˣ) (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer U) (hθ : IsInvariant U M hMU θ)
    (S : Subrepresentation A.ρ) :
    (action S.toRepresentation U θ M hMU hθ).IntertwiningMap
      (imageSubrepresentation U θ M hMU hθ A.ρ S).toRepresentation where
  toLinearMap := (map U θ M hMU hθ (stepEmbedding S)).toLinearMap.codRestrict
    (imageSubrepresentation U θ M hMU hθ A.ρ S).toSubmodule (by
      intro q
      obtain ⟨v, rfl⟩ := mk_surjective S.toRepresentation U θ q
      exact ⟨v.val, v.property, rfl⟩)
  isIntertwining' m := by
    apply LinearMap.ext
    intro q
    apply Subtype.ext
    exact LinearMap.congr_fun
      ((map U θ M hMU hθ (stepEmbedding S)).isIntertwining' m) q

variable [TopologicalSpace G] [IsTopologicalGroup G]

private def stepImageEquiv
    (U : Subgroup G) (hU : IsLimitOfCompactSubgroups U)
    (θ : U →* ℂˣ) (hθloc : IsLocallyConstant (fun u : U => (θ u : ℂ)))
    (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U) (hθ : IsInvariant U M hMU θ)
    (hA : IsSmooth A.ρ) (S : Subrepresentation A.ρ) :
    (action S.toRepresentation U θ M hMU hθ).Equiv
      (imageSubrepresentation U θ M hMU hθ A.ρ S).toRepresentation :=
  (stepImageMap U θ M hMU hθ S).ofBijective ⟨by
    intro x y hxy
    exact map_injective_of_smooth U hU θ hθloc M hMU hθ (stepEmbedding S)
      Subtype.val_injective hA (congrArg Subtype.val hxy), by
    rintro ⟨q, hq⟩
    obtain ⟨v, hv, rfl⟩ := hq
    exact ⟨mk S.toRepresentation U θ ⟨v, hv⟩, rfl⟩⟩

private theorem localized_adjacent_kernel
    (U : Subgroup G) (hU : IsLimitOfCompactSubgroups U)
    (θ : U →* ℂˣ) (hθloc : IsLocallyConstant (fun u : U => (θ u : ℂ)))
    (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U) (hθ : IsInvariant U M hMU θ)
    (hA : IsSmooth A.ρ) {n : ℕ} (s : ObjectRepFiltration A n) (i : Fin n)
    (y : Coinvariants (s.subrepresentation i.succ).toRepresentation U θ) :
    map U θ M hMU hθ (stepEmbedding (s.subrepresentation i.succ)) y ∈
        imageSubrepresentation U θ M hMU hθ A.ρ (s.subrepresentation i.castSucc) ↔
      map U θ M hMU hθ (s.gradedProjection i).hom y = 0 := by
  let S := s.subrepresentation i.castSucc
  let T := s.subrepresentation i.succ
  let inc := stepInclusion S T (s.monotone_subrepresentation (Fin.castSucc_le_succ i))
  have hex := map_range_eq_ker U θ M hMU hθ inc (s.gradedProjection i).hom
    (s.gradedProjection_surjective i) (adjacent_exact s i)
  constructor
  · rintro ⟨v, hv, hvy⟩
    have hz :
        map U θ M hMU hθ (stepEmbedding T)
            (map U θ M hMU hθ inc (mk S.toRepresentation U θ ⟨v, hv⟩)) =
          map U θ M hMU hθ (stepEmbedding T) y := hvy
    have hinj := map_injective_of_smooth U hU θ hθloc M hMU hθ (stepEmbedding T)
      Subtype.val_injective hA
    have hy : y ∈ LinearMap.range (map U θ M hMU hθ inc).toLinearMap :=
      ⟨mk S.toRepresentation U θ ⟨v, hv⟩, hinj hz⟩
    rw [hex] at hy
    exact hy
  · intro hy
    have hy' : y ∈ LinearMap.ker
        (map U θ M hMU hθ (s.gradedProjection i).hom).toLinearMap := hy
    rw [← hex] at hy'
    obtain ⟨z, rfl⟩ := hy'
    obtain ⟨v, rfl⟩ := mk_surjective S.toRepresentation U θ z
    exact ⟨v.val, v.property, rfl⟩

end ImageFiltrationGradedProof

open ImageFiltrationGradedProof

/-- Localized step inclusions identify their sources with the actual image
steps; exactness then identifies every actual graded quotient. -/
theorem imageFiltrationGraded : ImageFiltrationGradedStatement.{uG, uV} := by
  intro G _ _ _ U hU θ hθloc M hMU hθ A hA n s
  let t : ObjectRepFiltration (Rep.of (action A.ρ U θ M hMU hθ)) n :=
    ObjectRepFiltration.ofSubrepresentations
      (fun k => imageSubrepresentation U θ M hMU hθ A.ρ (s.subrepresentation k))
      (fun _ _ h => imageSubrepresentation_mono U θ M hMU hθ A.ρ
        (s.monotone_subrepresentation h))
      (by rw [s.subrepresentation_zero, imageSubrepresentation_bot])
      (by rw [s.subrepresentation_last, imageSubrepresentation_top])
  refine ⟨t, fun _ => rfl, ?_⟩
  intro i
  let S := imageSubrepresentation U θ M hMU hθ A.ρ (s.subrepresentation i.castSucc)
  let T := imageSubrepresentation U θ M hMU hθ A.ρ (s.subrepresentation i.succ)
  let e := stepImageEquiv U hU θ hθloc M hMU hθ hA (s.subrepresentation i.succ)
  let p := map U θ M hMU hθ (s.gradedProjection i).hom
  let f : T.toRepresentation.IntertwiningMap
      (action (s.gradedRepresentation i).ρ U θ M hMU hθ) :=
    p.comp e.symm.toIntertwiningMap
  change Nonempty ((LengthCriterionProof.quotientRep S T).Equiv
    (action (s.gradedRepresentation i).ρ U θ M hMU hθ))
  apply MultiplicityAdditivityProof.quotient_equiv_of_surjective
    (A := Rep.of (action A.ρ U θ M hMU hθ))
    (B := Rep.of (action (s.gradedRepresentation i).ρ U θ M hMU hθ)) S T f
  · intro x
    change (x : Coinvariants A.ρ U θ) ∈ S ↔ p (e.symm x) = 0
    have h := localized_adjacent_kernel U hU θ hθloc M hMU hθ hA s i (e.symm x)
    have he :
        map U θ M hMU hθ (stepEmbedding (s.subrepresentation i.succ)) (e.symm x) =
          (x : Coinvariants A.ρ U θ) := by
      change (e (e.symm x)).val = x.val
      rw [e.apply_symm_apply]
    rwa [he] at h
  · exact (map_surjective U θ M hMU hθ (s.gradedProjection i).hom
      (s.gradedProjection_surjective i)).comp e.symm.toLinearEquiv.surjective

end Langlands.Jacquet.Localization
