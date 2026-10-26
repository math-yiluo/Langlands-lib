import Langlands.Representation.Jacquet.LocalizationFiltrationCollapseStatement
import Langlands.Representation.Jacquet.LocalizationExactnessProof

noncomputable section

namespace Langlands.Jacquet.Localization

universe uG uV

variable {G : Type uG} [Group G]

private def stepEmbedding {A : Rep.{uV} ℂ G} (S : Subrepresentation A.ρ) :
    S.toRepresentation.IntertwiningMap A.ρ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

private def stepInclusion {A : Rep.{uV} ℂ G} (S T : Subrepresentation A.ρ)
    (hST : S ≤ T) : S.toRepresentation.IntertwiningMap T.toRepresentation where
  toLinearMap := Submodule.inclusion hST
  isIntertwining' _ := rfl

private theorem adjacent_exact {A : Rep.{uV} ℂ G} {m : ℕ}
    (s : ObjectRepFiltration A m) (i : Fin m) :
    LinearMap.range
        (stepInclusion (s.subrepresentation i.castSucc)
          (s.subrepresentation i.succ)
          (s.monotone_subrepresentation (Nat.le_succ i.val))).toLinearMap =
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

/-- Finite induction on the actual localized adjacent short exact sequences. -/
theorem filtrationCollapse : FiltrationCollapseStatement.{uG, uV} := by
  intro G _ _ _ hG θ hθ A hA m s j hvanish
  let U : Subgroup G := ⊤
  let η : U →* ℂˣ := θ.comp U.subtype
  have hηloc : IsLocallyConstant (fun u : U => (η u : ℂ)) :=
    hθ.comp_continuous continuous_subtype_val
  have hMU : (⊥ : Subgroup G) ≤ Subgroup.normalizer U := bot_le
  have hηinv : IsInvariant U ⊥ hMU η := by
    intro a u
    apply congrArg η
    apply Subtype.ext
    have ha : (a : G) = 1 := Subgroup.mem_bot.mp a.property
    simp [conjugate, ha]
  let C (k : Fin (m + 1)) :=
    Coinvariants (s.subrepresentation k).toRepresentation U η
  let D (i : Fin m) := Coinvariants (s.gradedRepresentation i).ρ U η
  let inc (i : Fin m) :=
    stepInclusion (s.subrepresentation i.castSucc) (s.subrepresentation i.succ)
      (s.monotone_subrepresentation (Nat.le_succ i.val))
  let f (i : Fin m) : C i.castSucc →ₗ[ℂ] C i.succ := mapLinear U η (inc i)
  let p (i : Fin m) : C i.succ →ₗ[ℂ] D i :=
    mapLinear U η (s.gradedProjection i).hom
  have hsmooth (k : Fin (m + 1)) : IsSmooth (s.subrepresentation k).toRepresentation :=
    isSmooth_of_injective (stepEmbedding _) Subtype.val_injective hA
  have hinj (i : Fin m) : Function.Injective (f i) :=
    map_injective_of_smooth U hG η hηloc ⊥ hMU hηinv (inc i)
      (by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : (s.subrepresentation i.succ).toSubmodule => (z : A)) h)
      (hsmooth i.succ)
  have hex (i : Fin m) : LinearMap.range (f i) = LinearMap.ker (p i) :=
    map_range_eq_ker U η ⊥ hMU hηinv (inc i) (s.gradedProjection i).hom
      (s.gradedProjection_surjective i) (adjacent_exact s i)
  have hsurj (i : Fin m) : Function.Surjective (p i) :=
    map_surjective U η ⊥ hMU hηinv (s.gradedProjection i).hom
      (s.gradedProjection_surjective i)
  have hoff (i : Fin m) (hij : i ≠ j) : Function.Bijective (f i) := by
    refine ⟨hinj i, ?_⟩
    intro y
    have hy : y ∈ LinearMap.ker (p i) := (hvanish i hij).elim _ _
    rw [← hex i] at hy
    exact hy
  have hzero : Subsingleton (C 0) := by
    let : Subsingleton (s.subrepresentation 0).toSubmodule := by
      rw [s.subrepresentation_zero]
      change Subsingleton (⊥ : Submodule ℂ A)
      infer_instance
    infer_instance
  have hind (k : Fin (m + 1)) :
      (k.val ≤ j.val → Subsingleton (C k)) ∧
      (j.val < k.val → Nonempty (C k ≃ₗ[ℂ] D j)) := by
    induction k using Fin.induction with
    | zero =>
        constructor
        · intro _
          exact hzero
        · intro h
          simp at h
    | @succ i ih =>
        constructor
        · intro hi
          have hij : i ≠ j := by
            intro hij
            subst i
            simp at hi
          let : Subsingleton (C i.castSucc) := ih.1 (by
            change i.val ≤ j.val
            have : i.val + 1 ≤ j.val := hi
            omega)
          refine ⟨fun x y => ?_⟩
          obtain ⟨x, rfl⟩ := (hoff i hij).2 x
          obtain ⟨y, rfl⟩ := (hoff i hij).2 y
          exact congrArg (f i) (Subsingleton.elim x y)
        · intro hi
          by_cases hij : i = j
          · subst i
            let : Subsingleton (C j.castSucc) := ih.1 (by simp)
            refine ⟨LinearEquiv.ofBijective (p j) ⟨?_, hsurj j⟩⟩
            intro x y hxy
            have hmem : x - y ∈ LinearMap.ker (p j) := by
              simp only [LinearMap.mem_ker, map_sub, hxy, sub_self]
            rw [← hex j] at hmem
            obtain ⟨z, hz⟩ := hmem
            have hz0 : z = 0 := Subsingleton.elim _ _
            rw [hz0, map_zero] at hz
            exact sub_eq_zero.mp hz.symm
          · have hlt : j.val < i.castSucc.val := by
              have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
              change j.val < i.val
              have : j.val < i.val + 1 := hi
              omega
            obtain ⟨e⟩ := ih.2 hlt
            exact ⟨(LinearEquiv.ofBijective (f i) (hoff i hij)).symm.trans e⟩
  obtain ⟨e⟩ := (hind (Fin.last m)).2 j.isLt
  let a := stepEmbedding (s.subrepresentation (Fin.last m))
  have ha : Function.Surjective a := by
    intro v
    refine ⟨⟨v, ?_⟩, rfl⟩
    rw [s.subrepresentation_last]
    trivial
  have haL : Function.Bijective (mapLinear U η a) :=
    ⟨map_injective_of_smooth U hG η hηloc ⊥ hMU hηinv a Subtype.val_injective hA,
      map_surjective U η ⊥ hMU hηinv a ha⟩
  exact ⟨(LinearEquiv.ofBijective (mapLinear U η a) haL).symm.trans e⟩

end Langlands.Jacquet.Localization
