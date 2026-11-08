import Langlands.Representation.Filtration.ObjectDefinitions
import Langlands.Representation.Jacquet.Normalized
import Langlands.Representation.Jacquet.ExactProof

/-!
# Collapse of a filtration under normalized Jacquet functors

Let `U` be a normal subgroup of a topological group `P` in which every finite set lies in a
compact open subgroup. Take a finite filtration of a representation `A` of `P` which is smooth
on `U`. Suppose the `U`-coinvariants of all graded quotients except the `j`th vanish. Then
coinvariants turn the inclusion of the `(j+1)`st step and the projection onto the `j`th graded
quotient into bijections. Hence the normalized Jacquet actions of `A` and of that graded quotient
are equivalent, for every normalizing subgroup and every modulus.
-/

noncomputable section

namespace Langlands.Whittaker

open scoped NNReal

universe uP uH uV uW

section Equivalence

variable {P : Type uP} [Group P]

/-- The linear map induced on `U`-coinvariants by an intertwiner. -/
abbrev coinvariantsMap (U : Subgroup P) {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ P V} {σ : Representation ℂ P W} (f : ρ.IntertwiningMap σ) :
    Jacquet.Coinvariants ρ U →ₗ[ℂ] Jacquet.Coinvariants σ U :=
  Representation.Coinvariants.map _ _ (Jacquet.restrictMap f U)

variable {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Restrict an equivalence of representations along a group homomorphism. -/
def representationEquivComp {H : Type uH} [Group H] {ρ : Representation ℂ P V}
    {σ : Representation ℂ P W} (e : ρ.Equiv σ) (f : H →* P) :
    Representation.Equiv (ρ.comp f) (σ.comp f) :=
  Representation.Equiv.mk e.toLinearEquiv (fun h => by
    ext v
    exact Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (f h) v)

/-- An equivalence of representations induces an equivalence of normalized Jacquet actions. -/
def normalizedEquivOfModulus {ρ : Representation ℂ P V} {σ : Representation ℂ P W}
    (N M : Subgroup P) (hMN : M ≤ Subgroup.normalizer N) (δ : M →* ℝ≥0ˣ) (e : ρ.Equiv σ) :
    Representation.Equiv (Jacquet.normalizedActionOfModulus ρ N M hMN δ)
      (Jacquet.normalizedActionOfModulus σ N M hMN δ) :=
  (Jacquet.normalizedMapOfModulus N M hMN δ e.toIntertwiningMap).ofBijective (by
      have hleft : Function.LeftInverse
          (Jacquet.normalizedMapOfModulus N M hMN δ e.symm.toIntertwiningMap)
          (Jacquet.normalizedMapOfModulus N M hMN δ e.toIntertwiningMap) := by
        intro x
        obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ N x
        rw [Jacquet.normalizedMapOfModulus_mk, Jacquet.normalizedMapOfModulus_mk]
        exact congrArg (Jacquet.mk ρ N) (e.symm_apply_apply v)
      have hright : Function.RightInverse
          (Jacquet.normalizedMapOfModulus N M hMN δ e.symm.toIntertwiningMap)
          (Jacquet.normalizedMapOfModulus N M hMN δ e.toIntertwiningMap) := by
        intro x
        obtain ⟨w, rfl⟩ := Jacquet.mk_surjective σ N x
        rw [Jacquet.normalizedMapOfModulus_mk, Jacquet.normalizedMapOfModulus_mk]
        exact congrArg (Jacquet.mk σ N) (e.apply_symm_apply w)
      exact ⟨hleft.injective, hright.surjective⟩)

/-- Equivalent representations have equivalent coinvariants; in particular vanishing transfers. -/
theorem subsingleton_coinvariants_of_equiv {ρ : Representation ℂ P V}
    {σ : Representation ℂ P W} (N : Subgroup P) (e : ρ.Equiv σ)
    [Subsingleton (Jacquet.Coinvariants σ N)] : Subsingleton (Jacquet.Coinvariants ρ N) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ N a
  obtain ⟨w, rfl⟩ := Jacquet.mk_surjective ρ N b
  rw [← e.symm_apply_apply v, ← e.symm_apply_apply w]
  have h : Jacquet.mk σ N (e v) = Jacquet.mk σ N (e w) := Subsingleton.elim _ _
  change coinvariantsMap N e.symm.toIntertwiningMap (Jacquet.mk σ N (e v)) =
    coinvariantsMap N e.symm.toIntertwiningMap (Jacquet.mk σ N (e w))
  rw [h]

end Equivalence

section Collapse

variable {P : Type uP} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
variable {A : Rep.{uV} ℂ P} {m : ℕ}

/-- The inclusion of one step of an object filtration into a later step. -/
def stepInclusion (s : ObjectRepFiltration A m) {k l : Fin (m + 1)} (h : k ≤ l) :
    (s.subrepresentation k).toRepresentation.IntertwiningMap
      (s.subrepresentation l).toRepresentation where
  toLinearMap := Submodule.inclusion (s.monotone_subrepresentation h)
  isIntertwining' _ := rfl

/-- The inclusion of one step of an object filtration into the ambient representation. -/
def stepSubtype (s : ObjectRepFiltration A m) (k : Fin (m + 1)) :
    (s.subrepresentation k).toRepresentation.IntertwiningMap A.ρ where
  toLinearMap := (s.subrepresentation k).toSubmodule.subtype
  isIntertwining' _ := rfl

omit [TopologicalSpace P] [IsTopologicalGroup P] in
theorem range_stepInclusion_eq_ker (s : ObjectRepFiltration A m) (i : Fin m) :
    LinearMap.range (stepInclusion s (Fin.castSucc_le_succ i)).toLinearMap =
      LinearMap.ker (s.gradedProjection i).hom.toLinearMap := by
  ext v
  change v ∈ LinearMap.range
      (Submodule.inclusion (s.monotone_subrepresentation (Fin.castSucc_le_succ i))) ↔
    (Submodule.Quotient.mk v : _ ⧸ (_ : Submodule ℂ _)) = 0
  rw [Submodule.range_inclusion]
  exact (Submodule.Quotient.mk_eq_zero _).symm

theorem coinvariantsMap_range_eq_ker (U : Subgroup P) (s : ObjectRepFiltration A m) (i : Fin m) :
    LinearMap.range (coinvariantsMap U (stepInclusion s (Fin.castSucc_le_succ i))) =
      LinearMap.ker (coinvariantsMap U (s.gradedProjection i).hom) :=
  coinvariants_map_range_eq_ker _ _ (s.gradedProjection_surjective i)
    (range_stepInclusion_eq_ker s i)

/-- If all graded quotients except the `j`th have vanishing `U`-coinvariants, the coinvariant
maps of the inclusion of step `j + 1` and of the projection onto the `j`th quotient are
bijective. -/
theorem coinvariants_filtration_bijective (U : Subgroup P)
    (hU : ∀ t : Finset U, ∃ K : OpenSubgroup U, IsCompact (K : Set U) ∧ ∀ g ∈ t, g ∈ K)
    (hA : IsSmooth (A.ρ.comp U.subtype)) (s : ObjectRepFiltration A m) (j : Fin m)
    (hvan : ∀ i, i ≠ j → Subsingleton (Jacquet.Coinvariants (s.gradedRepresentation i).ρ U)) :
    Function.Bijective (coinvariantsMap U (stepSubtype s j.succ)) ∧
      Function.Bijective (coinvariantsMap U (s.gradedProjection j).hom) := by
  -- The early steps have vanishing coinvariants.
  have hzero : ∀ k : Fin (m + 1), k ≤ j.castSucc →
      ∀ x : Jacquet.Coinvariants (s.subrepresentation k).toRepresentation U, x = 0 := by
    intro k
    induction k using Fin.induction with
    | zero =>
      intro _ x
      obtain ⟨v, rfl⟩ := Jacquet.mk_surjective _ U x
      obtain ⟨w, hw⟩ := v
      have hw' : w ∈ (⊥ : Subrepresentation A.ρ).toSubmodule := by
        rw [← s.subrepresentation_zero]
        exact hw
      have hv : (⟨w, hw⟩ : (s.subrepresentation 0).toSubmodule) = 0 := Subtype.ext hw'
      rw [hv, map_zero]
    | succ i ih =>
      intro hi x
      have hij : i < j := Fin.succ_le_castSucc_iff.mp hi
      have hsub := hvan i (ne_of_lt hij)
      have hker : x ∈ LinearMap.ker (coinvariantsMap U (s.gradedProjection i).hom) :=
        Subsingleton.elim _ _
      rw [← coinvariantsMap_range_eq_ker U s i] at hker
      obtain ⟨y, rfl⟩ := hker
      rw [ih (Fin.castSucc_le_castSucc_iff.mpr hij.le) y, map_zero]
  -- The late steps surject onto the coinvariants of the ambient representation.
  have hsurj : ∀ k : Fin (m + 1), j.succ ≤ k →
      Function.Surjective (coinvariantsMap U (stepSubtype s k)) := by
    intro k
    induction k using Fin.reverseInduction with
    | last =>
      intro _
      apply coinvariants_map_surjective
      intro v
      have hv : v ∈ (s.subrepresentation (Fin.last m)).toSubmodule := by
        rw [s.subrepresentation_last]
        trivial
      exact ⟨⟨v, hv⟩, rfl⟩
    | cast i ih =>
      intro hi
      have hji : j < i := Fin.succ_le_castSucc_iff.mp hi
      have hsub := hvan i (ne_of_gt hji)
      have hincl : Function.Surjective
          (coinvariantsMap U (stepInclusion s (Fin.castSucc_le_succ i))) := by
        intro x
        have hker : x ∈ LinearMap.ker (coinvariantsMap U (s.gradedProjection i).hom) :=
          Subsingleton.elim _ _
        rw [← coinvariantsMap_range_eq_ker U s i] at hker
        exact hker
      have hcomp : ∀ y, coinvariantsMap U (stepSubtype s i.castSucc) y =
          coinvariantsMap U (stepSubtype s i.succ)
            (coinvariantsMap U (stepInclusion s (Fin.castSucc_le_succ i)) y) := by
        intro y
        obtain ⟨v, rfl⟩ := Jacquet.mk_surjective _ U y
        rfl
      intro x
      obtain ⟨y, rfl⟩ := ih (Fin.succ_le_succ_iff.mpr hji.le) x
      obtain ⟨z, rfl⟩ := hincl y
      exact ⟨z, hcomp z⟩
  refine ⟨⟨?_, hsurj j.succ le_rfl⟩, ⟨?_, ?_⟩⟩
  · exact coinvariants_map_injective_of_smooth hU (Jacquet.restrictMap (stepSubtype s j.succ) U)
      Subtype.val_injective hA
  · rw [← LinearMap.ker_eq_bot, ← coinvariantsMap_range_eq_ker U s j, LinearMap.range_eq_bot]
    apply LinearMap.ext
    intro y
    rw [hzero j.castSucc le_rfl y, map_zero]
    rfl
  · exact coinvariants_map_surjective _ (s.gradedProjection_surjective j)

/-- Under the hypotheses of `coinvariants_filtration_bijective`, the normalized Jacquet action of
the ambient representation is equivalent to that of the surviving graded quotient. -/
def coinvariantsFiltrationEquiv (U : Subgroup P)
    (hU : ∀ t : Finset U, ∃ K : OpenSubgroup U, IsCompact (K : Set U) ∧ ∀ g ∈ t, g ∈ K)
    (hA : IsSmooth (A.ρ.comp U.subtype)) (s : ObjectRepFiltration A m) (j : Fin m)
    (hvan : ∀ i, i ≠ j → Subsingleton (Jacquet.Coinvariants (s.gradedRepresentation i).ρ U))
    (M : Subgroup P) (hMU : M ≤ Subgroup.normalizer U) (δ : M →* ℝ≥0ˣ) :
    Representation.Equiv (Jacquet.normalizedActionOfModulus A.ρ U M hMU δ)
      (Jacquet.normalizedActionOfModulus (s.gradedRepresentation j).ρ U M hMU δ) :=
  ((Jacquet.normalizedMapOfModulus U M hMU δ (stepSubtype s j.succ)).ofBijective
      (coinvariants_filtration_bijective U hU hA s j hvan).1).symm.trans
    ((Jacquet.normalizedMapOfModulus U M hMU δ (s.gradedProjection j).hom).ofBijective
      (coinvariants_filtration_bijective U hU hA s j hvan).2)

end Collapse

end Langlands.Whittaker
