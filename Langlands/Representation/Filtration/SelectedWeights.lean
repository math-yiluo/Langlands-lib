import Langlands.Representation.Exponents.SelectedWeights
import Langlands.Representation.Filtration.ObjectDefinitions
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof

/-! Restriction of actual finite filtrations to selected generalized weights. -/

noncomputable section

namespace Langlands.ObjectRepFiltration

universe uR uG uA uV uW

section Algebra

variable {R : Type uR} [Field R] {G : Type uG} [Monoid G]
  {B : Rep.{uV} R G} {n : ℕ}

/-- Intersect every step with a supplied invariant subspace. Repeated steps and
zero grades are retained. -/
def intersect (s : ObjectRepFiltration B n) (S : Subrepresentation B.ρ) :
    ObjectRepFiltration (Rep.of S.toRepresentation) n :=
  ofSubrepresentations
    (fun i => {
      toSubmodule := (s.subrepresentation i).toSubmodule.comap S.toSubmodule.subtype
      apply_mem_toSubmodule g _ hv := (s.subrepresentation i).apply_mem_toSubmodule g hv })
    (fun _ _ hij _ hv => s.monotone_subrepresentation hij hv)
    (by
      apply Subrepresentation.toSubmodule_injective
      apply le_antisymm _ bot_le
      intro v hv
      have hv' : (v : B) ∈ s.subrepresentation 0 := hv
      rw [s.subrepresentation_zero] at hv'
      exact (Submodule.mem_bot R).mpr (Subtype.ext ((Submodule.mem_bot R).mp hv')))
    (by
      apply Subrepresentation.toSubmodule_injective
      apply le_antisymm le_top
      intro v _
      change (v : B) ∈ s.subrepresentation (Fin.last n)
      rw [s.subrepresentation_last]
      exact Submodule.mem_top)

@[simp]
theorem mem_intersect_subrepresentation (s : ObjectRepFiltration B n)
    (S : Subrepresentation B.ρ) (i : Fin (n + 1)) (v : S) :
    v ∈ (s.intersect S).subrepresentation i ↔ (v : B) ∈ s.subrepresentation i := Iff.rfl

/-- The inclusion of an intersected step into the original step. -/
def intersectStepMap (s : ObjectRepFiltration B n) (S : Subrepresentation B.ρ)
    (i : Fin (n + 1)) :
    ((s.intersect S).subrepresentation i).toRepresentation.IntertwiningMap
      (s.subrepresentation i).toRepresentation where
  toLinearMap := {
    toFun v := ⟨v.val.val, v.property⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  isIntertwining' _ := rfl

/-- A surjection from the upper step whose kernel is exactly the lower step
identifies the actual successive quotient with its target. -/
def gradedEquivOfSurjection (s : ObjectRepFiltration B n) (i : Fin n)
    {W : Type uW} [AddCommGroup W] [Module R W] {σ : Representation R G W}
    (f : (s.subrepresentation i.succ).toRepresentation.IntertwiningMap σ)
    (hf : Function.Surjective f)
    (hker : ∀ v : s.subrepresentation i.succ,
      f v = 0 ↔ (v : B) ∈ s.subrepresentation i.castSucc) :
    (s.gradedRepresentation i).ρ.Equiv σ := by
  let N := (s.subrepresentation i.castSucc).toSubmodule.comap
    (s.subrepresentation i.succ).toSubmodule.subtype
  let L := N.liftQ f.toLinearMap (fun v hv => (hker v).mpr hv)
  let F : (s.gradedRepresentation i).ρ.IntertwiningMap σ := {
    toLinearMap := L
    isIntertwining' := by
      intro g
      ext v
      obtain ⟨v, rfl⟩ := s.gradedProjection_surjective i v
      exact Representation.IntertwiningMap.isIntertwining _ _ f g v }
  refine F.ofBijective ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨v, rfl⟩ := s.gradedProjection_surjective i x
    obtain ⟨w, rfl⟩ := s.gradedProjection_surjective i y
    change f v = f w at hxy
    apply (Submodule.Quotient.eq N).mpr
    exact (hker (v - w)).mp (by rw [map_sub, hxy, sub_self])
  · intro w
    obtain ⟨v, rfl⟩ := hf w
    exact ⟨(s.gradedProjection i).hom v, rfl⟩

end Algebra

section Weights

variable {R : Type uR} [Field R] {G : Type uG} [Group G]
  [TopologicalSpace G] [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]
  {A : Type uA} [Group A] {B : Rep.{uV} R G} {n : ℕ}
  (s : ObjectRepFiltration B n) (ι : A →* G)
  (hι : ∀ a : A, ι a ∈ Subgroup.center G) (P : (A →* Rˣ) → Prop)

/-- The literal intersection filtration of the selected part of the ambient
representation. It has the same number and order of steps as the original. -/
def selectedFiltration :
    ObjectRepFiltration (Rep.of (selectedWeightPart B.ρ ι hι P).toRepresentation) n :=
  s.intersect (selectedWeightPart B.ρ ι hι P)

/-- The actual projection from a selected upper step to the selected part of
its original graded quotient. -/
def selectedUpperProjection (hB : IsSmooth B.ρ) (i : Fin n)
    (hspan : (⨆ χ : A →* Rˣ,
      (generalizedWeightSpace (s.subrepresentation i.succ).toRepresentation
        ι χ hι).toSubmodule) = ⊤) :
    ((s.selectedFiltration ι hι P).subrepresentation i.succ).toRepresentation.IntertwiningMap
      (selectedWeightPart (s.gradedRepresentation i).ρ ι hι P).toRepresentation := by
  let j : (s.subrepresentation i.succ).toRepresentation.IntertwiningMap B.ρ := {
    toLinearMap := (s.subrepresentation i.succ).toSubmodule.subtype
    isIntertwining' _ := rfl }
  let f := s.intersectStepMap (selectedWeightPart B.ρ ι hι P) i.succ
  have hv (v : (s.selectedFiltration ι hι P).subrepresentation i.succ) :
      f v ∈ selectedWeightPart (s.subrepresentation i.succ).toRepresentation ι hι P :=
    (mem_selectedWeightPart_iff_of_injective ι hι P hB hspan j
      Subtype.val_injective (f v)).mp v.val.property
  exact {
    toFun v := ⟨(s.gradedProjection i).hom (f v),
      map_mem_selectedWeightPart ι hι P (s.gradedProjection i).hom (hv v)⟩
    map_add' _ _ := Subtype.ext (map_add ((s.gradedProjection i).hom.comp f) _ _)
    map_smul' _ _ := Subtype.ext (map_smul ((s.gradedProjection i).hom.comp f) _ _)
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact Representation.IntertwiningMap.isIntertwining _ _
        ((s.gradedProjection i).hom.comp f) g v }

/-- Selected vectors in the original quotient lift to the selected upper step.
Only the upper step needs spanning; the ambient representation needs smoothness. -/
theorem selectedUpperProjection_surjective (hB : IsSmooth B.ρ) (i : Fin n)
    (hspan : (⨆ χ : A →* Rˣ,
      (generalizedWeightSpace (s.subrepresentation i.succ).toRepresentation
        ι χ hι).toSubmodule) = ⊤) :
    Function.Surjective (s.selectedUpperProjection ι hι P hB i hspan) := by
  let j : (s.subrepresentation i.succ).toRepresentation.IntertwiningMap B.ρ := {
    toLinearMap := (s.subrepresentation i.succ).toSubmodule.subtype
    isIntertwining' _ := rfl }
  have hu : IsSmooth (s.subrepresentation i.succ).toRepresentation :=
    isSmooth_of_injective j Subtype.val_injective hB
  have hq : IsSmooth (s.gradedRepresentation i).ρ :=
    isSmooth_of_surjective (s.gradedProjection i).hom (s.gradedProjection_surjective i) hu
  intro w
  obtain ⟨v, hv⟩ := selectedWeightMap_surjective ι hι P hq hspan
    (s.gradedProjection i).hom (s.gradedProjection_surjective i) w
  refine ⟨⟨⟨v.val.val, map_mem_selectedWeightPart ι hι P j v.property⟩,
    v.val.property⟩, ?_⟩
  exact Subtype.ext (congrArg Subtype.val hv)

/-- Taking selected weights commutes with each actual successive quotient. -/
def selectedGradedEquiv (hB : IsSmooth B.ρ) (i : Fin n)
    (hspan : (⨆ χ : A →* Rˣ,
      (generalizedWeightSpace (s.subrepresentation i.succ).toRepresentation
        ι χ hι).toSubmodule) = ⊤) :
    ((s.selectedFiltration ι hι P).gradedRepresentation i).ρ.Equiv
      (selectedWeightPart (s.gradedRepresentation i).ρ ι hι P).toRepresentation := by
  apply gradedEquivOfSurjection (s.selectedFiltration ι hι P) i
    (s.selectedUpperProjection ι hι P hB i hspan)
    (s.selectedUpperProjection_surjective ι hι P hB i hspan)
  intro v
  constructor
  · intro hv
    have h0 := congrArg Subtype.val hv
    exact (Submodule.Quotient.mk_eq_zero
      ((s.subrepresentation i.castSucc).toSubmodule.comap
        (s.subrepresentation i.succ).toSubmodule.subtype)).mp h0
  · intro hv
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero
      ((s.subrepresentation i.castSucc).toSubmodule.comap
        (s.subrepresentation i.succ).toSubmodule.subtype)).mpr hv

@[simp]
theorem selectedGradedEquiv_projection (hB : IsSmooth B.ρ) (i : Fin n)
    (hspan : (⨆ χ : A →* Rˣ,
      (generalizedWeightSpace (s.subrepresentation i.succ).toRepresentation
        ι χ hι).toSubmodule) = ⊤)
    (v : (s.selectedFiltration ι hι P).subrepresentation i.succ) :
    s.selectedGradedEquiv ι hι P hB i hspan
        (((s.selectedFiltration ι hι P).gradedProjection i).hom v) =
      s.selectedUpperProjection ι hι P hB i hspan v := rfl

/-- Ambient admissibility over an algebraically closed field supplies the
spanning needed for every selected graded comparison. -/
def selectedGradedEquivOfAdmissible [IsAlgClosed R] (hB : IsAdmissible B.ρ) (i : Fin n) :
    ((s.selectedFiltration ι hι P).gradedRepresentation i).ρ.Equiv
      (selectedWeightPart (s.gradedRepresentation i).ρ ι hι P).toRepresentation := by
  have hu : IsAdmissible (s.subrepresentation i.succ).toRepresentation :=
    isAdmissible_of_injective
      { toLinearMap := (s.subrepresentation i.succ).toSubmodule.subtype
        isIntertwining' _ := rfl }
      Subtype.val_injective hB
  exact s.selectedGradedEquiv ι hι P hB.1 i
    (generalizedWeightSpace_iSup_eq_top _ ι hι hu.1
      (CentralDecomposition.admissible_centerFinite _ hu))

end Weights

end Langlands.ObjectRepFiltration
