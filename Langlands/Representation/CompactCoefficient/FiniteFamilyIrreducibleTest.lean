import Langlands.Representation.CompactCoefficient.SelectedConjugation

/-!
# The irreducible test for a finite-family ambient projector

A supplied finite family spans one restricted object. The associated natural
ambient projector acts as the identity on an ambient irreducible exactly when
there is a nonzero restricted intertwiner to that spanning object.
-/

noncomputable section

namespace Langlands.CompactCoefficientClass

universe uG uC uV uW uU uI

private theorem exists_nonzero_eval_of_not_mem_selectedAnnihilator
    {H : Type uG} [Group H] [TopologicalSpace H]
    (t : Finset (CompactCoefficientClass.{uG, uC} H))
    (B : SmoothRep.{0, uG, uW} ℂ H) (v : B)
    (hv : v ∉ selectedAnnihilatorSubrepresentation t B) :
    ∃ (c : t) (D : IrreducibleCompactCoefficientRep.{uG, uC} H),
      ofRep D = c.val ∧
      ∃ g : B.representation.IntertwiningMap D.obj.representation, g v ≠ 0 := by
  classical
  by_contra hn
  apply hv
  rw [selectedAnnihilatorSubrepresentation, Subrepresentation.mem_iInf]
  intro c
  apply (mem_annihilatorSubrepresentation_iff v).2
  intro D hD g
  by_contra hne
  exact hn ⟨c, D, hD, g, hne⟩

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal]
    {ι : Type uI} [Fintype ι]
    (E : ι → IrreducibleCompactCoefficientRep.{uG, uC} N)
    (A : SmoothRep.{0, uG, uV} ℂ G)
    (f : ∀ i, (E i).obj.representation.IntertwiningMap
      (SmoothRep.restrictSubgroup N A).representation)
    (hf : ∀ i, Function.Injective (f i))
    (hspan : (⨆ i, (f i).range.toSubmodule) = ⊤)
    (hA : ∀ c : classesOfFiniteFamily E,
      IsCompl (isotypicSubrepresentation c.val (SmoothRep.restrictSubgroup N A)).toSubmodule
        (annihilatorSubrepresentation c.val (SmoothRep.restrictSubgroup N A)).toSubmodule)

/-- The actual ambient intertwiner selected by a finite spanning restriction
family. Conjugation stability follows from the family, not an extra premise. -/
def finiteFamilyAmbientProjector
    (X : SmoothRep.{0, uG, uW} ℂ G)
    (hX : ∀ c : classesOfFiniteFamily E,
      IsCompl (isotypicSubrepresentation c.val (SmoothRep.restrictSubgroup N X)).toSubmodule
        (annihilatorSubrepresentation c.val (SmoothRep.restrictSubgroup N X)).toSubmodule) :
    X.representation.IntertwiningMap X.representation :=
  ambientSelectedProjector N (classesOfFiniteFamily E)
    (mem_classesOfFiniteFamily_conjugation_iff N E f hf hspan hA) hX

theorem finiteFamilyAmbientProjector_idempotent
    (X : SmoothRep.{0, uG, uW} ℂ G)
    (hX : ∀ c : classesOfFiniteFamily E,
      IsCompl (isotypicSubrepresentation c.val (SmoothRep.restrictSubgroup N X)).toSubmodule
        (annihilatorSubrepresentation c.val (SmoothRep.restrictSubgroup N X)).toSubmodule) :
    IsIdempotentElem
      (finiteFamilyAmbientProjector N E A f hf hspan hA X hX).toLinearMap :=
  ambientSelectedProjector_idempotent N (classesOfFiniteFamily E)
    (mem_classesOfFiniteFamily_conjugation_iff N E f hf hspan hA) hX

/-- Naturality holds for every ambient intertwiner, across carrier universes. -/
theorem finiteFamilyAmbientProjector_natural
    {X : SmoothRep.{0, uG, uW} ℂ G}
    (hX : ∀ c : classesOfFiniteFamily E,
      IsCompl (isotypicSubrepresentation c.val (SmoothRep.restrictSubgroup N X)).toSubmodule
        (annihilatorSubrepresentation c.val (SmoothRep.restrictSubgroup N X)).toSubmodule)
    {Y : SmoothRep.{0, uG, uU} ℂ G}
    (hY : ∀ c : classesOfFiniteFamily E,
      IsCompl (isotypicSubrepresentation c.val (SmoothRep.restrictSubgroup N Y)).toSubmodule
        (annihilatorSubrepresentation c.val (SmoothRep.restrictSubgroup N Y)).toSubmodule)
    (q : X.representation.IntertwiningMap Y.representation) (v : X) :
    finiteFamilyAmbientProjector N E A f hf hspan hA Y hY (q v) =
      q (finiteFamilyAmbientProjector N E A f hf hspan hA X hX v) :=
  ambientSelectedProjector_natural N (classesOfFiniteFamily E)
    (mem_classesOfFiniteFamily_conjugation_iff N E f hf hspan hA) hX hY q v

/-- The projector fixes the object spanned by the supplied family. -/
theorem finiteFamilyAmbientProjector_fixes_base (v : A) :
    finiteFamilyAmbientProjector N E A f hf hspan hA A hA v = v := by
  let p := finiteFamilyAmbientProjector N E A f hf hspan hA A hA
  have hr : p.range.toSubmodule =
      (selectedIsotypicSubrepresentation (classesOfFiniteFamily E)
        (SmoothRep.restrictSubgroup N A)).toSubmodule :=
    ambientSelectedProjector_range N (classesOfFiniteFamily E)
      (mem_classesOfFiniteFamily_conjugation_iff N E f hf hspan hA) hA
  have hv : v ∈ p.range.toSubmodule := by
    rw [hr, selectedIsotypic_eq_top_of_finiteFamily_span E f hspan]
    trivial
  obtain ⟨w, hw⟩ := hv
  change p.toLinearMap w = v at hw
  change p v = v
  rw [← hw]
  exact congrArg (fun q : A →ₗ[ℂ] A => q w)
    (finiteFamilyAmbientProjector_idempotent N E A f hf hspan hA A hA)

/-- On an ambient irreducible, identity action is equivalent to a nonzero
restricted intertwiner to the object spanned by the finite family. No
semisimplicity or finite-length hypothesis on the candidate restriction is
needed. -/
theorem finiteFamilyAmbientProjector_fixes_iff_restricted_hom
    (X : SmoothRep.{0, uG, uW} ℂ G) (hirr : X.IsIrreducible)
    (hX : ∀ c : classesOfFiniteFamily E,
      IsCompl (isotypicSubrepresentation c.val (SmoothRep.restrictSubgroup N X)).toSubmodule
        (annihilatorSubrepresentation c.val (SmoothRep.restrictSubgroup N X)).toSubmodule) :
    (∀ v, finiteFamilyAmbientProjector N E A f hf hspan hA X hX v = v) ↔
      ∃ q : (SmoothRep.restrictSubgroup N X).representation.IntertwiningMap
          (SmoothRep.restrictSubgroup N A).representation, q ≠ 0 := by
  classical
  let t := classesOfFiniteFamily E
  let p := finiteFamilyAmbientProjector N E A f hf hspan hA X hX
  let : Representation.IsIrreducible X.representation := hirr
  let : Nontrivial X :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) X.representation.asModule
  change (∀ v, p v = v) ↔ _
  constructor
  · intro hfix
    obtain ⟨v, hv⟩ := exists_ne (0 : X)
    have hvnot : v ∉ selectedAnnihilatorSubrepresentation t
        (SmoothRep.restrictSubgroup N X) := by
      intro hmem
      have hk : p.ker.toSubmodule =
          (selectedAnnihilatorSubrepresentation t
            (SmoothRep.restrictSubgroup N X)).toSubmodule :=
        ambientSelectedProjector_ker N t
          (mem_classesOfFiniteFamily_conjugation_iff N E f hf hspan hA) hX
      have hker : v ∈ p.ker.toSubmodule := by
        rw [hk]
        exact hmem
      change p v = 0 at hker
      exact hv ((hfix v).symm.trans hker)
    obtain ⟨c, D, hD, g, hg⟩ :
        ∃ (c : t) (D : IrreducibleCompactCoefficientRep.{uG, uC} N),
          ofRep D = c.val ∧
          ∃ g : (SmoothRep.restrictSubgroup N X).representation.IntertwiningMap
              D.obj.representation, g v ≠ 0 :=
      exists_nonzero_eval_of_not_mem_selectedAnnihilator t
        (SmoothRep.restrictSubgroup N X) v hvnot
    obtain ⟨i, hi⟩ := (mem_classesOfFiniteFamily E c.val).1 c.property
    obtain ⟨a⟩ := (ofRep_eq_iff D (E i)).1 (hD.trans hi.symm)
    let e := SmoothRep.equivOfIso ((irreducibleCompactCoefficientProperty N).ι.mapIso a)
    let q := (f i).comp (e.toIntertwiningMap.comp g)
    refine ⟨q, fun hq => ?_⟩
    have hqv : f i (e (g v)) = 0 :=
      congrArg (fun r : (SmoothRep.restrictSubgroup N X).representation.IntertwiningMap
        (SmoothRep.restrictSubgroup N A).representation => r v) hq
    have hegv : e (g v) = 0 := hf i (hqv.trans (map_zero (f i)).symm)
    exact hg (e.injective (hegv.trans (map_zero e).symm))
  · rintro ⟨q, hq⟩
    have hp : p ≠ 0 := by
      intro hp
      apply hq
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro v
      have hbase : selectedProjectorOfIsCompl t hA (q v) = q v :=
        finiteFamilyAmbientProjector_fixes_base N E A f hf hspan hA (q v)
      have hnat := selectedProjectorOfIsCompl_natural t hX hA q v
      have hzero : q (p v) = 0 := by
        rw [hp]
        exact map_zero q
      exact hbase.symm.trans (hnat.trans hzero)
    have hinj : Function.Injective p :=
      (Representation.IsIrreducible.injective_or_eq_zero p).resolve_right hp
    intro v
    apply hinj
    exact congrArg (fun r : X →ₗ[ℂ] X => r v)
      (finiteFamilyAmbientProjector_idempotent N E A f hf hspan hA X hX)

end Langlands.CompactCoefficientClass
