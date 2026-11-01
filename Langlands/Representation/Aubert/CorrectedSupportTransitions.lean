import Langlands.Representation.Aubert.CorrectedSupportFiltration
import Langlands.Representation.Aubert.CutTransitionMaps

/-! Actual cut maps on corrected support images and their successive quotients. -/

noncomputable section

namespace Langlands.Aubert.Support

open GeneralLinear Geometric CategoryTheory

universe uF uV

section Cores

variable {n : ℕ} {B D : BlockShape n} (C : BlockShape n)

/-- Adding source cuts increases the corrected support for a fixed target. -/
theorem weylSupport_mono_source_cuts (h : B.cuts ⊆ D.cuts)
    (θ : Set (Equiv.Perm (Fin n))) :
    weylSupport B C θ ⊆ weylSupport D C θ :=
  twoSidedCore_antitone_subgroups _ _ le_rfl
    ((blockWeyl_le_iff_cuts_subset B D).mpr h) θ

/-- The same containment holds for the actual matrix support. -/
theorem bruhatSupport_mono_source_cuts (F : Type uF) [Field F]
    (h : B.cuts ⊆ D.cuts) (θ : Set (Equiv.Perm (Fin n))) :
    bruhatSupport F (weylSupport B C θ) ⊆ bruhatSupport F (weylSupport D C θ) :=
  bruhatSupport_mono F (weylSupport_mono_source_cuts C h θ)

end Cores

section Actual

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}

/-- The actual smooth induction--Jacquet object at a source shape. -/
abbrev cutTermObject
    (A : letI := T.topology
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier)) (B : BlockShape n) :
    letI := T.topology
    SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  (T.normalizedParabolicInductionFunctor B).obj ((T.normalizedJacquetFunctor B).obj A)

/-- Apply the fixed target Jacquet functor to an actual cut term. -/
abbrev cutJacquetObject
    (A : letI := T.topology
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier)) (B C : BlockShape n) :
    letI := T.topology
    SmoothRep.{0,uF,max uF uV} ℂ (C.Levi F.Carrier) :=
  letI := T.topology
  (T.normalizedJacquetFunctor C).obj (cutTermObject T A B)

variable (A : letI := T.topology
    SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier))
  {B D E : BlockShape n} (C : BlockShape n)

/-- The actual pointwise cut map preserves corrected induction support. -/
theorem cutMap_mem_correctedInductionSupport (h : B.cuts ⊆ D.cuts)
    (θ : Set (Equiv.Perm (Fin n))) :
    letI := T.topology
    ∀ (f : cutTermObject T A B),
      f ∈ (correctedInductionSupport T B C θ).obj
          ((T.normalizedJacquetFunctor B).obj A) →
      Transition.cutMap T A.representation h f ∈
        (correctedInductionSupport T D C θ).obj
          ((T.normalizedJacquetFunctor D).obj A) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  intro f hf
  apply (mem_correctedInductionSupport_iff T D C θ _ _).mpr
  intro g hg
  apply bruhatSupport_mono_source_cuts C F.Carrier h θ
  apply (mem_correctedInductionSupport_iff T B C θ _ _).mp hf g
  intro hz
  apply hg
  change Transition.quotient A.representation
    (unipotentSubgroup_le_of_cuts_subset h) (Induction.eval _ _ f g) = 0
  exact (congrArg (Transition.quotient A.representation
    (unipotentSubgroup_le_of_cuts_subset h)) hz).trans (map_zero _)

/-- The actual fixed-target Jacquet descent of the actual cut map. -/
def cutJacquetMap (h : B.cuts ⊆ D.cuts) :
    letI := T.topology
    (cutJacquetObject T A B C).representation.IntertwiningMap
      (cutJacquetObject T A D C).representation :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  T.normalizedJacquetMap C (Transition.cutMap T A.representation h)

@[simp]
theorem cutJacquetMap_mk (h : B.cuts ⊆ D.cuts) :
    letI := T.topology
    ∀ (f : cutTermObject T A B),
      cutJacquetMap T A C h (C.jacquetMk (cutTermObject T A B).representation f) =
        C.jacquetMk (cutTermObject T A D).representation
          (Transition.cutMap T A.representation h f) := by
  intros
  rfl

/-- The fixed-target Jacquet descent preserves the actual corrected support image. -/
theorem cutJacquetMap_mem_correctedJacquetSupport (h : B.cuts ⊆ D.cuts)
    (θ : Set (Equiv.Perm (Fin n))) :
    letI := T.topology
    ∀ (q : cutJacquetObject T A B C),
      q ∈ (correctedJacquetSupport T B C θ).obj
          ((T.normalizedJacquetFunctor B).obj A) →
      cutJacquetMap T A C h q ∈ (correctedJacquetSupport T D C θ).obj
          ((T.normalizedJacquetFunctor D).obj A) := by
  let := T.topology
  intro q hq
  obtain ⟨f, hf, rfl⟩ := hq
  exact ⟨Transition.cutMap T A.representation h f,
    cutMap_mem_correctedInductionSupport T A C h θ f hf, rfl⟩

/-- Restrict the actual descended cut map to its corrected support images. -/
def cutJacquetSupportMap (h : B.cuts ⊆ D.cuts)
    (θ : Set (Equiv.Perm (Fin n))) :
    letI := T.topology
    (correctedJacquetSupport T B C θ).representation
        ((T.normalizedJacquetFunctor B).obj A) ⟶
      (correctedJacquetSupport T D C θ).representation
        ((T.normalizedJacquetFunctor D).obj A) := by
  letI := T.topology
  exact Rep.ofHom
    { toLinearMap :=
        { toFun := fun q => ⟨cutJacquetMap T A C h q.1,
            cutJacquetMap_mem_correctedJacquetSupport T A C h θ q.1 q.property⟩
          map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
          map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
      isIntertwining' := by
        intro c
        ext q
        exact LinearMap.congr_fun ((cutJacquetMap T A C h).isIntertwining' c) q.1 }

/-- The actual quotient between two corrected fixed-target support images. -/
abbrev cutSupportQuotient (B : BlockShape n)
    (θ η : Set (Equiv.Perm (Fin n))) :
    letI := T.topology
    Rep.{max uF uV} ℂ (C.Levi F.Carrier) :=
  letI := T.topology
  (correctedJacquetSupport T B C θ).quotientObj (correctedJacquetSupport T B C η)
    ((T.normalizedJacquetFunctor B).obj A)

/-- Descend the actual cut map to the actual successive support quotients.
The denominator is the lower support pulled back to the upper support. -/
def cutSupportQuotientMap (h : B.cuts ⊆ D.cuts)
    (θ η : Set (Equiv.Perm (Fin n))) :
    letI := T.topology
    cutSupportQuotient T A C B θ η ⟶ cutSupportQuotient T A C D θ η := by
  letI := T.topology
  let S := correctedJacquetSupport T B C θ
  let U := correctedJacquetSupport T B C η
  let S' := correctedJacquetSupport T D C θ
  let U' := correctedJacquetSupport T D C η
  let X := (T.normalizedJacquetFunctor B).obj A
  let Y := (T.normalizedJacquetFunctor D).obj A
  exact Rep.ofHom
    { toLinearMap := Submodule.mapQ (S.lowerInUpper U X).toSubmodule
        (S'.lowerInUpper U' Y).toSubmodule (cutJacquetSupportMap T A C h η).hom.toLinearMap
        (fun q hq => cutJacquetMap_mem_correctedJacquetSupport T A C h θ q.1 hq)
      isIntertwining' := by
        intro c
        apply LinearMap.ext
        intro q
        obtain ⟨q, rfl⟩ := S.quotientProjection_surjective U X q
        change (S'.quotientProjection U' Y).hom
            ((cutJacquetSupportMap T A C h η).hom ((U.representation X).ρ c q)) =
          (S'.quotientProjection U' Y).hom
            ((U'.representation Y).ρ c ((cutJacquetSupportMap T A C h η).hom q))
        rw [Rep.hom_comm_apply (cutJacquetSupportMap T A C h η)] }

@[simp]
theorem cutSupportQuotientMap_projection (h : B.cuts ⊆ D.cuts)
    (θ η : Set (Equiv.Perm (Fin n))) :
    letI := T.topology
    ∀ q : (correctedJacquetSupport T B C η).representation
        ((T.normalizedJacquetFunctor B).obj A),
      (cutSupportQuotientMap T A C h θ η).hom
          (((correctedJacquetSupport T B C θ).quotientProjection
            (correctedJacquetSupport T B C η)
            ((T.normalizedJacquetFunctor B).obj A)).hom q) =
        ((correctedJacquetSupport T D C θ).quotientProjection
          (correctedJacquetSupport T D C η)
          ((T.normalizedJacquetFunctor D).obj A)).hom
            ((cutJacquetSupportMap T A C h η).hom q) := by
  intros
  rfl

end Actual
end Langlands.Aubert.Support
