import Langlands.Algebra.NonUnitalModuleCompletionSubmoduleStatements

/-!
# Proof of the completed submodule inclusion and the three ranges of I.1.5.3

Renard 2026, printed p.11/PDF17. Every description is identified with the set
of ambient families all of whose coordinates lie in the original submodule.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

open Set Filter NonUnitalModuleLeftLimit
open scoped Topology Uniformity

universe uA uM

section

variable {A : Type uA} [NonUnitalRing A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]

/-- The completed subtype map hits exactly the families with every coordinate in `S`. -/
theorem nonUnitalModuleCompletionSubmodule_range_mapAddHom (S : NonUnitalSubmodule A M) :
    range (mapAddHom S.subtype) =
      {x : NonUnitalModuleLeftLimit A M | ∀ e : Idempotent A, x.val e ∈ S} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ e
    exact (y.val e).property
  · intro hx
    refine ⟨⟨fun e => ⟨x.val e, hx e⟩, ?_⟩, rfl⟩
    constructor
    · intro e
      exact Subtype.ext (x.property.1 e)
    · intro e f hef
      exact Subtype.ext (x.property.2 e f hef)

/-- The completed subtype map is injective: coordinates are compared in `M`. -/
theorem nonUnitalModuleCompletionSubmodule_mapAddHom_injective (S : NonUnitalSubmodule A M) :
    Function.Injective (mapAddHom S.subtype) := by
  intro x y h
  apply Subtype.ext
  funext e
  exact Subtype.ext (congrArg (fun z : NonUnitalModuleLeftLimit A M => z.val e) h)

/-- The ambient coordinate uniformity pulls back to the submodule coordinate uniformity. -/
theorem nonUnitalModuleCompletionSubmodule_comap_uniformSpace (S : NonUnitalSubmodule A M) :
    UniformSpace.comap (mapAddHom S.subtype) (uniformSpace A M) = uniformSpace A S := by
  apply UniformSpace.ext
  rw [uniformity_comap, uniformity_eq, uniformity_eq, Filter.comap_iInf]
  refine iInf_congr fun e => ?_
  rw [comap_principal]
  congr 1
  ext p
  exact Subtype.ext_iff.symm

/-- The completed subtype map is a uniform embedding for the coordinate uniformities. -/
theorem nonUnitalModuleCompletionSubmodule_isUniformEmbedding (S : NonUnitalSubmodule A M) :
    @IsUniformEmbedding (NonUnitalModuleLeftLimit A S) (NonUnitalModuleLeftLimit A M)
      (uniformSpace A S) (uniformSpace A M) (mapAddHom S.subtype) := by
  let := uniformSpace A S
  let := uniformSpace A M
  exact ⟨isUniformInducing_iff_uniformSpace.mpr
      (nonUnitalModuleCompletionSubmodule_comap_uniformSpace S),
    nonUnitalModuleCompletionSubmodule_mapAddHom_injective S⟩

/-- Closure in the coordinate topology: every single coordinate is approximated exactly. -/
theorem nonUnitalModuleLeftLimit_mem_closure_iff (hA : IsIdempotented A)
    (T : Set (NonUnitalModuleLeftLimit A M)) (x : NonUnitalModuleLeftLimit A M) :
    x ∈ @closure _ (uniformSpace A M).toTopologicalSpace T ↔
      ∀ e : Idempotent A, ∃ y ∈ T, y.val e = x.val e := by
  let := uniformSpace A M
  rw [mem_closure_iff_nhds_basis (nhds_hasBasis hA x)]
  simp only [forall_const, mem_ofPred_eq]

/-- The closure of the canonical image of `S` is the set of families with coordinates in `S`. -/
theorem nonUnitalModuleCompletionSubmodule_closure_canonical (hA : IsIdempotented A)
    (S : NonUnitalSubmodule A M) :
    @closure _ (uniformSpace A M).toTopologicalSpace
        (canonical (A := A) (M := M) '' (S : Set M)) =
      {x : NonUnitalModuleLeftLimit A M | ∀ e : Idempotent A, x.val e ∈ S} := by
  ext x
  rw [nonUnitalModuleLeftLimit_mem_closure_iff hA]
  constructor
  · intro h e
    obtain ⟨_, ⟨m, hm, rfl⟩, he⟩ := h e
    rw [← he]
    exact S.smul_mem' (e : A) hm
  · intro hx e
    exact ⟨canonical (x.val e), ⟨x.val e, hx e, rfl⟩, x.property.1 e⟩

/-- The range of the completed subtype map is closed, being a closure. -/
theorem nonUnitalModuleCompletionSubmodule_isClosed_range (hA : IsIdempotented A)
    (S : NonUnitalSubmodule A M) :
    @IsClosed _ (uniformSpace A M).toTopologicalSpace (range (mapAddHom S.subtype)) := by
  rw [nonUnitalModuleCompletionSubmodule_range_mapAddHom,
    ← nonUnitalModuleCompletionSubmodule_closure_canonical hA S]
  exact @isClosed_closure _ (uniformSpace A M).toTopologicalSpace _

/-- A coordinate lies in `S` exactly when it is `e` acting on a vector of `S`. -/
theorem nonUnitalModuleCompletionSubmodule_coordinate_eq_exists (S : NonUnitalSubmodule A M) :
    {x : NonUnitalModuleLeftLimit A M | ∀ e : Idempotent A, x.val e ∈ S} =
      {x : NonUnitalModuleLeftLimit A M |
        ∀ e : Idempotent A, ∃ n : M, n ∈ S ∧ (e : A) • n = x.val e} := by
  ext x
  constructor
  · intro hx e
    exact ⟨x.val e, hx e, x.property.1 e⟩
  · intro hx e
    obtain ⟨n, hn, he⟩ := hx e
    rw [← he]
    exact S.smul_mem' (e : A) hn

/-- Coordinates lie in `S` exactly when every scalar translate is a canonical vector of `S`. -/
theorem nonUnitalModuleCompletionSubmodule_coordinate_eq_smul (hA : IsIdempotented A)
    (S : NonUnitalSubmodule A M) :
    {x : NonUnitalModuleLeftLimit A M | ∀ e : Idempotent A, x.val e ∈ S} =
      {x : NonUnitalModuleLeftLimit A M |
        ∀ a : A, scalarAction hA a x ∈ canonical (A := A) (M := M) '' (S : Set M)} := by
  ext x
  constructor
  · intro hx a
    classical
    obtain ⟨f, hf⟩ := (IsIdempotented.iff_two_sided_local_units.mp hA) {a}
    have haf : a * (f : A) = a := (hf a (by simp)).2
    refine ⟨a • x.val f, S.smul_mem' a (hx f), ?_⟩
    apply Subtype.ext
    funext e
    rw [scalarAction_val hA a x e f (by rw [mul_assoc, haf])]
    exact (mul_smul (e : A) a (x.val f)).symm
  · intro hx e
    obtain ⟨n, hn, hne⟩ := hx (e : A)
    rw [idempotent_scalarAction hA e x] at hne
    have h : (e : A) • n = (e : A) • x.val e :=
      congrArg (fun z : NonUnitalModuleLeftLimit A M => z.val e) hne
    rw [x.property.1 e] at h
    rw [← h]
    exact S.smul_mem' (e : A) hn

/-- The inclusion package for the actual completed subtype intertwiner. -/
theorem nonUnitalModuleCompletionSubmoduleInclusion_proof (hA : IsIdempotented A)
    (S : NonUnitalSubmodule A M) : NonUnitalModuleCompletionSubmoduleInclusion hA M S := by
  delta NonUnitalModuleCompletionSubmoduleInclusion
  intro _ _ _ _ _ _
  exact ⟨rfl, nonUnitalModuleCompletionSubmodule_mapAddHom_injective S,
    nonUnitalModuleCompletionSubmodule_isUniformEmbedding S,
    nonUnitalModuleCompletionSubmodule_isClosed_range hA S⟩

/-- The three range descriptions of (I.1.5.3) for the actual completed subtype intertwiner. -/
theorem nonUnitalModuleCompletionSubmoduleRange_proof (hA : IsIdempotented A)
    (S : NonUnitalSubmodule A M) : NonUnitalModuleCompletionSubmoduleRange hA M S := by
  delta NonUnitalModuleCompletionSubmoduleRange
  intro _ _ _ _ _ _
  exact ⟨(nonUnitalModuleCompletionSubmodule_range_mapAddHom S).trans
      (nonUnitalModuleCompletionSubmodule_closure_canonical hA S).symm,
    (nonUnitalModuleCompletionSubmodule_range_mapAddHom S).trans
      (nonUnitalModuleCompletionSubmodule_coordinate_eq_exists S),
    (nonUnitalModuleCompletionSubmodule_range_mapAddHom S).trans
      (nonUnitalModuleCompletionSubmodule_coordinate_eq_smul hA S)⟩

end

/-- The exact closed target; the ambient nondegeneracy premise is not needed by the argument. -/
theorem nonUnitalModuleCompletionSubmoduleTheorem_proof :
    NonUnitalModuleCompletionSubmoduleTheorem.{uA, uM} := by
  intro A _ hA M _ _ _ S
  exact ⟨nonUnitalModuleCompletionSubmoduleInclusion_proof hA S,
    nonUnitalModuleCompletionSubmoduleRange_proof hA S⟩

/-! Complete unapplied proof interfaces at independent scalar and vector universes. -/

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (S : NonUnitalSubmodule A M) →
      NonUnitalModuleCompletionSubmoduleInclusion hA M S :=
  @nonUnitalModuleCompletionSubmoduleInclusion_proof.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (S : NonUnitalSubmodule A M) →
      NonUnitalModuleCompletionSubmoduleRange hA M S :=
  @nonUnitalModuleCompletionSubmoduleRange_proof.{uA, uM}

example : NonUnitalModuleCompletionSubmoduleTheorem.{uA, uM} :=
  nonUnitalModuleCompletionSubmoduleTheorem_proof.{uA, uM}

example : NonUnitalModuleCompletionSubmoduleTheorem.{0, 1} :=
  nonUnitalModuleCompletionSubmoduleTheorem_proof.{0, 1}

example : NonUnitalModuleCompletionSubmoduleTheorem.{1, 0} :=
  nonUnitalModuleCompletionSubmoduleTheorem_proof.{1, 0}

end Langlands.Algebra
