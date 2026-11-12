import Langlands.Representation.CompactCoefficient.CompactIsotypicComplementStatement
import Langlands.Representation.CompactCoefficient.AdmissibleComplement
import Langlands.Representation.Hecke.CommonInvarianceProof
import Langlands.Representation.CompactCoefficient.SelectedBlock
import Mathlib.Order.CompactlyGenerated.Basic

/-! # The compact-isotypic decomposition (Renard IV.1.4–IV.1.5) -/

noncomputable section

open CategoryTheory MeasureTheory

namespace Langlands.Renard.CompactRepresentation

private theorem independent_atoms_subset
    {α : Type*} [CompleteLattice α] [IsModularLattice α] [IsCompactlyGenerated α]
    (A : Set α) (hA : ∀ a ∈ A, IsAtom a) :
    ∃ s : Set α, s ⊆ A ∧ sSupIndep s ∧ sSup s = sSup A := by
  classical
  have hz := zorn_subset (S := {s : Set α | s ⊆ A ∧ sSupIndep s})
    (fun c hc hchain =>
      ⟨⋃₀ c, ⟨fun a ⟨s, hs, ha⟩ => (hc hs).1 ha,
        iSupIndep_sUnion_of_directed hchain.directedOn (fun s hs => (hc hs).2)⟩,
        fun s hs => Set.subset_sUnion_of_mem hs⟩)
  simp_rw [maximal_subset_iff] at hz
  obtain ⟨s, ⟨hsA, hind⟩, hmax⟩ := hz
  refine ⟨s, hsA, hind, le_antisymm (sSup_le_sSup hsA) (sSup_le ?_)⟩
  intro a ha
  by_contra hle
  have hd : Disjoint a (sSup s) := by
    rw [disjoint_iff]
    exact ((hA a ha).le_iff.mp inf_le_left).resolve_right
      (fun h => hle (inf_eq_left.mp h))
  have hins : sSupIndep (insert a s) := by
    intro b hb
    by_cases hba : b = a
    · subst b
      rw [Set.insert_sdiff_of_mem s (Set.mem_singleton a)]
      exact hd.mono_right (sSup_le_sSup Set.sdiff_subset)
    · have hbs : b ∈ s := (Set.mem_insert_iff.mp hb).resolve_left hba
      rw [Set.insert_sdiff_of_notMem s (show a ∉ ({b} : Set α) by simpa using Ne.symm hba),
        sSup_insert]
      simpa only [sup_comm] using
        (hind hbs).disjoint_sup_right_of_disjoint_sup_left
          (hd.mono_right (sup_le (le_sSup hbs) (sSup_le_sSup Set.sdiff_subset))).symm
  have heq := hmax ⟨Set.insert_subset_iff.mpr ⟨ha, hsA⟩, hins⟩ (Set.subset_insert a s)
  exact hle (le_sSup (heq ▸ Set.mem_insert a s))

private theorem independent_isotypic_ranges
    {k G W V : Type*} [Field k] [Monoid G]
    [AddCommGroup W] [Module k W] [AddCommGroup V] [Module k V]
    (τ : Representation k G W) (ρ : Representation k G V) (hirr : τ.IsIrreducible) :
    ∃ s : Set (τ.IntertwiningMap ρ),
      (∀ f ∈ s, Function.Injective f) ∧
      iSupIndep (fun f : s => (f : τ.IntertwiningMap ρ).range) ∧
      ⨆ f : s, (f : τ.IntertwiningMap ρ).range =
        ⨆ f : τ.IntertwiningMap ρ, f.range := by
  classical
  have := hirr
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  let F (f : τ.IntertwiningMap ρ) := e f.range
  let A : Set (Submodule (MonoidAlgebra k G) ρ.asModule) :=
    {N | ∃ f : τ.IntertwiningMap ρ, f ≠ 0 ∧ F f = N}
  have hA : ∀ N ∈ A, IsAtom N := by
    rintro N ⟨f, hfnz, rfl⟩
    let fm := Representation.IntertwiningMap.equivLinearMapAsModule τ ρ f
    have hinj : Function.Injective fm :=
      (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hfnz
    have hs : IsSimpleModule (MonoidAlgebra k G) (LinearMap.range fm) :=
      (LinearEquiv.ofInjective fm hinj).isSimpleModule_iff.mp inferInstance
    exact isSimpleModule_iff_isAtom.mp hs
  obtain ⟨s, hsA, hind, hsup⟩ := independent_atoms_subset A hA
  choose f hfne hf using fun i : s => hsA i.property
  let t : Set (τ.IntertwiningMap ρ) := Set.range f
  have hindf : iSupIndep (fun i : s => (f i).range) := by
    apply (iSupIndep_map_orderIso_iff e).mp
    change iSupIndep (fun i : s => F (f i))
    simpa only [hf] using (sSupIndep_iff s).mp hind
  have hst : sSup s = ⨆ i : t, F i.val := by
    rw [sSup_eq_iSup']
    apply le_antisymm
    · exact iSup_le fun i => le_iSup_of_le ⟨f i, ⟨i, rfl⟩⟩ (hf i).ge
    · refine iSup_le fun i => ?_
      obtain ⟨j, hj⟩ := i.property
      rw [← hj, hf j]
      exact le_iSup (fun j : s => j.val) j
  refine ⟨t, ?_, ?_, le_antisymm ?_ ?_⟩
  · rintro g ⟨i, rfl⟩
    exact (Representation.IsIrreducible.injective_or_eq_zero (f i)).resolve_right (hfne i)
  · exact hindf.comp' (f := fun i : s => (⟨f i, ⟨i, rfl⟩⟩ : t))
      (by rintro ⟨g, i, rfl⟩; exact ⟨i, rfl⟩)
  · exact iSup_le fun i => le_iSup (fun f : τ.IntertwiningMap ρ => f.range) i.val
  · refine iSup_le fun g => ?_
    by_cases hg : g = 0
    · subst g
      rintro _ ⟨w, rfl⟩
      exact Submodule.zero_mem _
    · apply e.le_iff_le.mp
      rw [e.map_iSup, ← hst, hsup]
      exact le_sSup ⟨g, hg, rfl⟩

universe u v

/-- Renard IV.1.4 and IV.1.5: the isotypic direct sum has a unique invariant
complement, and that complement has no subquotient isomorphic to the compact type. -/
theorem compactIsotypicComplement : CompactIsotypicComplementStatement.{u, v} := by
  classical
  intro G _ _ _ _ _ _ _ _ _ μ _ _ _ τ hirr hc V
  have hcof : ∀ K : OpenSubgroup G,
      ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hLK, hL, -⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ K
    exact ⟨L, hL, hLK⟩
  let D : IrreducibleCompactCoefficientRep.{u, v} G := ⟨τ, hirr, hc⟩
  let c := CompactCoefficientClass.ofRep D
  have hsplit (A : SmoothRep.{0, u, v} ℂ G) :
      IsCompl (CompactCoefficientClass.isotypicSubrepresentation c A).toSubmodule
        (CompactCoefficientClass.annihilatorSubrepresentation c A).toSubmodule :=
    CompactSplitting.isCompl_isotypicSubrepresentation_annihilatorSubrepresentation μ hcof c A
  let p (A : SmoothRep.{0, u, v} ℂ G) :=
    CompactCoefficientClass.isotypicProjectorOfIsCompl c (hsplit A)
  have hrange (A : SmoothRep.{0, u, v} ℂ G) :
      (p A).range = ⨆ f : τ.representation.IntertwiningMap A.representation, f.range := by
    exact (CompactCoefficientClass.isotypicProjectorOfIsCompl_range c (hsplit A)).trans
      (CompactCoefficientClass.isotypicSubrepresentation_eq_iSup_range D rfl)
  have hker (A : SmoothRep.{0, u, v} ℂ G) :
      (p A).ker = CompactCoefficientClass.annihilatorSubrepresentation c A :=
    CompactCoefficientClass.isotypicProjectorOfIsCompl_ker c (hsplit A)
  have hnat (A B : SmoothRep.{0, u, v} ℂ G)
      (f : A.representation.IntertwiningMap B.representation) (x : A) :
      f (p A x) = p B (f x) :=
    CompactCoefficientClass.isotypicProjectorOfIsCompl_natural c (hsplit A) (hsplit B) f x
  let I : Subrepresentation V.representation :=
    ⨆ f : τ.representation.IntertwiningMap V.representation, f.range
  let K : Subrepresentation V.representation := (p V).ker
  have hIV : (p V).range = I := hrange V
  have hIK : IsCompl I.toSubmodule K.toSubmodule := by
    rw [← hIV]
    exact LinearMap.IsIdempotentElem.isCompl
      (CompactCoefficientClass.isotypicProjectorOfIsCompl_idempotent c (hsplit V))
  have hIKrep : IsCompl I K :=
    IsCompl.of_eq
      (Subrepresentation.toSubmodule_injective hIK.inf_eq_bot)
      (Subrepresentation.toSubmodule_injective hIK.sup_eq_top)
  have huniq (S : Subrepresentation V.representation) (hS : IsCompl I S) : S = K := by
    have hle : S.toSubmodule ≤ K.toSubmodule := by
      intro x hx
      let A := SmoothRep.subrepresentation V S
      let j := SmoothRep.hom (SmoothRep.subtype V S)
      have hpS : p V x ∈ S := by
        have hn := hnat A V j ⟨x, hx⟩
        change Subtype.val (p A ⟨x, hx⟩) = p V x at hn
        rw [← hn]
        exact (p A ⟨x, hx⟩).property
      have hpI : p V x ∈ I := by
        rw [← hIV]
        exact ⟨x, rfl⟩
      have hz : p V x ∈ I ⊓ S := ⟨hpI, hpS⟩
      rw [hS.inf_eq_bot] at hz
      exact hz
    have hSmod : IsCompl I.toSubmodule S.toSubmodule :=
      IsCompl.of_eq (congrArg Subrepresentation.toSubmodule hS.inf_eq_bot)
        (congrArg Subrepresentation.toSubmodule hS.sup_eq_top)
    apply Subrepresentation.toSubmodule_injective
    apply eq_of_le_of_inf_le_of_sup_le (z := I.toSubmodule) hle
    · rw [hIK.symm.inf_eq_bot]
      exact bot_le
    · rw [hSmod.symm.sup_eq_top]
      exact le_top
  have hno : ¬ SmoothRep.IsSubquotient τ (SmoothRep.subrepresentation V K) := by
    apply CompactCoefficientClass.not_isSubquotient_of_range_le_selectedAnnihilator
      {c} (fun A d => by
        have hd : d.val = c := Finset.mem_singleton.mp d.property
        rw [hd]
        exact hsplit A) D (Finset.mem_singleton.mpr rfl)
      (SmoothRep.hom (SmoothRep.subtype V K)) (SmoothRep.subtype_injective V K)
    rintro _ ⟨x, rfl⟩
    have hx : x.val ∈ CompactCoefficientClass.annihilatorSubrepresentation c V := by
      rw [← hker V]
      exact x.property
    change x.val ∈ CompactCoefficientClass.selectedAnnihilatorSubrepresentation {c} V
    simpa [CompactCoefficientClass.selectedAnnihilatorSubrepresentation] using hx
  refine ⟨independent_isotypic_ranges τ.representation V.representation hirr,
    ⟨K, hIKrep, huniq⟩, ?_⟩
  intro S hS B hB
  rw [huniq S hS] at hB
  refine ⟨fun e => ?_⟩
  obtain ⟨S', T, ⟨e'⟩⟩ := hB
  exact hno ⟨S', T, ⟨e.symm ≪≫ e'⟩⟩

end Langlands.Renard.CompactRepresentation
