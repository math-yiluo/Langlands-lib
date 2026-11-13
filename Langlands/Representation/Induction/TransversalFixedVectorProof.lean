import Langlands.Representation.Induction.TransversalConjugationStatements

/-! # Fixed vectors over an arbitrary double-coset transversal (Renard III.2.2) -/

noncomputable section

open Classical

namespace Langlands.Induction

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V]

variable (P : Subgroup G) (σ : Representation R P V) (K : OpenSubgroup G) (Ω : Set G)

/-- Evaluation at an arbitrary set of representatives, without a finiteness restriction. -/
private def transversalEvaluation :
    fixedVectors (smoothInduced P σ) K.toSubgroup →ₗ[R]
      ((ω : Ω) → fixedVectors σ (conjOpenSubgroup P K ω).toSubgroup) where
  toFun f ω := ⟨eval P σ f.val ω, eval_mem_fixedVectors P σ K ω f.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem transversalEvaluation_injective
    (hcover : ∀ x : G, ∃ ω ∈ Ω, ∃ p ∈ P, ∃ k ∈ K, x = p * ω * k) :
    Function.Injective (transversalEvaluation P σ K Ω) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf => ?_
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  obtain ⟨ω, hω, p, hp, k, hk, rfl⟩ := hcover x
  have hz : eval P σ f.val ω = 0 := congrArg Subtype.val (congrFun hf ⟨ω, hω⟩)
  change eval P σ f.val (p * ω * k) = 0
  rw [eval_mul_of_mem_fixedVectors P σ K.toSubgroup f.property ⟨k, hk⟩,
    eval_covariant P σ f.val ⟨p, hp⟩, hz, map_zero]

omit [CommRing R] [AddCommGroup V] [Module R V] [IsTopologicalGroup G] in
/-- A transversal indexes the entire double-coset quotient, including infinite quotients. -/
private def transversalQuotientEquiv
    (hcover : ∀ x : G, ∃ ω ∈ Ω, ∃ p ∈ P, ∃ k ∈ K, x = p * ω * k)
    (hdistinct : Function.Injective (fun ω : Ω => DoubleCoset.mk P K.toSubgroup (ω : G))) :
    Ω ≃ DoubleCoset.Quotient (P : Set G) (K.toSubgroup : Set G) :=
  Equiv.ofBijective (fun ω : Ω => DoubleCoset.mk P K.toSubgroup (ω : G))
    ⟨hdistinct, by
      intro q
      obtain ⟨ω, hω, p, hp, k, hk, hx⟩ := hcover q.out
      exact ⟨⟨ω, hω⟩, (DoubleCoset.eq.mpr ⟨p, hp, k, hk, hx⟩).trans
        (DoubleCoset.out_eq' q)⟩⟩

/-- Glue the compact one-double-coset sections pointwise; no infinite sum is used. -/
private theorem transversalEvaluation_surjective (hK : IsCompact (K : Set G))
    (hcover : ∀ x : G, ∃ ω ∈ Ω, ∃ p ∈ P, ∃ k ∈ K, x = p * ω * k)
    (hdistinct : Function.Injective (fun ω : Ω => DoubleCoset.mk P K.toSubgroup (ω : G))) :
    Function.Surjective (transversalEvaluation P σ K Ω) := by
  intro v
  let E := transversalQuotientEquiv P K Ω hcover hdistinct
  let s : DoubleCoset.Quotient (P : Set G) (K.toSubgroup : Set G) →
      fixedVectors (smoothInduced P σ) K.toSubgroup :=
    fun q => fixedDoubleCosetSection P σ K hK (E.symm q) (v (E.symm q))
  let F : G → V := fun x => eval P σ (s (DoubleCoset.mk P K.toSubgroup x)).val x
  have hcov : ∀ (p : P) (x : G), F ((p : G) * x) = σ p (F x) := by
    intro p x
    dsimp only [F]
    rw [DoubleCoset.mk_mem_mul]
    exact eval_covariant P σ _ p x
  have hright : ∀ (k : K) (x : G), F (x * (k : G)) = F x := by
    intro k x
    dsimp only [F]
    rw [DoubleCoset.mk_mul_mem]
    exact eval_mul_of_mem_fixedVectors P σ K.toSubgroup (s _).property k x
  let f := smoothFunctionOf P σ F hcov K hright
  have hf : f ∈ fixedVectors (smoothInduced P σ) K.toSubgroup := by
    intro k
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact hright k x
  refine ⟨⟨f, hf⟩, ?_⟩
  funext ω
  apply Subtype.ext
  change eval P σ (s (DoubleCoset.mk P K.toSubgroup (ω : G))).val ω = (v ω).val
  have hω : E.symm (DoubleCoset.mk P K.toSubgroup (ω : G)) = ω := E.symm_apply_apply ω
  dsimp only [s]
  rw [hω]
  exact fixedDoubleCosetSection_eval_self P σ K hK ω (v ω)

/-- Compact support meets only finitely many elements of a double-coset transversal. -/
private theorem compactTransversalEvaluation_finite
    (hcover : ∀ x : G, ∃ ω ∈ Ω, ∃ p ∈ P, ∃ k ∈ K, x = p * ω * k)
    (hdistinct : Function.Injective (fun ω : Ω => DoubleCoset.mk P K.toSubgroup (ω : G)))
    (f : fixedVectors (compactInduced P σ) K.toSubgroup) :
    ∃ t : Finset Ω, ∀ ω : Ω, compactFixedEvaluationAt P σ K ω f ≠ 0 → ω ∈ t := by
  have hopen : IsOpenMap (quotientMap P) :=
    MulAction.isOpenQuotientMap_quotientMk.isOpenMap
  obtain ⟨t, ht⟩ := f.val.property.elim_finite_subcover
    (fun i : Ω => quotientMap P '' ((fun k => (i : G) * k) '' (K : Set G)))
    (fun i => hopen _ (isOpenMap_mul_left (i : G) _ K.isOpen))
    (by
      rintro _ ⟨y, -, rfl⟩
      obtain ⟨ω, hω, p, hp, k, hk, hy⟩ := hcover y
      apply Set.mem_iUnion.mpr
      refine ⟨⟨ω, hω⟩, ω * k, ⟨k, hk, rfl⟩, ?_⟩
      apply Quotient.sound
      change QuotientGroup.rightRel P (ω * k) y
      rw [QuotientGroup.rightRel_apply]
      rw [hy]
      convert hp using 1; group)
  refine ⟨t, ?_⟩
  intro ω hω
  have hval : eval P σ f.val.val ω ≠ 0 := fun hz => hω (Subtype.ext hz)
  have hcov := ht ⟨ω, hval, rfl⟩
  simp only [Set.mem_iUnion] at hcov
  obtain ⟨i, hi, _, ⟨k, hk, rfl⟩, he⟩ := hcov
  have hp : (ω : G) * ((i : G) * k)⁻¹ ∈ P :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact he)
  have hiω : i = ω := hdistinct (DoubleCoset.eq.mpr
    ⟨(ω : G) * ((i : G) * k)⁻¹, hp, k, hk, by group⟩)
  exact hiω ▸ hi

/-- Compact evaluation as a dependent finitely supported family on the given transversal. -/
private def compactTransversalEvaluation
    (hcover : ∀ x : G, ∃ ω ∈ Ω, ∃ p ∈ P, ∃ k ∈ K, x = p * ω * k)
    (hdistinct : Function.Injective (fun ω : Ω => DoubleCoset.mk P K.toSubgroup (ω : G))) :
    fixedVectors (compactInduced P σ) K.toSubgroup →ₗ[R]
      (Π₀ ω : Ω, fixedVectors σ (conjOpenSubgroup P K ω).toSubgroup) where
  toFun f := by
    let h := compactTransversalEvaluation_finite P σ K Ω hcover hdistinct f
    exact ⟨fun ω => compactFixedEvaluationAt P σ K ω f,
      Trunc.mk ⟨h.choose.val, fun ω => by
        by_cases hz : compactFixedEvaluationAt P σ K ω f = 0
        · exact Or.inr hz
        · exact Or.inl (h.choose_spec ω hz)⟩⟩
  map_add' f g := by
    apply DFinsupp.ext
    intro ω
    exact map_add (compactFixedEvaluationAt P σ K ω) f g
  map_smul' r f := by
    apply DFinsupp.ext
    intro ω
    exact map_smul (compactFixedEvaluationAt P σ K ω) r f

private theorem compactTransversalEvaluation_injective
    (hcover : ∀ x : G, ∃ ω ∈ Ω, ∃ p ∈ P, ∃ k ∈ K, x = p * ω * k)
    (hdistinct : Function.Injective (fun ω : Ω => DoubleCoset.mk P K.toSubgroup (ω : G))) :
    Function.Injective (compactTransversalEvaluation P σ K Ω hcover hdistinct) := by
  intro f g hfg
  have hs : compactFixedToSmooth P σ K f = compactFixedToSmooth P σ K g := by
    apply transversalEvaluation_injective P σ K Ω hcover
    funext ω
    exact DFunLike.congr_fun hfg ω
  have hv : f.val.val = g.val.val :=
    congrArg (fun z : fixedVectors (smoothInduced P σ) K.toSubgroup => z.val) hs
  exact Subtype.ext (Subtype.ext hv)

/-- A compact section supported on the double coset of the chosen representative. -/
private def compactTransversalSection (hK : IsCompact (K : Set G)) (ω : Ω)
    (v : fixedVectors σ (conjOpenSubgroup P K ω).toSubgroup) :
    fixedVectors (compactInduced P σ) K.toSubgroup :=
  ⟨compactDoubleCosetSection P σ K hK ω v.val v.property, by
    intro k
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext y
    exact compactDoubleCosetSection_mul P σ K hK ω v.val v.property k y⟩

/-- Evaluation of a single section is the corresponding finitely supported coefficient. -/
private theorem compactTransversalEvaluation_section (hK : IsCompact (K : Set G))
    (hcover : ∀ x : G, ∃ ω ∈ Ω, ∃ p ∈ P, ∃ k ∈ K, x = p * ω * k)
    (hdistinct : Function.Injective (fun ω : Ω => DoubleCoset.mk P K.toSubgroup (ω : G)))
    (ω : Ω) (v : fixedVectors σ (conjOpenSubgroup P K ω).toSubgroup) :
    compactTransversalEvaluation P σ K Ω hcover hdistinct
      (compactTransversalSection P σ K Ω hK ω v) = DFinsupp.single ω v := by
  apply DFinsupp.ext
  intro η
  by_cases hωη : ω = η
  · subst η
    rw [DFinsupp.single_eq_same]
    apply Subtype.ext
    exact fixedDoubleCosetSection_eval_self P σ K hK ω v
  · rw [DFinsupp.single_eq_of_ne (Ne.symm hωη)]
    apply Subtype.ext
    exact fixedDoubleCosetSection_eval_of_ne P σ K hK ω v
      (fun he => hωη (hdistinct he.symm))

/-- The section is linear in its coefficient, as checked by injective evaluation. -/
private def compactTransversalSectionLinear (hK : IsCompact (K : Set G))
    (hcover : ∀ x : G, ∃ ω ∈ Ω, ∃ p ∈ P, ∃ k ∈ K, x = p * ω * k)
    (hdistinct : Function.Injective (fun ω : Ω => DoubleCoset.mk P K.toSubgroup (ω : G)))
    (ω : Ω) :
    fixedVectors σ (conjOpenSubgroup P K ω).toSubgroup →ₗ[R]
      fixedVectors (compactInduced P σ) K.toSubgroup where
  toFun := compactTransversalSection P σ K Ω hK ω
  map_add' v w := by
    apply compactTransversalEvaluation_injective P σ K Ω hcover hdistinct
    rw [map_add, compactTransversalEvaluation_section, compactTransversalEvaluation_section,
      compactTransversalEvaluation_section, DFinsupp.single_add]
  map_smul' a v := by
    apply compactTransversalEvaluation_injective P σ K Ω hcover hdistinct
    rw [map_smul, compactTransversalEvaluation_section, compactTransversalEvaluation_section,
      DFinsupp.single_smul]
    rfl

/-- The inverse to compact evaluation is a finite sum of single sections. -/
private def compactTransversalSectionSum (hK : IsCompact (K : Set G))
    (hcover : ∀ x : G, ∃ ω ∈ Ω, ∃ p ∈ P, ∃ k ∈ K, x = p * ω * k)
    (hdistinct : Function.Injective (fun ω : Ω => DoubleCoset.mk P K.toSubgroup (ω : G))) :
    (Π₀ ω : Ω, fixedVectors σ (conjOpenSubgroup P K ω).toSubgroup) →ₗ[R]
      fixedVectors (compactInduced P σ) K.toSubgroup :=
  DFinsupp.lsum R (compactTransversalSectionLinear P σ K Ω hK hcover hdistinct)

private theorem compactTransversalEvaluation_sectionSum (hK : IsCompact (K : Set G))
    (hcover : ∀ x : G, ∃ ω ∈ Ω, ∃ p ∈ P, ∃ k ∈ K, x = p * ω * k)
    (hdistinct : Function.Injective (fun ω : Ω => DoubleCoset.mk P K.toSubgroup (ω : G))) :
    (compactTransversalEvaluation P σ K Ω hcover hdistinct).comp
      (compactTransversalSectionSum P σ K Ω hK hcover hdistinct) = LinearMap.id := by
  apply DFinsupp.lhom_ext
  intro ω v
  change compactTransversalEvaluation P σ K Ω hcover hdistinct
    (DFinsupp.lsum R (compactTransversalSectionLinear P σ K Ω hK hcover hdistinct)
      (DFinsupp.single ω v)) = _
  rw [DFinsupp.lsum_single]
  exact compactTransversalEvaluation_section P σ K Ω hK hcover hdistinct ω v

/-- Renard III.2.2: evaluation on any double-coset transversal gives the smooth
product model and the compact direct-sum model of fixed vectors. -/
theorem inducedFixedVectorTransversal : InducedFixedVectorTransversalStatement.{uR, uG, uV} := by
  intro R G V _ _ _ _ _ _ P σ K hK Ω hcover hdistinct
  constructor
  · refine ⟨LinearEquiv.ofBijective (transversalEvaluation P σ K Ω)
      ⟨transversalEvaluation_injective P σ K Ω hcover,
        transversalEvaluation_surjective P σ K Ω hK hcover hdistinct⟩, ?_⟩
    intro f ω
    rfl
  · refine ⟨LinearEquiv.ofBijective (compactTransversalEvaluation P σ K Ω hcover hdistinct)
      ⟨compactTransversalEvaluation_injective P σ K Ω hcover hdistinct, ?_⟩, ?_⟩
    · intro v
      exact ⟨compactTransversalSectionSum P σ K Ω hK hcover hdistinct v,
        DFunLike.congr_fun
          (compactTransversalEvaluation_sectionSum P σ K Ω hK hcover hdistinct) v⟩
    · intro f ω
      rfl

end Langlands.Induction
