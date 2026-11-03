import Langlands.Representation.Smooth.FixedVectors.CompactRestrictionDetectionStatement
import Langlands.Representation.CompactCoefficient.SelectedAssembly
import Langlands.Representation.CompactCoefficient.AdmissibleComplement
import Langlands.Representation.Smooth.FixedVectors.FiniteTypes

/-! # Fixed-vector detection from a finite compact restriction -/

set_option autoImplicit false

noncomputable section

namespace Langlands

open CompactCoefficientClass

universe uG uV uI

/-- The full finite compact-restriction detection statement. -/
theorem compactRestrictionFixedVectorDetection :
    CompactRestrictionFixedVectorDetectionStatement.{uG, uV, uI} := by
  intro G _ _ _ N _ _ _ _ _ _ μ _ A D K hKN hgen ι _ _ V hVirr hVcomp hspan hDA
  classical
  let E : ι → IrreducibleCompactCoefficientRep.{uG, uV} N := fun i =>
    ⟨SmoothRep.subrepresentation (SmoothRep.restrictSubgroup N D) (V i),
      hVirr i, hVcomp i⟩
  let f : ∀ i, (E i).obj.representation.IntertwiningMap
      (SmoothRep.restrictSubgroup N D).representation := fun i =>
    SmoothRep.hom (SmoothRep.subtype (SmoothRep.restrictSubgroup N D) (V i))
  have hf : ∀ i, Function.Injective (f i) := fun _ => Subtype.val_injective
  have hfrange : ∀ i, (f i).range.toSubmodule = (V i).toSubmodule := by
    intro i
    ext v
    exact ⟨fun ⟨w, hw⟩ => hw ▸ w.property, fun hv => ⟨⟨v, hv⟩, rfl⟩⟩
  have hfspan : (⨆ i, (f i).range.toSubmodule) = ⊤ := by
    simpa only [hfrange] using hspan
  have hcof : ∀ L : OpenSubgroup N, ∃ J : OpenSubgroup N,
      IsCompact (J : Set N) ∧ J ≤ L := by
    intro L
    obtain ⟨J, hJL, hJ, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance N ∅ L
    exact ⟨J, hJ, hJL⟩
  have hsplit := CompactSplitting.isCompl_isotypicSubrepresentation_annihilatorSubrepresentation
    μ hcof
  let t := classesOfFiniteFamily E
  have ht : ∀ (g : G) c, c ∈ t ↔
      pullbackEquiv (SmoothRep.normalSubgroupInverseConjugation N g) c ∈ t :=
    mem_classesOfFiniteFamily_conjugation_iff N E f hf hfspan
      (fun c => hsplit c.val (SmoothRep.restrictSubgroup N D))
  let h := fun (B : SmoothRep.{0, uG, uV} ℂ N) (c : t) => hsplit c.val B
  let Q := (selectedBlockPair N t ht A (h (SmoothRep.restrictSubgroup N A))).2
  by_contra hn
  have hzero : ∀ v : D, v ∈ fixedVectors D.representation K → v = 0 := by
    intro v hv
    by_contra hv0
    exact hn ⟨v, hv, hv0⟩
  have hQ : Q = ⊤ := by
    apply hgen Q
    intro v hv
    change v ∈ (ambientSelectedProjector N t ht
      (h (SmoothRep.restrictSubgroup N A))).ker.toSubmodule
    rw [ambientSelectedProjector_ker]
    change (v : SmoothRep.restrictSubgroup N A) ∈
      selectedAnnihilatorSubrepresentation t (SmoothRep.restrictSubgroup N A)
    rw [selectedAnnihilatorSubrepresentation]
    apply (Subrepresentation.mem_iInf
      (ρ := (SmoothRep.restrictSubgroup N A).representation) _ _).mpr
    intro c
    obtain ⟨i, hi⟩ := (mem_classesOfFiniteFamily E c.val).mp c.property
    rw [annihilatorSubrepresentation_eq_iInf_ker (E i) hi]
    apply (Subrepresentation.mem_iInf
      (ρ := (SmoothRep.restrictSubgroup N A).representation) _ _).mpr
    intro p
    have hvN : v ∈ fixedVectors (SmoothRep.restrictSubgroup N A).representation
        (K.comap N.subtype) := by
      intro k
      exact hv ⟨k, k.property⟩
    have hp := map_mem_fixedVectors (f i) (map_mem_fixedVectors p hvN)
    have hpK : (f i) (p v) ∈ fixedVectors D.representation K := by
      intro k
      exact hp ⟨⟨k, hKN k.property⟩, k.property⟩
    have hz := hzero _ hpK
    exact (hf i) (hz.trans (map_zero (f i)).symm)
  let i₀ : ι := Classical.choice inferInstance
  have hnot := selectedBlockPair_not_isSubquotient N t ht h A D
    (V i₀) (hVirr i₀) (hVcomp i₀)
    ((mem_classesOfFiniteFamily E _).mpr ⟨i₀, rfl⟩)
  apply hnot
  obtain ⟨C, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hDA
  let j : C.representation.IntertwiningMap (SmoothRep.subrepresentation A Q).representation :=
    { toLinearMap := (SmoothRep.hom i).toLinearMap.codRestrict Q.toSubmodule
        (fun v => by rw [hQ]; trivial)
      isIntertwining' g := by
        ext v
        exact Subtype.ext
          (Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom i) g v) }
  exact SmoothRep.isSubquotient_iff_exists.mpr
    ⟨C, SmoothRep.ofHom j, q, fun x y hxy => hi (congrArg Subtype.val hxy), hq⟩

end Langlands
