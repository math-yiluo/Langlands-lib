import Langlands.Representation.Classification.DistinctCuspidalProductMultiplicityFreeStatement
import Langlands.Representation.Filtration.GradedRepetitionProof
import Langlands.Representation.CuspidalSupport.InducedJacquetCount
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof
import Langlands.Representation.CuspidalSupport.JacquetDetectingFamilyLengthProof
import Langlands.Representation.CuspidalSupport.CuspidalTensorProof
import Langlands.Representation.CuspidalSupport.DistinctTensorStabilizerProof
import Langlands.Representation.CuspidalSupport.AssociatedProof
import Langlands.Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof

/-!
# Multiplicity freeness of products of distinct supercuspidal data

Ze80 Proposition 2.1(c). The normalized product of pairwise distinct
supercuspidal data has an actual finite composition series, and no two of its
graded factors are equivalent.
-/

noncomputable section

namespace Langlands.Classification

open GeneralLinear Geometric CuspidalSupport PadicField.TopologicalData
open LengthCriterionProof

universe uF uV uW

namespace DistinctCuspidalProduct

section Weyl

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ}

/-- A coordinate permutation whose Weyl transport fixes a tensor of pairwise
distinct actual cuspidal data, up to equivalence, preserves every block. -/
theorem mem_blockWeyl_of_transport_equiv {B : BlockShape n}
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i))
    (hA : letI := T.topology
      Function.Injective (fun i =>
        (⟨B.size i, B.positive i, (A i).isoClass⟩ : CuspidalDatum.{uV, uF} T)))
    {v : Equiv.Perm (Fin n)} (hw : ConjugatesLevi (F := F.Carrier) B B v)
    (E : letI := T.topology
      (transport B B v hw (FiniteTensor.external (fun i => (A i).obj.representation))).Equiv
        (FiniteTensor.external (fun i => (A i).obj.representation))) :
    v ∈ blockWeyl B := by
  let := T.topology
  let d : Fin B.length → CuspidalDatum.{uV, uF} T :=
    fun i => ⟨B.size i, B.positive i, (A i).isoClass⟩
  have : ∀ i, Nontrivial (A i).obj := fun i =>
    nontrivial_of_isIrreducible (A i).obj.representation (hρ := (A i).property.1)
  have hfix : ∀ i, blockMap B B v i = i := by
    intro i
    have hE : Nonempty (Representation.Equiv
        ((A i).obj.representation.comp (factorHom hw i))
        (A (blockMap B B v i)).obj.representation) := by
      refine nonempty_equiv_of_factor_actions (V := fun i => (A i).obj)
        (W := fun j => (A j).obj)
        (hρ := isIrreducible_comp_of_surjective (A i).obj.representation
          (hρ := (A i).property.1) (factorHom hw i) (factorHom_surjective hw i))
        (hσ := (A (blockMap B B v i)).property.1)
        ?_ ?_ (equivComp E (MonoidHom.mulSingle _ (blockMap B B v i)))
      · intro g x
        have h := external_leviConjugation_symm_mulSingle
          (fun i => (A i).obj.representation) hw i g x
        exact h
      · intro g x
        have h := external_mulSingle_tprod (fun i => (A i).obj.representation)
          (blockMap B B v i) g x
        exact h
    obtain ⟨E'⟩ := hE
    have hd : d i = d (blockMap B B v i) :=
      cuspidalDatum_eq_of_equiv (A i) (A (blockMap B B v i)) rfl rfl
        (blockPositionEquiv hw i) (factorHom hw i)
        (fun g x y => factorHom_apply_entry hw i g x y) E'
    exact (hA hd).symm
  intro a
  obtain ⟨⟨i, x⟩, rfl⟩ := B.indexEquiv.surjective a
  change blockIndex B (v (B.index i x)) = blockIndex B (B.index i x)
  rw [blockIndex_image hw i x, hfix, blockIndex_index]

/-- For a tensor of pairwise distinct actual cuspidal data, distinct minimal
conjugating permutations give inequivalent Weyl transports. -/
theorem minimalConjugating_eq_of_transport_equiv {B C : BlockShape n}
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i))
    (hA : letI := T.topology
      Function.Injective (fun i =>
        (⟨B.size i, B.positive i, (A i).isoClass⟩ : CuspidalDatum.{uV, uF} T)))
    (w₁ w₂ : MinimalConjugatingPermutations (F := F.Carrier) B C)
    (E : letI := T.topology
      (transport B C w₁.val.val w₁.property
          (FiniteTensor.external (fun i => (A i).obj.representation))).Equiv
        (transport B C w₂.val.val w₂.property
          (FiniteTensor.external (fun i => (A i).obj.representation)))) :
    w₁ = w₂ := by
  let := T.topology
  let ρ := FiniteTensor.external (fun i => (A i).obj.representation)
  have hinv := conjugatesLevi_inv w₂.property
  have hv := conjugatesLevi_mul w₁.property hinv
  let E' : (transport B B (w₂.val.val⁻¹ * w₁.val.val) hv ρ).Equiv ρ :=
    Representation.Equiv.mk E.toLinearEquiv fun m => by
      refine LinearMap.ext fun x => ?_
      change E (ρ ((leviConjugation B B _ hv).symm m) x) = ρ m (E x)
      rw [leviConjugation_mul w₁.property hinv hv, MulEquiv.symm_trans_apply,
        leviConjugation_inv_symm w₂.property hinv]
      have h := LinearMap.congr_fun
        (E.isIntertwining' (leviConjugation B C _ w₂.property m)) x
      change E (ρ ((leviConjugation B C _ w₁.property).symm
          (leviConjugation B C _ w₂.property m)) x) =
        ρ ((leviConjugation B C _ w₂.property).symm
          (leviConjugation B C _ w₂.property m)) (E x) at h
      rw [MulEquiv.symm_apply_apply] at h
      exact h
  have hb := mem_blockWeyl_of_transport_equiv F T A hA hv E'
  obtain ⟨u, -, hu⟩ := minimalConjugatingCosets (F := F.Carrier) w₁.val.val w₁.property
  have h₁ := hu w₁ ⟨1, (mul_one _).symm⟩
  have h₂ := hu w₂ ⟨⟨_, hb⟩, (mul_inv_cancel_left _ _).symm⟩
  exact h₁.trans h₂.symm

end Weyl

section JacquetImage

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
  (C : BlockShape n) {V : Type uW} [AddCommGroup V] [Module ℂ V]

/-- The actual image of an invariant subspace in the normalized Jacquet module. -/
def jacquetImage {π : Representation ℂ (GeneralLinear n F.Carrier) V}
    (X : Subrepresentation π) : Subrepresentation (T.normalizedJacquet C π) where
  toSubmodule := X.toSubmodule.map (C.jacquetMk π)
  apply_mem_toSubmodule m := by
    rintro _ ⟨v, hv, rfl⟩
    rw [T.normalizedJacquet_mk]
    exact ⟨_, X.toSubmodule.smul_mem _
      (X.apply_mem_toSubmodule (C.leviEmbedding F.Carrier m) hv),
      map_smul (C.jacquetMk π) _ _⟩

/-- Images of the steps of a finite filtration form a finite filtration of the
normalized Jacquet module, with the same length. -/
def jacquetImageFiltration {Y : Rep.{uW} ℂ (GeneralLinear n F.Carrier)} {m : ℕ}
    (s : ObjectRepFiltration Y m) :
    ObjectRepFiltration (Rep.of (T.normalizedJacquet C Y.ρ)) m :=
  ObjectRepFiltration.ofSubrepresentations
    (fun k => jacquetImage T C (s.subrepresentation k))
    (fun _ _ h => by
      rintro _ ⟨v, hv, rfl⟩
      exact ⟨v, s.monotone_subrepresentation h hv, rfl⟩)
    (by
      apply le_antisymm _ bot_le
      rintro _ ⟨v, hv, rfl⟩
      have hv' : v ∈ s.subrepresentation 0 := hv
      rw [s.subrepresentation_zero] at hv'
      have hv0 : v = 0 := hv'
      change C.jacquetMk Y.ρ v = 0
      rw [hv0, map_zero])
    (by
      apply le_antisymm le_top
      intro q _
      obtain ⟨v, rfl⟩ := C.jacquetMk_surjective Y.ρ q
      refine ⟨v, ?_, rfl⟩
      change v ∈ s.subrepresentation (Fin.last m)
      rw [s.subrepresentation_last]
      trivial)

set_option maxHeartbeats 400000 in
/-- Exactness identifies the quotient of two Jacquet images with the Jacquet
module of the corresponding successive quotient. -/
theorem jacquetImage_quotient_equiv {π : Representation ℂ (GeneralLinear n F.Carrier) V}
    (hπ : letI := T.topology; IsSmooth π) {L U : Subrepresentation π} (hLU : L ≤ U) :
    Nonempty ((quotientRep (jacquetImage T C L) (jacquetImage T C U)).Equiv
      (T.normalizedJacquet C (quotientRep L U))) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let ιU : U.toRepresentation.IntertwiningMap π := JacquetLength.subtypeMap U
  let jU := T.normalizedJacquetMap C ιU
  have hjU : Function.Injective jU := by
    change Function.Injective (T.normalizedJacquetMap C ιU).toLinearMap
    rw [T.normalizedJacquetMap_toLinearMap_eq_coinvariantsMap]
    exact coinvariants_map_injective_of_smooth (Parabolic.unipotentFiniteContainment F T C)
      _ (JacquetLength.subtypeMap_injective U) (Parabolic.isSmooth_radical F T C _ hπ)
  have hjU_mem : ∀ x, jU x ∈ jacquetImage T C U := by
    intro x
    obtain ⟨v, rfl⟩ := C.jacquetMk_surjective U.toRepresentation x
    exact ⟨v.val, v.property, rfl⟩
  let gU : (T.normalizedJacquet C U.toRepresentation).IntertwiningMap
      (jacquetImage T C U).toRepresentation :=
    { toLinearMap := jU.toLinearMap.codRestrict _ hjU_mem
      isIntertwining' := fun m => LinearMap.ext fun x =>
        Subtype.ext (LinearMap.congr_fun (jU.isIntertwining' m) x) }
  have hgU : Function.Bijective gU := by
    constructor
    · intro x y h
      exact hjU (congrArg Subtype.val h)
    · rintro ⟨_, v, hv, rfl⟩
      exact ⟨C.jacquetMk U.toRepresentation ⟨v, hv⟩, rfl⟩
  let eU := gU.ofBijective hgU
  let qU : U.toRepresentation.IntertwiningMap (quotientRep L U) :=
    { toLinearMap := (lower L U).mkQ
      isIntertwining' := fun _ => rfl }
  let f := (T.normalizedJacquetMap C qU).comp eU.symm.toIntertwiningMap
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨w, rfl⟩ := C.jacquetMk_surjective (quotientRep L U) y
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (lower L U) w
    refine ⟨gU (C.jacquetMk U.toRepresentation v), ?_⟩
    change T.normalizedJacquetMap C qU (eU.symm (eU (C.jacquetMk U.toRepresentation v))) = _
    rw [eU.symm_apply_apply]
    rfl
  refine MultiplicityAdditivityProof.quotient_equiv_of_surjective
    (A := Rep.of (T.normalizedJacquet C π))
    (B := Rep.of (T.normalizedJacquet C (quotientRep L U))) _ _ f ?_ ?_
  · intro x
    obtain ⟨y, rfl⟩ := hgU.2 x
    obtain ⟨v, rfl⟩ := C.jacquetMk_surjective U.toRepresentation y
    have h1 : eU.symm (gU (C.jacquetMk U.toRepresentation v)) =
        C.jacquetMk U.toRepresentation v :=
      eU.symm_apply_apply _
    change C.jacquetMk π v.val ∈ jacquetImage T C L ↔
      T.normalizedJacquetMap C qU (eU.symm (gU (C.jacquetMk U.toRepresentation v))) = 0
    rw [h1]
    change C.jacquetMk π v.val ∈ jacquetImage T C L ↔
      C.jacquetMk (quotientRep L U) ((lower L U).mkQ v) = 0
    constructor
    · rintro ⟨w, hw, hwv⟩
      have h1 : C.jacquetMk U.toRepresentation ⟨w, hLU hw⟩ =
          C.jacquetMk U.toRepresentation v :=
        hjU (show jU (C.jacquetMk U.toRepresentation ⟨w, hLU hw⟩) =
          jU (C.jacquetMk U.toRepresentation v) from hwv)
      have h2 := congrArg (T.normalizedJacquetMap C qU) h1
      change C.jacquetMk (quotientRep L U) ((lower L U).mkQ ⟨w, hLU hw⟩) =
        C.jacquetMk (quotientRep L U) ((lower L U).mkQ v) at h2
      have hz : (lower L U).mkQ (⟨w, hLU hw⟩ : U.toSubmodule) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hw
      rw [← h2, hz, map_zero]
    · intro h0
      have hU : IsSmooth U.toRepresentation :=
        isSmooth_of_injective ιU (JacquetLength.subtypeMap_injective U) hπ
      let Lsub : Subrepresentation U.toRepresentation :=
        ⟨lower L U, fun g _ hv => L.apply_mem_toSubmodule g hv⟩
      let i := JacquetLength.subtypeMap Lsub
      have hex : LinearMap.range i.toLinearMap = LinearMap.ker qU.toLinearMap := by
        change LinearMap.range (lower L U).subtype = LinearMap.ker (lower L U).mkQ
        rw [Submodule.range_subtype, Submodule.ker_mkQ]
      have hrange := (T.normalizedJacquetMap_exact C i qU hU
        (JacquetLength.subtypeMap_injective Lsub) (Submodule.mkQ_surjective _) hex).2.1
      have hmem : C.jacquetMk U.toRepresentation v ∈
          LinearMap.range (T.normalizedJacquetMap C i).toLinearMap := by
        rw [hrange]
        exact h0
      obtain ⟨z, hz⟩ := hmem
      obtain ⟨z, rfl⟩ := C.jacquetMk_surjective Lsub.toRepresentation z
      exact ⟨z.val.val, z.property, congrArg jU hz⟩
  · exact hf

/-- The graded pieces of the Jacquet image filtration are the Jacquet modules
of the original graded pieces. -/
theorem jacquetImageFiltration_graded {Y : Rep.{uW} ℂ (GeneralLinear n F.Carrier)} {m : ℕ}
    (hY : letI := T.topology; IsSmooth Y.ρ) (s : ObjectRepFiltration Y m) (k : Fin m) :
    Nonempty (((jacquetImageFiltration T C s).gradedRepresentation k).ρ.Equiv
      (T.normalizedJacquet C (s.gradedRepresentation k).ρ)) :=
  jacquetImage_quotient_equiv T C hY
    (s.monotone_subrepresentation (Fin.castSucc_le_succ k))

end JacquetImage

section Detection

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}

/-- Every graded piece of a finite filtration of a smooth representation is an
actual smooth subquotient. -/
theorem exists_isSubquotient_graded
    (A : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear n F.Carrier))
    {m : ℕ} (s : ObjectRepFiltration A.obj m) (k : Fin m) :
    letI := T.topology
    ∃ hk : IsSmooth (s.gradedRepresentation k).ρ,
      SmoothRep.IsSubquotient (SmoothRep.of (s.gradedRepresentation k).ρ hk) A := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let S' := s.subrepresentation k.succ
  have hS' : IsSmooth S'.toRepresentation :=
    isSmooth_of_injective (JacquetLength.subtypeMap S')
      (JacquetLength.subtypeMap_injective S') A.isSmooth
  let q := (s.gradedProjection k).hom
  have hq : Function.Surjective q := s.gradedProjection_surjective k
  have hQ : IsSmooth (s.gradedRepresentation k).ρ := isSmooth_of_surjective q hq hS'
  let Cs : SmoothRep.{0, uF, uW} ℂ (GeneralLinear n F.Carrier) := SmoothRep.of _ hS'
  let Qs : SmoothRep.{0, uF, uW} ℂ (GeneralLinear n F.Carrier) := SmoothRep.of _ hQ
  exact ⟨hQ, SmoothRep.isSubquotient_iff_exists.mpr
    ⟨Cs, SmoothRep.ofHom (A := Cs) (B := A) (JacquetLength.subtypeMap S'),
      SmoothRep.ofHom (A := Cs) (B := Qs) q, JacquetLength.subtypeMap_injective S', hq⟩⟩

/-- Detection: every nonzero smooth subquotient of the normalized induction of
quasicuspidal data has a nonzero normalized Jacquet module along a standard
Levi associated to the inducing Levi. -/
theorem exists_associated_nontrivialJacquet
    (hnon : NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n) (B : BlockShape n) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
      IsLeviQuasicuspidal B σ.representation →
      ∀ D : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
        SmoothRep.IsSubquotient D ((T.normalizedParabolicInductionFunctor B).obj σ) →
        Nontrivial D → ∃ C, LevisAssociated (F := F.Carrier) B C ∧
          Nontrivial ((T.normalizedJacquetFunctor C).obj D) := by
  let := T.topology
  intro σ hσ D hD hnt
  obtain ⟨C, hJ, hJq⟩ := minimalNonzeroJacquet.{uF, max uF uV} p F T n D hnt
  by_cases hC : LevisAssociated (F := F.Carrier) B C
  · exact ⟨C, hC, hJ⟩
  · exfalso
    have hsub := normalizedJacquetSubquotient p F T n C _ _ hD
    have hss := hnon B C σ hσ hC _ hsub hJq
    exact not_subsingleton _ hss

end Detection

end DistinctCuspidalProduct

open DistinctCuspidalProduct

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Ze80 Proposition 2.1(c), conditional on the associated Jacquet filtration
and on the vanishing of quasicuspidal Jacquet subquotients for nonassociated
Levis. -/
theorem distinctCuspidalProductMultiplicityFree_of
    (hfilt : ∀ n, AssociatedJacquetFiltrationTheorem.{uF, uV} F T n)
    (hnon : ∀ n, NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n) :
    DistinctCuspidalProductMultiplicityFree.{uF, uV} F T := by
  let := T.topology
  intro n hn B A hA
  obtain ⟨hirr, -, hqc⟩ := glCuspidalTensor.{uV, uF} p F T n hn B A
  let σ := FiniteTensor.externalSmoothObject (fun i => (A i).obj)
  let P := (T.normalizedParabolicInductionFunctor B).obj σ
  have hd : Function.Injective (fun i =>
      (⟨B.size i, B.positive i, (A i).isoClass⟩ : CuspidalDatum.{uV, uF} T)) := by
    intro i j h
    exact hA (congrArg (fun d : CuspidalDatum.{uV, uF} T =>
      (⟨d.rank, d.cls⟩ : Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d))) h)
  have hbound : ∀ C ∈ JacquetLength.associatedShapes F.Carrier B,
      HasCompositionLengthAtMost (Rep.of ((T.normalizedJacquetFunctor C).obj P).representation)
        (Nat.card (MinimalConjugatingPermutations (F := F.Carrier) B C)) := by
    intro C hC
    obtain ⟨-, r, e, t, ht⟩ :=
      hfilt n B C σ hqc (JacquetLength.mem_associatedShapes.mp hC)
    have hsimple : t.HasSimpleFactors := fun a => by
      obtain ⟨φ⟩ := ht a
      exact JacquetLength.isIrreducible_of_equiv φ.symm
        (JacquetLength.isIrreducible_transport _ (e a).property hirr)
    have hr : Nat.card (MinimalConjugatingPermutations (F := F.Carrier) B C) = r :=
      (Nat.card_congr e).symm.trans (Nat.card_eq_fintype_card.trans (Fintype.card_fin r))
    exact ⟨r, hr.ge, t, hsimple⟩
  have hdet : ∀ D : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
      SmoothRep.IsSubquotient D P → Nontrivial D →
        ∃ C ∈ JacquetLength.associatedShapes F.Carrier B,
          Nontrivial ((T.normalizedJacquetFunctor C).obj D) := by
    intro D hD hnt
    obtain ⟨C, hC, hJ⟩ := exists_associated_nontrivialJacquet T (hnon n) B σ hqc D hD hnt
    exact ⟨C, JacquetLength.mem_associatedShapes.mpr hC, hJ⟩
  obtain ⟨m, -, s, hs⟩ := (jacquetDetectingFamilyLength.{uF, max uF uV} p F T n P
    (JacquetLength.associatedShapes F.Carrier B)
    (fun C => Nat.card (MinimalConjugatingPermutations (F := F.Carrier) B C)) hbound hdet).2
  refine ⟨m, s, hs, ?_⟩
  rintro i j ⟨E⟩
  by_contra hij
  obtain ⟨hsm, hsub⟩ := exists_isSubquotient_graded T P s i
  have hnt : Nontrivial (s.gradedRepresentation i) :=
    nontrivial_of_isIrreducible (s.gradedRepresentation i).ρ (hρ := hs i)
  obtain ⟨C, hC, hJ⟩ :=
    exists_associated_nontrivialJacquet T (hnon n) B σ hqc _ hsub hnt
  obtain ⟨-, r, e, t, ht⟩ := hfilt n B C σ hqc hC
  have hsimple : t.HasSimpleFactors := fun a => by
    obtain ⟨φ⟩ := ht a
    exact JacquetLength.isIrreducible_of_equiv φ.symm
      (JacquetLength.isIrreducible_transport _ (e a).property hirr)
  let u := jacquetImageFiltration T C s
  obtain ⟨φi⟩ := jacquetImageFiltration_graded T C P.isSmooth s i
  obtain ⟨φj⟩ := jacquetImageFiltration_graded T C P.isSmooth s j
  let Eu : (u.gradedRepresentation i).ρ.Equiv (u.gradedRepresentation j).ρ :=
    (φi.trans (JacquetLength.normalizedJacquetEquiv T C E)).trans φj.symm
  have hnu : Nontrivial (u.gradedRepresentation i) :=
    @Equiv.nontrivial _ _ φi.toLinearEquiv.toEquiv hJ
  obtain ⟨a, b, hab, ⟨Ft⟩⟩ :=
    ObjectRepFiltration.exists_equiv_factors_of_equiv_graded t hsimple u hij Eu hnu
  obtain ⟨φa⟩ := ht a
  obtain ⟨φb⟩ := ht b
  exact hab (e.injective (minimalConjugating_eq_of_transport_equiv F T A hd (e a) (e b)
    ((φa.symm.trans Ft).trans φb)))

/-- Ze80 Proposition 2.1(c): the upper normalized product of pairwise distinct
supercuspidal data has an actual finite composition series with pairwise
inequivalent graded factors. -/
theorem distinctCuspidalProductMultiplicityFree :
    DistinctCuspidalProductMultiplicityFree.{uF, uV} F T :=
  distinctCuspidalProductMultiplicityFree_of F T
    (fun n => associatedJacquetFiltration.{uF, uV} F T n)
    (fun n => nonassociatedJacquetSubquotients.{uF, uV} F T n)

end Langlands.Classification
