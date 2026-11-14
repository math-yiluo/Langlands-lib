import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalContragredientStatement
import Langlands.AllFieldBZ.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.AssociationForwardStatement
import Langlands.AllFieldBZ.Representation.CuspidalSupport.TotalConjugatingCountProof
import Langlands.AllFieldBZ.Representation.Induction.Equivalences
import Langlands.Representation.CuspidalSupport.AssociationReduction

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.AssociationReduction`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.AssociationReduction` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedCuspidalInductionFactorsTheorem AssociatedCuspidalInductionHomTheorem AssociatedGeometricPieceEquivalenceTheorem AssociatedGeometricPieceVanishingTheorem AssociatedJacquetFiltrationTheorem CuspidalEmbeddingTheorem CuspidalInductionLengthTheorem MinimalWeylTransportQuasicuspidalTheorem NonassociatedJacquetSubquotientsTheorem PadicAssociatedGeometricPiecesTheorem TotalConjugatingCountTheorem TwoBlockAssociatedCuspidalInductionFactorsTheorem associatedCuspidalInductionFactors_of_adjacent associatedCuspidalInductionFactors_of_length_lt_two associatedGeometricPieceEquivalence factors_of_blockMap factors_step fullRefinedInductionEquiv fullRefinedJacquetEquiv isIrreducible_normalizedParabolicInduced_singleBlock refinedHalfModulus_eq_one_of_full refinedInverseHalfModulus_eq_one_of_full refinedModulus_eq_one_of_full totalConjugatingCount
open Langlands.GeneralLinear
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor
open Langlands.AllFieldBZ.Geometric
universe uF uV uW u

section Transport
variable {F : Type uF} [Field F] {n : ℕ} {B C D : BlockShape n}
  {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end Transport
section GroupEquiv
variable {k : Type u} [Field k] {G : Type uF} {H : Type uW} [Monoid G] [Monoid H]
  {V : Type uV} [AddCommGroup V] [Module k V]

end GroupEquiv
section TransportProperties
variable {F : Type uF} [Field F] {n : ℕ} {B C : BlockShape n}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

variable [TopologicalSpace F] [IsTopologicalRing F]

end TransportProperties
section BlockPermutationTransport
variable {F : Type uF} [Field F] {n : ℕ} (B : BlockShape n) (e : Equiv.Perm (Fin B.length))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

end BlockPermutationTransport
section Swaps
end Swaps
section LengthOne
variable {G : Type uF} [Group G]

end LengthOne
section SingleBlock
variable {n : ℕ}

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- For one block the standard parabolic is everything, and normalized
induction of an irreducible smooth representation is irreducible. -/
theorem isIrreducible_normalizedParabolicInduced_singleBlock (B : BlockShape n)
    (hB : B.length = 1) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (B.Levi F.Carrier) V)
    (hσs : letI := T.topology
      IsSmooth σ) (hσ : Representation.IsIrreducible σ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation.IsIrreducible (T.normalizedParabolicInduced B σ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  have hP : B.parabolic F.Carrier = ⊤ := B.singleBlock_parabolic_eq_top hB F.Carrier
  let χ := (B.inflateCharacter (T.leviHalfCharacter B)).toMonoidHom
  let σP : Representation ℂ (B.parabolic F.Carrier) V :=
    twist χ (σ.comp (B.leviProjection F.Carrier))
  let c : GeneralLinear n F.Carrier →* B.parabolic F.Carrier :=
    (MonoidHom.id _).codRestrict (B.parabolic F.Carrier) (fun g => hP ▸ Subgroup.mem_top g)
  have hc : Continuous c := continuous_id.subtype_mk _
  have hσP : IsSmooth σP :=
    (isSmooth_twist_iff χ _ (B.inflateCharacter (T.leviHalfCharacter B)).isOpen_ker).mpr
      (isSmooth_comp _ (B.leviProjectionContinuous F.Carrier).continuous hσs)
  have hτ : IsSmooth (σP.comp c) := isSmooth_comp c hc hσP
  have E := fullInductionEquiv (B.parabolic F.Carrier) σP (σP.comp c) hP
    (Representation.Equiv.refl σP) hτ
  have hproj : Function.Surjective (B.leviProjection F.Carrier) := fun m =>
    ⟨B.leviInParabolic F.Carrier m, B.leviProjection_section F.Carrier m⟩
  have hcs : Function.Surjective c := fun q => ⟨q.val, rfl⟩
  have hirr : Representation.IsIrreducible (σP.comp c) :=
    (isIrreducible_comp_iff σP c hcs).mpr ((isIrreducible_twist_iff χ _).mpr
      ((isIrreducible_comp_iff σ _ hproj).mpr hσ))
  exact (isIrreducible_iff_of_equiv E).mpr hirr

/-- The case of at most one block. -/
theorem associatedCuspidalInductionFactors_of_length_lt_two (n : ℕ) (hn : 0 < n) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (B C : BlockShape n)
      (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
      B.length < 2 →
      σ.IsIrreducible → IsLeviCuspidal B σ.representation →
      τ.IsIrreducible → IsLeviCuspidal C τ.representation →
      RepresentationsAssociated B C σ.representation τ.representation →
      HaveSameJordanHolderFactors
        (Rep.of (T.normalizedParabolicInduced B σ.representation))
        (Rep.of (T.normalizedParabolicInduced C τ.representation)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  intro B C σ τ hB hσ _ _ _ hassoc
  obtain ⟨w, hw, ⟨φ⟩⟩ := hassoc
  have hB1 : B.length = 1 := by have := length_pos_of_pos B hn; omega
  have hC1 : C.length = 1 := by
    obtain ⟨e, he⟩ := exists_blockMap_of_conjugatesLevi hw
    have hle : ∀ k : Fin C.length, (k : ℕ) < 1 := by
      intro k
      have h := he (w.symm (C.index k ⟨0, C.positive k⟩))
      rw [Equiv.apply_symm_apply, blockIndex_index] at h
      rw [h, ← hB1]
      exact (e.symm _).isLt
    have := length_pos_of_pos C hn
    by_contra hne
    exact absurd (hle ⟨1, by omega⟩) (by simp)
  obtain rfl := eq_of_length_eq_one hB1 hC1
  have hb : w ∈ blockWeyl B := fun a => Fin.ext (by
    have h1 := (blockIndex B (w a)).isLt
    have h2 := (blockIndex B a).isLt
    omega)
  exact haveSameJordanHolderFactors_of_isIrreducible
    (isIrreducible_normalizedParabolicInduced_singleBlock T B hB1 σ.representation
      σ.isSmooth hσ)
    (T.normalizedParabolicInducedEquiv B
      ((transportWeylEquiv w hb hw σ.representation).symm.trans φ))

end SingleBlock
section Reduction
variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) (n : ℕ)

/-- One adjacent swap extends factor matching from block map `e` to `e * s`.
The induction hypothesis keeps the target carrier universe of the source,
while the conclusion allows an arbitrary target carrier universe. -/
theorem factors_step
    (hE : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      ∀ (B C : BlockShape n) (w : Equiv.Perm (Fin n))
        (hw : ConjugatesLevi (F := F.Carrier) B C w) (j : ℕ), j + 1 < B.length →
        (∀ a, (blockIndex C (w a) : ℕ) = Equiv.swap j (j + 1) (blockIndex B a : ℕ)) →
        IsMinimalRepresentative B C w →
        ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
          (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
          σ.IsIrreducible → IsLeviCuspidal B σ.representation →
          τ.IsIrreducible → IsLeviCuspidal C τ.representation →
          Nonempty ((transport B C w hw σ.representation).Equiv τ.representation) →
          HaveSameJordanHolderFactors
            (Rep.of (T.normalizedParabolicInduced B σ.representation))
            (Rep.of (T.normalizedParabolicInduced C τ.representation)))
    (htrans : ∀ (A A' : Rep.{max uF uV} ℂ (GeneralLinear n F.Carrier))
      (A'' : Rep.{max uF uW} ℂ (GeneralLinear n F.Carrier)),
      HaveSameJordanHolderFactors A A' → HaveSameJordanHolderFactors A' A'' →
        HaveSameJordanHolderFactors A A'')
    (B : BlockShape n) (e : Equiv.Perm (Fin B.length))
    (ih : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      ∀ (C : BlockShape n) (w : Equiv.Perm (Fin n))
        (hw : ConjugatesLevi (F := F.Carrier) B C w),
        IsMinimalRepresentative B C w →
        (∀ a, (blockIndex C (w a) : ℕ) = (e.symm (blockIndex B a) : ℕ)) →
        ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
          (τ : SmoothRep.{0, uF, uV} ℂ (C.Levi F.Carrier)),
          σ.IsIrreducible → IsLeviCuspidal B σ.representation →
          τ.IsIrreducible → IsLeviCuspidal C τ.representation →
          Nonempty ((transport B C w hw σ.representation).Equiv τ.representation) →
          HaveSameJordanHolderFactors
            (Rep.of (T.normalizedParabolicInduced B σ.representation))
            (Rep.of (T.normalizedParabolicInduced C τ.representation)))
    (j : ℕ) (hj : j + 1 < B.length) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (C : BlockShape n) (w : Equiv.Perm (Fin n))
      (hw : ConjugatesLevi (F := F.Carrier) B C w),
      IsMinimalRepresentative B C w →
      (∀ a, (blockIndex C (w a) : ℕ) =
        ((e * Equiv.swap (⟨j, by omega⟩ : Fin B.length) ⟨j + 1, hj⟩).symm
          (blockIndex B a) : ℕ)) →
      ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
        (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
        σ.IsIrreducible → IsLeviCuspidal B σ.representation →
        τ.IsIrreducible → IsLeviCuspidal C τ.representation →
        Nonempty ((transport B C w hw σ.representation).Equiv τ.representation) →
        HaveSameJordanHolderFactors
          (Rep.of (T.normalizedParabolicInduced B σ.representation))
          (Rep.of (T.normalizedParabolicInduced C τ.representation)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  intro C w hw hmin hblock σ τ hσ hσc hτ hτc hφ
  obtain ⟨φ⟩ := hφ
  set s : Equiv.Perm (Fin B.length) := Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ with hs
  have hsymm : ∀ x, (e * s).symm x = s (e.symm x) := fun x => by
    rw [Equiv.symm_apply_eq, Equiv.Perm.mul_apply, hs, Equiv.swap_apply_self,
      Equiv.apply_symm_apply]
  let B' := B.permute e
  let w' := B.blockPermutation e
  have hw' : ConjugatesLevi (F := F.Carrier) B B' w' := conjugatesLevi_blockPermutation B e
  have hmin' : IsMinimalRepresentative B B' w' := isMinimalRepresentative_blockPermutation B e
  let v := w * w'⁻¹
  have hvblock : ∀ a, (blockIndex C (v a) : ℕ) = Equiv.swap j (j + 1) (blockIndex B' a : ℕ) := by
    intro a
    obtain ⟨b, rfl⟩ := w'.surjective a
    have hva : v (w' b) = w b := by
      simp only [v, Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    rw [hva, hblock, hsymm, blockIndex_blockPermutation, hs, val_swap_adjacent]
  have hv : ConjugatesLevi (F := F.Carrier) B' C v :=
    conjugatesLevi_of_blockIndex v (fun i => Equiv.swap j (j + 1) (i : ℕ))
      ((Equiv.injective _).comp Fin.val_injective) hvblock
  have hvmin : IsMinimalRepresentative B' C v := by
    apply isMinimalRepresentative_mul_inv hmin hmin'
    · intro a b hab
      rw [blockIndex_blockPermutation, blockIndex_blockPermutation] at hab
      exact e.symm.injective hab
    · intro a b hab
      exact blockIndex_eq_of_conjugatesLevi_apply hw hab
  let σ' : SmoothRep.{0, uF, uV} ℂ (B'.Levi F.Carrier) :=
    SmoothRep.of (transport B B' w' hw' σ.representation)
      (isSmooth_transport B B' w' hw' σ.isSmooth)
  have hσ' : σ'.IsIrreducible := (isIrreducible_transport w' hw' _).mpr hσ
  have hσ'c : IsLeviCuspidal B' σ'.representation :=
    ⟨isAdmissible_transport w' hw' hσc.1,
      isLeviQuasicuspidal_transport_blockPermutation B e hw' hσc.2⟩
  have h1 := ih B' w' hw' hmin' (fun a => by rw [blockIndex_blockPermutation]) σ σ'
    hσ hσc hσ' hσ'c ⟨Representation.Equiv.refl _⟩
  have hvw : v * w' = w := by simp only [v, inv_mul_cancel_right]
  have h2 := hE B' C v hv j hj hvblock hvmin σ' τ hσ' hσ'c hτ hτc
    ⟨by
      change (transport B' C v hv (transport B B' w' hw' σ.representation)).Equiv _
      rw [transport_transport hw' hv hw hvw]
      exact φ⟩
  exact htrans _ _ _ h1 h2

/-- Factor matching along every block map, for a source with at least two
blocks, with source and target carriers in the same universe. -/
theorem factors_of_blockMap
    (hE : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      ∀ (B C : BlockShape n) (w : Equiv.Perm (Fin n))
        (hw : ConjugatesLevi (F := F.Carrier) B C w) (j : ℕ), j + 1 < B.length →
        (∀ a, (blockIndex C (w a) : ℕ) = Equiv.swap j (j + 1) (blockIndex B a : ℕ)) →
        IsMinimalRepresentative B C w →
        ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
          (τ : SmoothRep.{0, uF, uV} ℂ (C.Levi F.Carrier)),
          σ.IsIrreducible → IsLeviCuspidal B σ.representation →
          τ.IsIrreducible → IsLeviCuspidal C τ.representation →
          Nonempty ((transport B C w hw σ.representation).Equiv τ.representation) →
          HaveSameJordanHolderFactors
            (Rep.of (T.normalizedParabolicInduced B σ.representation))
            (Rep.of (T.normalizedParabolicInduced C τ.representation)))
    (htrans : ∀ (A A' : Rep.{max uF uV} ℂ (GeneralLinear n F.Carrier))
      (A'' : Rep.{max uF uV} ℂ (GeneralLinear n F.Carrier)),
      HaveSameJordanHolderFactors A A' → HaveSameJordanHolderFactors A' A'' →
        HaveSameJordanHolderFactors A A'')
    (B : BlockShape n) (hB : 2 ≤ B.length) (e : Equiv.Perm (Fin B.length)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (C : BlockShape n) (w : Equiv.Perm (Fin n))
      (hw : ConjugatesLevi (F := F.Carrier) B C w),
      IsMinimalRepresentative B C w →
      (∀ a, (blockIndex C (w a) : ℕ) = (e.symm (blockIndex B a) : ℕ)) →
      ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
        (τ : SmoothRep.{0, uF, uV} ℂ (C.Levi F.Carrier)),
        σ.IsIrreducible → IsLeviCuspidal B σ.representation →
        τ.IsIrreducible → IsLeviCuspidal C τ.representation →
        Nonempty ((transport B C w hw σ.representation).Equiv τ.representation) →
        HaveSameJordanHolderFactors
          (Rep.of (T.normalizedParabolicInduced B σ.representation))
          (Rep.of (T.normalizedParabolicInduced C τ.representation)) := by
  refine Submonoid.induction_of_closure_eq_top_right (closure_adjacent_swaps B.length) e ?_ ?_
  · have h0 : 0 + 1 < B.length := by omega
    have hbase := factors_step F T n hE htrans B
      (Equiv.swap (⟨0, by omega⟩ : Fin B.length) ⟨0 + 1, h0⟩)
      (fun C w hw hmin hblock σ τ hσ hσc hτ hτc hφ =>
        hE B C w hw 0 h0 (fun a => by
          rw [hblock, Equiv.symm_swap]
          exact val_swap_adjacent h0 _) hmin σ τ hσ hσc hτ hτc hφ) 0 h0
    rw [Equiv.swap_mul_self] at hbase
    exact hbase
  · rintro x _ ⟨j, hj, rfl⟩ ih
    exact factors_step F T n hE htrans B x ih j hj

/-- The reduction of factor matching for associated irreducible cuspidal data
to adjacent block swaps and factor-matching transitivity. -/
theorem associatedCuspidalInductionFactors_of_adjacent
    (hEV : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      ∀ (B C : BlockShape n) (w : Equiv.Perm (Fin n))
        (hw : ConjugatesLevi (F := F.Carrier) B C w) (j : ℕ), j + 1 < B.length →
        (∀ a, (blockIndex C (w a) : ℕ) = Equiv.swap j (j + 1) (blockIndex B a : ℕ)) →
        IsMinimalRepresentative B C w →
        ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
          (τ : SmoothRep.{0, uF, uV} ℂ (C.Levi F.Carrier)),
          σ.IsIrreducible → IsLeviCuspidal B σ.representation →
          τ.IsIrreducible → IsLeviCuspidal C τ.representation →
          Nonempty ((transport B C w hw σ.representation).Equiv τ.representation) →
          HaveSameJordanHolderFactors
            (Rep.of (T.normalizedParabolicInduced B σ.representation))
            (Rep.of (T.normalizedParabolicInduced C τ.representation)))
    (hEW : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      ∀ (B C : BlockShape n) (w : Equiv.Perm (Fin n))
        (hw : ConjugatesLevi (F := F.Carrier) B C w) (j : ℕ), j + 1 < B.length →
        (∀ a, (blockIndex C (w a) : ℕ) = Equiv.swap j (j + 1) (blockIndex B a : ℕ)) →
        IsMinimalRepresentative B C w →
        ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
          (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
          σ.IsIrreducible → IsLeviCuspidal B σ.representation →
          τ.IsIrreducible → IsLeviCuspidal C τ.representation →
          Nonempty ((transport B C w hw σ.representation).Equiv τ.representation) →
          HaveSameJordanHolderFactors
            (Rep.of (T.normalizedParabolicInduced B σ.representation))
            (Rep.of (T.normalizedParabolicInduced C τ.representation)))
    (htransV : ∀ (A A' : Rep.{max uF uV} ℂ (GeneralLinear n F.Carrier))
      (A'' : Rep.{max uF uV} ℂ (GeneralLinear n F.Carrier)),
      HaveSameJordanHolderFactors A A' → HaveSameJordanHolderFactors A' A'' →
        HaveSameJordanHolderFactors A A'')
    (htransW : ∀ (A A' : Rep.{max uF uV} ℂ (GeneralLinear n F.Carrier))
      (A'' : Rep.{max uF uW} ℂ (GeneralLinear n F.Carrier)),
      HaveSameJordanHolderFactors A A' → HaveSameJordanHolderFactors A' A'' →
        HaveSameJordanHolderFactors A A'')
    (hn : 0 < n) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (B C : BlockShape n)
      (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
      σ.IsIrreducible → IsLeviCuspidal B σ.representation →
      τ.IsIrreducible → IsLeviCuspidal C τ.representation →
      RepresentationsAssociated B C σ.representation τ.representation →
      HaveSameJordanHolderFactors
        (Rep.of (T.normalizedParabolicInduced B σ.representation))
        (Rep.of (T.normalizedParabolicInduced C τ.representation)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  intro B C σ τ hσ hσc hτ hτc hassoc
  by_cases hB : B.length < 2
  · exact associatedCuspidalInductionFactors_of_length_lt_two T n hn B C σ τ hB hσ hσc hτ hτc
      hassoc
  replace hB : 2 ≤ B.length := not_lt.mp hB
  obtain ⟨w, hw, ⟨φ⟩⟩ := hassoc
  obtain ⟨⟨⟨v, hvmin⟩, hv⟩, ⟨⟨b, hb⟩, hwvb⟩, -⟩ := minimalConjugatingCosets w hw
  have hbB : ConjugatesLevi (F := F.Carrier) B B b :=
    conjugatesLevi_of_blockIndex b (fun i => (i : ℕ)) Fin.val_injective
      (fun a => by rw [hb a])
  obtain ⟨e, he⟩ := exists_blockMap_of_conjugatesLevi hv
  have hiso : (transport B C v hv σ.representation).Equiv τ.representation := by
    refine (transportEquiv v hv (transportWeylEquiv b hb hbB σ.representation).symm).trans ?_
    rw [transport_transport hbB hv hw hwvb.symm]
    exact φ
  have h0 : 0 + 1 < B.length := by omega
  have hall := factors_of_blockMap F T n hEV htransV B hB
    (e * Equiv.swap (⟨0, by omega⟩ : Fin B.length) ⟨0 + 1, h0⟩)
  refine factors_step F T n hEW htransW B _ hall 0 h0 C v hv hvmin (fun a => ?_)
    σ τ hσ hσc hτ hτc ⟨hiso⟩
  rw [mul_assoc, Equiv.swap_mul_self, mul_one]
  exact he a

end Reduction
end Langlands.AllFieldBZ.CuspidalSupport
