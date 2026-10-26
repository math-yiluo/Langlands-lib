import Langlands.Representation.CuspidalSupport.DistinctTensorStabilizerStatement
import Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof
import Langlands.Representation.CuspidalSupport.AssociationLawsProof
import Langlands.Representation.Geometric.WeylMinimalRepresentativeProof

/-! The self-stabilizer of an actual tensor with distinct cuspidal factors. -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric PadicField.TopologicalData

universe uF uV

/-- A tensor with pairwise distinct actual cuspidal block data has exactly
one minimal self-associating coordinate permutation. -/
theorem distinctCuspidalTensorStabilizer_count
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    {n : ℕ} (B : BlockShape n)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i))
    (hA : letI := T.topology
      Function.Injective (fun i =>
        (⟨B.size i, B.positive i, (A i).isoClass⟩ : CuspidalDatum.{uV,uF} T))) :
    letI := T.topology
    Nat.card (AssociatingPermutations B B
      (FiniteTensor.external (fun i => (A i).obj.representation))
      (FiniteTensor.external (fun i => (A i).obj.representation))) = 1 := by
  let := T.topology
  let ρ := FiniteTensor.external (fun i => (A i).obj.representation)
  let d : Fin B.length → CuspidalDatum.{uV,uF} T :=
    fun i => ⟨B.size i, B.positive i, (A i).isoClass⟩
  have hmin : IsMinimalRepresentative B B 1 :=
    ⟨fun i => index_strictMono B i, fun i => index_strictMono B i⟩
  let one : AssociatingPermutations B B ρ ρ :=
    ⟨⟨⟨1, hmin⟩, conjugatesLevi_one B⟩, by
      unfold transport
      rw [leviConjugation_one]
      exact ⟨Representation.Equiv.refl ρ⟩⟩
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨one, fun w => ?_⟩
  let v := w.val.val.val
  have hw : ConjugatesLevi (F := F.Carrier) B B v := w.val.property
  obtain ⟨E⟩ := w.property
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
  have hv : v ∈ blockWeyl B := by
    intro a
    obtain ⟨⟨i, x⟩, rfl⟩ := B.indexEquiv.surjective a
    change blockIndex B (v (B.index i x)) = blockIndex B (B.index i x)
    rw [blockIndex_image hw i x, hfix, blockIndex_index]
  have hcoset : weylDoubleCoset B B w.val.val =
      weylDoubleCoset B B ⟨1, hmin⟩ :=
    DoubleCoset.eq.mpr
      ⟨v⁻¹, (blockWeyl B).inv_mem hv, 1, (blockWeyl B).one_mem, by simp [v]⟩
  have heq := weylDoubleCoset_injective B B hcoset
  apply Subtype.ext
  apply Subtype.ext
  exact heq

/-- Exact published self-stabilizer statement for pairwise distinct actual
cuspidal tensor factors. -/
theorem glDistinctCuspidalTensorStabilizer
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    GLDistinctCuspidalTensorStabilizerStatement.{uF,uV} F T := by
  let := T.topology
  intro n B A hA
  exact distinctCuspidalTensorStabilizer_count F T B A hA

end Langlands.CuspidalSupport
