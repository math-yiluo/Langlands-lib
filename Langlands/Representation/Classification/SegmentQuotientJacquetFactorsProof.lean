import Langlands.Representation.Classification.SegmentQuotientJacquetFactorsStatement
import Langlands.Representation.Classification.SegmentQuotientJacquetSingleBlock
import Langlands.Representation.Classification.SegmentWeakQuotientHeadProof
import Langlands.Representation.Classification.SegmentHeadJacquetStatement
import Langlands.Representation.Classification.SegmentSpecialConstituentExistenceProof
import Langlands.Representation.Classification.SegmentHeadJacquetProof
import Langlands.Group.GL.AdjacentMergeShape
import Langlands.Group.GL.HeadTailBlocks
import Langlands.Representation.Parabolic.RefinementTransitivityStatement
import Langlands.Representation.Parabolic.RefinementJacquetTransitivityProof
import Langlands.Representation.Parabolic.FlattenedJacquetComparisonProof
import Langlands.Representation.Tensor.FlattenedGLRefinement
import Langlands.Representation.Parabolic.RefinedJacquetTensor

/-! Actual ordered Jacquet factors of weak segment quotients. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GeneralLinear.BlockShape

open scoped BigOperators

variable {n k : ℕ} (B : BlockShape n) (h : B.length = k + 2)

/-- Assemble dependent data at the original first and ordered tail labels. -/
private def headTailCons {A : Fin B.length → Sort*}
    (v₀ : A (B.headIndex h)) (v₁ : ∀ j, A (B.tailIndex h j)) :
    ∀ i, A i :=
  fun i => Fin.cases (motive := fun j => A (Fin.cast h.symm j)) v₀ v₁ (Fin.cast h i)

@[simp] private theorem headTailCons_head {A : Fin B.length → Sort*}
    (v₀ : A (B.headIndex h)) (v₁ : ∀ j, A (B.tailIndex h j)) :
    B.headTailCons h v₀ v₁ (B.headIndex h) = v₀ := rfl

@[simp] private theorem headTailCons_tail {A : Fin B.length → Sort*}
    (v₀ : A (B.headIndex h)) (v₁ : ∀ j, A (B.tailIndex h j))
    (j : Fin (k + 1)) :
    B.headTailCons h v₀ v₁ (B.tailIndex h j) = v₁ j := rfl

/-- The head/tail dependent eliminator retains the original block labels. -/
private theorem headTail_forall {P : Fin B.length → Prop}
    (h₀ : P (B.headIndex h)) (h₁ : ∀ j, P (B.tailIndex h j)) :
    ∀ i, P i :=
  B.headTailCons h h₀ h₁

private theorem sum_headTailCons (a : ℕ) (b : Fin (k + 1) → ℕ) :
    (∑ i, B.headTailCons (A := fun _ => ℕ) h a b i) = a + ∑ j, b j := by
  calc
    _ = ∑ i : Fin (k + 2), B.headTailCons (A := fun _ => ℕ) h a b (Fin.cast h.symm i) :=
      (Equiv.sum_comp (finCongr h.symm) _).symm
    _ = a + ∑ j, b j := by
      rw [Fin.sum_univ_succ (fun i : Fin (k + 2) =>
        B.headTailCons (A := fun _ => ℕ) h a b (Fin.cast h.symm i))]
      rfl

private theorem prefix_headTailCons_head (a : ℕ) (b : Fin (k + 1) → ℕ) :
    (∑ i : Fin B.length with i < B.headIndex h, B.headTailCons (A := fun _ => ℕ) h a b i) = 0 := by
  have hn : ∀ i : Fin B.length, ¬i < B.headIndex h := by
    intro i
    change ¬i.val < 0
    omega
  simp only [hn, Finset.filter_false, Finset.sum_empty]

private theorem prefix_headTailCons_tail (a : ℕ) (b : Fin (k + 1) → ℕ)
    (j : Fin (k + 1)) :
    (∑ i : Fin B.length with i < B.tailIndex h j, B.headTailCons (A := fun _ => ℕ) h a b i) =
      a + ∑ i : Fin (k + 1) with i < j, b i := by
  rw [Finset.sum_filter, Finset.sum_filter]
  calc
    _ = ∑ i : Fin (k + 2),
        if Fin.cast h.symm i < B.tailIndex h j then
          B.headTailCons (A := fun _ => ℕ) h a b (Fin.cast h.symm i) else 0 :=
      (Equiv.sum_comp (finCongr h.symm) _).symm
    _ = a + ∑ i : Fin (k + 1), if i < j then b i else 0 := by
      rw [Fin.sum_univ_succ (fun i : Fin (k + 2) =>
        if Fin.cast h.symm i < B.tailIndex h j then
          B.headTailCons (A := fun _ => ℕ) h a b (Fin.cast h.symm i) else 0)]
      simp only [show (Fin.cast h.symm 0 : Fin B.length) = B.headIndex h from rfl,
        B.headIndex_lt_tailIndex h j, ite_true, B.headTailCons_head]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      have hlt : Fin.cast h.symm i.succ < B.tailIndex h j ↔ i < j := by
        change i.val + 1 < j.val + 1 ↔ i.val < j.val
        omega
      simp only [hlt]
      rfl

end Langlands.GeneralLinear.BlockShape

namespace Langlands.Parabolic.SegmentJacquetAssembly

open GeneralLinear Geometric

universe uF uV

/-- Tensor actual factor equivalences over their dependent product group. -/
private def externalCongr {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]
    {V W : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {ρ : ∀ i, Representation ℂ (G i) (V i)}
    {τ : ∀ i, Representation ℂ (G i) (W i)}
    (E : ∀ i, (ρ i).Equiv (τ i)) :
    (FiniteTensor.external ρ).Equiv (FiniteTensor.external τ) :=
  Representation.Equiv.mk (PiTensorProduct.congr (fun i => (E i).toLinearEquiv))
    (fun g => by
      ext v
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, FiniteTensor.external_tprod, PiTensorProduct.congr_tprod]
      congr 1
      funext i
      exact LinearMap.congr_fun ((E i).isIntertwining' (g i)) (v i))

/-- A zero factor kills the entire indexed tensor, by pure-tensor spanning. -/
private theorem tensor_subsingleton_of_factor {ι : Type*} {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (j : ι) (hz : Subsingleton (V j)) : Subsingleton (PiTensorProduct ℂ V) := by
  let := hz
  have hzero : ∀ x : PiTensorProduct ℂ V, x = 0 := by
    intro x
    induction x using PiTensorProduct.induction_on with
    | smul_tprod a v =>
      rw [(PiTensorProduct.tprod ℂ).map_coord_zero j (Subsingleton.elim (v j) 0), smul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

/-- Cancel the inverse group pullback in an actual equivalence. -/
private def cancelPullback {G H : Type*} [Group G] [Group H]
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : G ≃* H) {ρ : Representation ℂ H V} {τ : Representation ℂ G W}
    (E : ρ.Equiv (τ.comp e.symm.toMonoidHom)) :
    Representation.Equiv (ρ.comp e.toMonoidHom) τ :=
  Representation.Equiv.mk E.toLinearEquiv (fun g => by
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using E.isIntertwining' (e g))

variable {n : ℕ} (B D : BlockShape n) (S : BlockRefinement D)
  (e : ((i : Fin D.length) × Fin (S i).length) ≃ Fin B.length)
  (hs : ∀ a, (S a.1).size a.2 = B.size (e a))
  (hc : ∀ i j x, D.index i ((S i).index j x) =
    B.index (e ⟨i,j⟩) (Fin.cast (hs ⟨i,j⟩) x))

include hc in
private theorem orderedBlock_cast_eq
    (h : (D.flatten S).length = B.length)
    (a : (i : Fin D.length) × Fin (S i).length) :
    Fin.cast h (D.flattenBlockEquiv S a) = e a := by
  let f := D.flattenBlockEquiv S
  let H : Fin (D.flatten S).length → Fin (D.flatten S).length :=
    fun k => Fin.cast h.symm (e (f.symm k))
  have hmono : StrictMono H := by
    intro k l hkl
    obtain ⟨⟨i,j⟩, rfl⟩ := f.surjective k
    obtain ⟨⟨i',j'⟩, rfl⟩ := f.surjective l
    change e (f.symm (f ⟨i,j⟩)) < e (f.symm (f ⟨i',j'⟩))
    simp only [Equiv.symm_apply_apply]
    rcases (D.flattenBlockEquiv_lt_iff S _ _).mp hkl with hi | ⟨hi,hj⟩
    · exact B.refinementBlock_lt_of_outer_lt D S e hs hc j j' hi
    · change i = i' at hi
      subst i'
      exact B.refinementBlock_strictMono D S e hs hc i hj
  have hfix : H (f a) = f a := le_antisymm hmono.apply_le hmono.le_apply
  apply Fin.ext
  have hval := congrArg Fin.val hfix
  simpa only [H, Fin.val_cast, Equiv.symm_apply_apply] using hval.symm

include hc in
private theorem orderedFlattenShape_eq : D.flatten S = B := by
  have hl : (D.flatten S).length = B.length := by
    have h := Fintype.card_congr ((D.flattenBlockEquiv S).symm.trans e)
    simpa only [Fintype.card_fin] using h
  refine BlockShape.ext_of_size hl ?_
  intro k
  obtain ⟨a, rfl⟩ := (D.flattenBlockEquiv S).surjective k
  rw [orderedBlock_cast_eq B D S e hs hc hl a,
    D.flatten_size_flattenBlockEquiv S a, hs a]

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Conditional passage from intrinsic transitivity to the actual ordered
Levi of any standard shape with the specified consecutive coordinates. -/
private def orderedRefinementJacquetEquiv
    (hcomparison : FlattenedNormalizedJacquetComparisonStatement.{uF,max uF uV})
    (htrans : NormalizedRefinementJacquetTransitivityClause.{uF,max uF uV} F T D S) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier),
      (T.normalizedJacquet B A.representation).Equiv
        ((T.normalizedRefinedJacquet D S (T.normalizedJacquet D A.representation)).comp
          (B.leviRefinementEquiv D S e hs F.Carrier).toMonoidHom) := by
  letI := T.topology
  intro A
  have hshape := orderedFlattenShape_eq B D S e hs hc
  subst B
  have he : e = D.flattenBlockEquiv S := by
    apply Equiv.ext
    intro a
    exact (orderedBlock_cast_eq (D.flatten S) D S e hs hc rfl a).symm
  subst e
  have hlevi : (D.flatten S).leviRefinementEquiv D S (D.flattenBlockEquiv S) hs
      F.Carrier = flattenedLeviEquiv F.Carrier D S :=
    FiniteTensor.leviRefinementEquiv_flatten F.Carrier D S
  rw [hlevi]
  let E : (T.normalizedRefinedJacquet D S (T.normalizedJacquet D A.representation)).Equiv
      (T.normalizedComposedJacquet D S A.representation) :=
    SmoothRep.equivOfIso (htrans.choose.app A)
  let φ := (hcomparison F T D S A.representation).choose
  exact φ.symm.trans (E.symm.precomp (flattenedLeviEquiv F.Carrier D S).toMonoidHom)

/-- Object-level refinement assembly, with every actual block rank transport.
The hypotheses supply only the coarse tensor and its individual refined factors. -/
private def orderedJacquetTensorEquiv
    (hcomparison : FlattenedNormalizedJacquetComparisonStatement.{uF,max uF uV})
    (htrans : NormalizedRefinementJacquetTransitivityClause.{uF,max uF uV} F T D S) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
      (τ : ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (D.size i) F.Carrier))
      (σ : ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
      (T.normalizedJacquet D A.representation).Equiv
        (D.blockTensor (fun i => (τ i).representation)) →
      (∀ i, (T.normalizedJacquet (S i) (τ i).representation).Equiv
        ((S i).blockTensor (fun j =>
          ((hs ⟨i,j⟩).symm ▸ σ (e ⟨i,j⟩) :
            SmoothRep.{0,uF,max uF uV} ℂ
              (GeneralLinear ((S i).size j) F.Carrier)).representation))) →
      (T.normalizedJacquet B A.representation).Equiv
        (B.blockTensor (fun i => (σ i).representation)) := by
  letI := T.topology
  intro A τ σ E H
  let inner := fun i j =>
    ((hs ⟨i,j⟩).symm ▸ σ (e ⟨i,j⟩) :
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((S i).size j) F.Carrier))
  let Einner : Representation.Equiv
      (FiniteTensor.external (fun i => T.normalizedJacquet (S i) (τ i).representation))
      (FiniteTensor.external (fun i => (S i).blockTensor (fun j => (inner i j).representation))) :=
    externalCongr H
  let Etensor : Representation.Equiv
      (T.normalizedRefinedJacquet D S (D.blockTensor (fun i => (τ i).representation)))
      ((FiniteTensor.external (fun i => (S i).blockTensor
        (fun j => (inner i j).representation))).comp
        (refinedLeviEquiv F.Carrier D S).symm.toMonoidHom) :=
    (RefinedJacquetTensor.jacquetEquiv T D S (fun i => (τ i).obj)).trans
      (Einner.precomp (refinedLeviEquiv F.Carrier D S).symm.toMonoidHom)
  let Eregrp : Representation.Equiv
      (T.normalizedRefinedJacquet D S (D.blockTensor (fun i => (τ i).representation)))
      ((B.blockTensor (fun i => (σ i).representation)).comp
        (B.leviRefinementEquiv D S e hs F.Carrier).symm.toMonoidHom) :=
    Etensor.trans (FiniteTensor.glRefinementEquiv F T B D S e hs σ).symm
  let Ecoarse : Representation.Equiv
      (T.normalizedRefinedJacquet D S (T.normalizedJacquet D A.representation))
      (T.normalizedRefinedJacquet D S (D.blockTensor (fun i => (τ i).representation))) :=
    RefinedJacquetTensor.normalizedRefinedJacquetCongr T D S E
  exact (orderedRefinementJacquetEquiv B D S e hs hc F T hcomparison htrans A).trans
    (cancelPullback (B.leviRefinementEquiv D S e hs F.Carrier) (Ecoarse.trans Eregrp))

include hc in
/-- Vanishing of the coarse Jacquet module propagates through the actual refined
quotient and the ordered transitivity equivalence. -/
private theorem orderedJacquet_subsingleton_of_coarse
    (hcomparison : FlattenedNormalizedJacquetComparisonStatement.{uF,max uF uV})
    (htrans : NormalizedRefinementJacquetTransitivityClause.{uF,max uF uV} F T D S) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier),
      Subsingleton (D.JacquetModule A.representation) →
      Subsingleton (B.JacquetModule A.representation) := by
  let := T.topology
  intro A hzero
  let := hzero
  let ρ := T.normalizedJacquet D A.representation
  have hz : Subsingleton (RefinedJacquetModule D S ρ) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨v, rfl⟩ := RefinedJacquetTensor.refinedJacquetMk_surjective D S ρ x
    obtain ⟨w, rfl⟩ := RefinedJacquetTensor.refinedJacquetMk_surjective D S ρ y
    rw [Subsingleton.elim v w]
  let := hz
  let E := orderedRefinementJacquetEquiv B D S e hs hc F T hcomparison htrans A
  exact ⟨fun x y => E.injective (Subsingleton.elim _ _)⟩

include hc in
/-- A vanishing individual refined factor also gives vanishing on the original
ordered shape, after a supplied coarse tensor identification. -/
private theorem orderedJacquet_subsingleton_of_factor
    (hcomparison : FlattenedNormalizedJacquetComparisonStatement.{uF,max uF uV})
    (htrans : NormalizedRefinementJacquetTransitivityClause.{uF,max uF uV} F T D S) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
      (τ : ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (D.size i) F.Carrier)),
      (T.normalizedJacquet D A.representation).Equiv
        (D.blockTensor (fun i => (τ i).representation)) →
      ∀ j, Subsingleton ((S j).JacquetModule (τ j).representation) →
        Subsingleton (B.JacquetModule A.representation) := by
  let := T.topology
  intro A τ E j hz
  let := tensor_subsingleton_of_factor
    (V := fun i => (S i).JacquetModule (τ i).representation) j hz
  let X := orderedRefinementJacquetEquiv B D S e hs hc F T hcomparison htrans A
  let Y := RefinedJacquetTensor.normalizedRefinedJacquetCongr T D S E
  let Z := RefinedJacquetTensor.jacquetEquiv T D S (fun i => (τ i).obj)
  let L := X.toLinearEquiv.trans (Y.toLinearEquiv.trans Z.toLinearEquiv)
  exact ⟨fun x y => L.injective (Subsingleton.elim _ _)⟩

/-- Exact degree transport of the actual Jacquet carrier and action. Shape
transport preserves its block labels, sizes, and Levi definitionally. -/
private def rankCastJacquetEquiv {r s : ℕ} (h : r = s) (C : BlockShape s) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear s F.Carrier),
      (T.normalizedJacquet (C.rankCast h.symm)
        (h.symm ▸ A : SmoothRep.{0,uF,max uF uV} ℂ
          (GeneralLinear r F.Carrier)).representation).Equiv
        (T.normalizedJacquet C A.representation) := by
  letI := T.topology
  cases h
  intro A
  exact Representation.Equiv.refl _

private theorem familyRankCast_eq {ι : Type*} {size : ι → ℕ} {A : ℕ → Type*}
    (σ : ∀ i, A (size i)) {i j : ι} (hij : i = j) (hr : size i = size j) :
    hr ▸ σ i = σ j := by
  subst j
  rfl

private def blockTensorFamilyEquiv {r : ℕ} (C : BlockShape r) :
    letI := T.topology
    ∀ (σ τ : ∀ i, SmoothRep.{0,uF,max uF uV} ℂ
      (GeneralLinear (C.size i) F.Carrier)), σ = τ →
      (C.blockTensor (fun i => (σ i).representation)).Equiv
        (C.blockTensor (fun i => (τ i).representation)) := by
  letI := T.topology
  intro σ τ h
  subst τ
  exact Representation.Equiv.refl _

/-- Combine the unchanged first factor and the actual ordered tail factors. -/
private def headTailTensorEquiv {k : ℕ} (h : B.length = k + 2)
    (hcomparison : FlattenedNormalizedJacquetComparisonStatement.{uF,max uF uV})
    (htrans : NormalizedRefinementJacquetTransitivityClause.{uF,max uF uV} F T
      (B.headTailShape h) (B.headTailRefinement h)) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
      (τ : ∀ i : Fin 2, SmoothRep.{0,uF,max uF uV} ℂ
        (GeneralLinear ((B.headTailShape h).size i) F.Carrier))
      (σ : ∀ j, SmoothRep.{0,uF,max uF uV} ℂ
        (GeneralLinear ((B.tailShape h).size j) F.Carrier)),
      (T.normalizedJacquet (B.headTailShape h) A.representation).Equiv
        ((B.headTailShape h).blockTensor (fun i => (τ i).representation)) →
      (T.normalizedJacquet (B.tailShape h) (τ 1).representation).Equiv
        ((B.tailShape h).blockTensor (fun j => (σ j).representation)) →
      (T.normalizedJacquet B A.representation).Equiv
        (B.blockTensor (fun i => (B.headTailCons (A := fun j => SmoothRep.{0,uF,max uF uV} ℂ
          (GeneralLinear (B.size j) F.Carrier)) h (τ 0) σ i).representation)) := by
  letI := T.topology
  intro A τ σ E Etail
  let υ : ∀ j, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size j) F.Carrier) :=
    B.headTailCons h (τ 0) σ
  refine orderedJacquetTensorEquiv B (B.headTailShape h) (B.headTailRefinement h)
    (B.headTailBlockEquiv h) (B.headTailBlock_size h) (B.headTail_index h)
    F T hcomparison htrans A τ υ E ?_
  intro i
  change Fin 2 at i
  refine Fin.cases ?_ (fun j => ?_) i
  · have hf : (fun j : Fin (B.headShape h).length =>
        ((B.headTailBlock_size h ⟨0,j⟩).symm ▸ υ (B.headTailBlockEquiv h ⟨0,j⟩) :
          SmoothRep.{0,uF,max uF uV} ℂ
            (GeneralLinear ((B.headShape h).size j) F.Carrier))) =
        (fun j => ((B.headShape h).singleBlock_size rfl j).symm ▸ τ 0) := by
      funext j
      exact familyRankCast_eq (size := B.size)
        (A := fun r => SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear r F.Carrier))
        υ (B.headTailBlockEquiv_head h j) _
    exact (T.singleBlockNormalizedJacquetTensorEquiv (B.headShape h) rfl (τ 0)).trans
      (blockTensorFamilyEquiv F T (B.headShape h) _ _ hf.symm)
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hf : (fun j : Fin (B.tailShape h).length =>
        ((B.headTailBlock_size h ⟨1,j⟩).symm ▸ υ (B.headTailBlockEquiv h ⟨1,j⟩) :
          SmoothRep.{0,uF,max uF uV} ℂ
            (GeneralLinear ((B.tailShape h).size j) F.Carrier))) = σ := by
      funext j
      exact familyRankCast_eq (size := B.size)
        (A := fun r => SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear r F.Carrier))
        υ (B.headTailBlockEquiv_tail h j) _
    exact Etail.trans (blockTensorFamilyEquiv F T (B.tailShape h) _ _ hf.symm)

/-- The first/tail instance retains exactly the original actual block labels. -/
private abbrev headTailJacquetEquiv {k : ℕ} (h : B.length = k + 2)
    (hcomparison : FlattenedNormalizedJacquetComparisonStatement.{uF,max uF uV})
    (htrans : NormalizedRefinementJacquetTransitivityClause.{uF,max uF uV} F T
      (B.headTailShape h) (B.headTailRefinement h)) :=
  orderedRefinementJacquetEquiv B (B.headTailShape h) (B.headTailRefinement h)
    (B.headTailBlockEquiv h) (B.headTailBlock_size h) (B.headTail_index h)
    F T hcomparison htrans

end Langlands.Parabolic.SegmentJacquetAssembly

namespace Langlands.Classification

open GeneralLinear
open scoped BigOperators

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The full factor alternative, with precisely the original ordered interval
and degree-transport clauses. This is an internal abbreviation for assembly. -/
private def FactorBranch :
    letI := T.topology
    ∀ (Δ : T.Segment.{max uF uV,uF})
      (_π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
      (_B : BlockShape Δ.degree), Prop :=
  letI := T.topology
  fun Δ π B =>
    ∃ (k : Fin B.length → ℕ)
      (Γ : Fin B.length → T.Segment.{max uF uV,uF})
      (hdeg : ∀ i, (Γ i).degree = B.size i)
      (σ : ∀ i, SmoothRep.{0,uF,max uF uV} ℂ
        (GeneralLinear (B.size i) F.Carrier)),
      (∀ i, 0 < k i) ∧
      (∀ i, B.size i = Δ.rank * k i) ∧
      (∑ i, k i) = Δ.length ∧
      (∀ i, (Γ i).length = k i) ∧
      (∀ i, (Γ i).base =
        Δ.member (Δ.length - (∑ j : Fin B.length with j < i, k j) - k i)) ∧
      (∀ i, T.IsSegmentQuotient (Γ i) ((hdeg i).symm ▸ σ i)) ∧
      Nonempty ((T.normalizedJacquet B π.representation).Equiv
        (B.blockTensor (fun i => (σ i).representation)))

/-- A supplied proper two-block head calculation gives the full ordered factor
alternative on its native split shape. -/
private theorem factors_split_of_head
    (hformula : SegmentHeadJacquetFormula.{uF,max uF uV} F T) :
    letI := T.topology
    ∀ (Δ : T.Segment.{max uF uV,uF})
      (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentHead Δ π →
      ∀ (q : ℕ) (hq : 0 < q) (hqm : q < Δ.length),
        FactorBranch T Δ π (Δ.splitShape q hq hqm) := by
  let := T.topology
  intro Δ π hπ q hq hqm
  classical
  obtain ⟨π₁, π₂, hπ₁, hπ₂, ⟨e⟩⟩ := (hformula Δ π hπ).2 q hq hqm
  let k : Fin 2 → ℕ := ![Δ.length - q, q]
  let Γ : Fin 2 → T.Segment.{max uF uV,uF} :=
    ![Δ.terminal q hqm, Δ.initial q hq]
  let hdeg : ∀ i, (Γ i).degree = (Δ.splitShape q hq hqm).size i := by
    intro i
    fin_cases i <;> rfl
  let σ := Δ.splitFactors q hq hqm π₁ π₂
  refine ⟨k, Γ, hdeg, σ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact Nat.sub_pos_of_lt hqm
    · exact hq
  · intro i
    fin_cases i <;> exact Nat.mul_comm _ _
  · change (∑ i : Fin 2, k i) = Δ.length
    rw [Fin.sum_univ_two]
    exact Nat.sub_add_cancel hqm.le
  · intro i
    fin_cases i <;> rfl
  · intro i
    fin_cases i
    · change Δ.member q = Δ.member
        (Δ.length - (∑ j : Fin 2 with j < 0, k j) - (Δ.length - q))
      simp only [Fin.not_lt_zero, Finset.filter_false, Finset.sum_empty, Nat.sub_zero]
      congr 1
      omega
    · change Δ.base = Δ.member
        (Δ.length - (∑ j : Fin 2 with j < 1, k j) - q)
      have hp : (∑ j : Fin 2 with j < 1, k j) = Δ.length - q := by
        rw [Finset.sum_filter, Fin.sum_univ_two]
        simp [k]
      rw [hp]
      have hz : Δ.length - (Δ.length - q) - q = 0 := by omega
      rw [hz, Δ.member_zero]
  · intro i
    fin_cases i
    · exact hπ₁.isSegmentQuotient
    · exact hπ₂.isSegmentQuotient
  · exact ⟨SmoothRep.equivOfIso e⟩

/-- Every ordered two-block shape is either an indivisible vanishing split or
a literal segment split. The supplied head formula is still a premise. -/
private theorem factors_twoBlock_of_head
    (hformula : SegmentHeadJacquetFormula.{uF,max uF uV} F T) :
    letI := T.topology
    ∀ (Δ : T.Segment.{max uF uV,uF})
      (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentHead Δ π →
      ∀ (B : BlockShape Δ.degree), B.length = 2 →
        Subsingleton (B.JacquetModule π.representation) ∨ FactorBranch T Δ π B := by
  let := T.topology
  intro Δ π hπ B hB
  classical
  let i₀ : Fin B.length := Fin.cast hB.symm 0
  let i₁ : Fin B.length := Fin.cast hB.symm 1
  let l := B.size i₁
  have hl : 0 < l := B.positive i₁
  have hsum : B.size i₀ + l = Δ.degree := by
    calc
      _ = ∑ i : Fin 2, B.size (Fin.cast hB.symm i) := (Fin.sum_univ_two _).symm
      _ = ∑ i, B.size i := Equiv.sum_comp (finCongr hB.symm) _
      _ = Δ.degree := B.sum_eq
  have hln : l < Δ.degree := by
    have := B.positive i₀
    omega
  have hshape : B = BlockShape.ofPair (Δ.degree - l) l (Nat.sub_pos_of_lt hln) hl
      (Nat.sub_add_cancel hln.le) := by
    refine BlockShape.ext_of_size hB ?_
    intro i
    have hi : ∃ j : Fin 2, i = Fin.cast hB.symm j :=
      ⟨Fin.cast hB i, by simp⟩
    obtain ⟨j, rfl⟩ := hi
    fin_cases j
    · change B.size i₀ = Δ.degree - l
      omega
    · rfl
  by_cases hd : Δ.rank ∣ l
  · obtain ⟨q, hqeq⟩ := hd
    have hq : 0 < q := by
      by_contra hn
      have hz : q = 0 := by omega
      simp [hz] at hqeq
      omega
    have hqm : q < Δ.length := by
      have hlt : q * Δ.rank < Δ.length * Δ.rank := by
        simpa only [hqeq, Nat.mul_comm, PadicField.TopologicalData.Segment.degree]
          using hln
      exact (Nat.mul_lt_mul_right Δ.rank_pos).mp hlt
    have hqeq' : l = q * Δ.rank := hqeq.trans (Nat.mul_comm _ _)
    have hsplit : B = Δ.splitShape q hq hqm := by
      have hl' : 0 < Δ.degree - q * Δ.rank := by
        rw [← hqeq']
        exact Nat.sub_pos_of_lt hln
      exact hshape.trans (by
        simpa only [← hqeq'] using (Δ.splitShape_eq_ofPair q hq hqm hl').symm)
    right
    rw [hsplit]
    exact factors_split_of_head T hformula Δ π hπ q hq hqm
  · left
    have hv := (hformula Δ π hπ).1 l hl hln hd
    rw [hshape]
    exact hv

/-- Conditional complete factorization for all shapes with at most two blocks.
Strong constituent existence and the proper head formula remain explicit inputs. -/
theorem segmentQuotientJacquetFactors_length_le_two
    (hex : SegmentSpecialConstituentExistence.{uF,max uF uV} F T)
    (hformula : SegmentHeadJacquetFormula.{uF,max uF uV} F T) :
    letI := T.topology
    ∀ (Δ : T.Segment.{max uF uV,uF})
      (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentQuotient Δ π →
      ∀ (B : BlockShape Δ.degree), B.length ≤ 2 →
        Subsingleton (B.JacquetModule π.representation) ∨ FactorBranch T Δ π B := by
  let := T.topology
  intro Δ π hπ B hB
  have hpos : 0 < B.length := by
    by_contra hn
    have hz : B.length = 0 := by omega
    have hs : Δ.degree = 0 := by
      rw [← B.sum_eq]
      apply Finset.sum_eq_zero
      intro i _
      exact Fin.elim0 (Fin.cast hz i)
    have := Δ.degree_pos
    omega
  have hcases : B.length = 1 ∨ B.length = 2 := by omega
  rcases hcases with hone | htwo
  · exact Or.inr (segmentQuotientJacquetFactors_singleBlock T Δ π hπ B hone)
  · have hhead := (segmentWeakQuotientHeadUpgrade F T hex Δ π).mp hπ
    exact factors_twoBlock_of_head T hformula Δ π hhead B htwo

open Parabolic.SegmentJacquetAssembly

/-- One ordered induction step. The recursive assertion is required only for
the smaller actual tail shape, with its exact segment degree transport. -/
private theorem factors_headTail_step
    (hcomparison : Parabolic.FlattenedNormalizedJacquetComparisonStatement.{uF,max uF uV}) :
    letI := T.topology
    ∀ (Δ : T.Segment.{max uF uV,uF})
      (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
      (B : BlockShape Δ.degree) {l : ℕ} (h : B.length = l + 2),
      Parabolic.NormalizedRefinementJacquetTransitivityClause.{uF,max uF uV} F T
        (B.headTailShape h) (B.headTailRefinement h) →
      (Subsingleton ((B.headTailShape h).JacquetModule π.representation) ∨
        FactorBranch T Δ π (B.headTailShape h)) →
      (∀ (Θ : T.Segment.{max uF uV,uF})
        (τ : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Θ.degree F.Carrier))
        (hd : Θ.degree = B.tailRank h), T.IsSegmentQuotient Θ τ →
          Subsingleton (((B.tailShape h).rankCast hd.symm).JacquetModule τ.representation) ∨
            FactorBranch T Θ τ ((B.tailShape h).rankCast hd.symm)) →
      Subsingleton (B.JacquetModule π.representation) ∨ FactorBranch T Δ π B := by
  let := T.topology
  intro Δ π B l h htrans houter htail
  classical
  rcases houter with hz | hb
  · exact Or.inl (orderedJacquet_subsingleton_of_coarse B (B.headTailShape h)
      (B.headTailRefinement h) (B.headTailBlockEquiv h) (B.headTailBlock_size h)
      (B.headTail_index h) F T hcomparison htrans π hz)
  simp only [FactorBranch, BlockShape.headTailShape_length] at hb
  obtain ⟨ko, Γo, hd, τ, hpos, hsize, hsum, hlen, hbase, hquo, ⟨E⟩⟩ := hb
  change (∑ i : Fin 2, ko i) = Δ.length at hsum
  change ∀ i : Fin 2, (Γo i).base =
    Δ.member (Δ.length - (∑ j : Fin 2 with j < i, ko j) - ko i) at hbase
  have hkadd : ko (0 : Fin 2) + ko (1 : Fin 2) = Δ.length := by
    simpa only [Fin.sum_univ_two] using hsum
  have hbase₀ : (Γo (0 : Fin 2)).base = Δ.member (Δ.length - ko (0 : Fin 2)) := by
    simpa only [Fin.not_lt_zero, Finset.filter_false, Finset.sum_empty, Nat.sub_zero]
      using hbase (0 : Fin 2)
  have hbase₁ : (Γo (1 : Fin 2)).base = Δ.base := by
    have hp : (∑ j : Fin 2 with j < 1, ko j) = ko 0 := by
      rw [Finset.sum_filter, Fin.sum_univ_two]
      simp
    have hi : Δ.length - ko (0 : Fin 2) - ko (1 : Fin 2) = 0 := by omega
    simpa only [hp, hi, Δ.member_zero] using hbase (1 : Fin 2)
  have hrank₁ : (Γo (1 : Fin 2)).rank = Δ.rank := congrArg
    PadicField.TopologicalData.CuspidalDatum.rank hbase₁
  let τ₁ : SmoothRep.{0,uF,max uF uV} ℂ
      (GeneralLinear (Γo (1 : Fin 2)).degree F.Carrier) :=
    (hd (1 : Fin 2)).symm ▸ τ (1 : Fin 2)
  let J := rankCastJacquetEquiv F T (hd (1 : Fin 2)) (B.tailShape h) (τ (1 : Fin 2))
  rcases htail (Γo (1 : Fin 2)) τ₁ (hd (1 : Fin 2)) (hquo (1 : Fin 2)) with hz | ht
  · have hz' : Subsingleton ((B.tailShape h).JacquetModule (τ (1 : Fin 2)).representation) :=
      ⟨fun x y => J.symm.injective (hz.elim _ _)⟩
    exact Or.inl (orderedJacquet_subsingleton_of_factor B (B.headTailShape h)
      (B.headTailRefinement h) (B.headTailBlockEquiv h) (B.headTailBlock_size h)
      (B.headTail_index h) F T hcomparison htrans π τ E (1 : Fin 2) hz')
  simp only [FactorBranch] at ht
  obtain ⟨kt, Γt, hdt, σ, hpost, hsizet, hsumt, hlent, hbaset, hquot, ⟨Et⟩⟩ := ht
  change Fin (l + 1) → ℕ at kt
  change (∑ i : Fin (l + 1), kt i) = (Γo (1 : Fin 2)).length at hsumt
  change ∀ i : Fin (l + 1), (Γt i).base =
    (Γo (1 : Fin 2)).member
      ((Γo (1 : Fin 2)).length - (∑ j : Fin (l + 1) with j < i, kt j) - kt i) at hbaset
  let κ : Fin B.length → ℕ := B.headTailCons h (ko (0 : Fin 2)) kt
  let Γ : Fin B.length → T.Segment.{max uF uV,uF} :=
    B.headTailCons h (Γo (0 : Fin 2)) Γt
  let υ : ∀ i, SmoothRep.{0,uF,max uF uV} ℂ
      (GeneralLinear (B.size i) F.Carrier) :=
    B.headTailCons h (τ (0 : Fin 2)) σ
  let Hdeg : ∀ i, (Γ i).degree = B.size i :=
    B.headTail_forall h (hd (0 : Fin 2)) hdt
  right
  refine ⟨κ, Γ, Hdeg, υ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact B.headTail_forall h (hpos (0 : Fin 2)) hpost
  · refine B.headTail_forall h (hsize (0 : Fin 2)) ?_
    intro j
    change B.size (B.tailIndex h j) = Δ.rank * kt j
    exact (hsizet j).trans (by rw [hrank₁])
  · change (∑ i, B.headTailCons (A := fun _ => ℕ) h (ko (0 : Fin 2)) kt i) = Δ.length
    rw [B.sum_headTailCons, hsumt, hlen (1 : Fin 2)]
    exact hkadd
  · exact B.headTail_forall h (hlen (0 : Fin 2)) hlent
  · refine B.headTail_forall h ?_ ?_
    · change (Γo (0 : Fin 2)).base =
        Δ.member (Δ.length -
          (∑ j : Fin B.length with j < B.headIndex h, κ j) - ko (0 : Fin 2))
      rw [show (∑ j : Fin B.length with j < B.headIndex h, κ j) = 0 from
        B.prefix_headTailCons_head h _ _, Nat.sub_zero]
      exact hbase₀
    · intro j
      change (Γt j).base =
        Δ.member (Δ.length -
          (∑ i : Fin B.length with i < B.tailIndex h j, κ i) - kt j)
      rw [show (∑ i : Fin B.length with i < B.tailIndex h j, κ i) =
        ko (0 : Fin 2) + ∑ i : Fin (l + 1) with i < j, kt i from
          B.prefix_headTailCons_tail h _ _ j]
      have hi : Δ.length -
          (ko (0 : Fin 2) + ∑ i : Fin (l + 1) with i < j, kt i) - kt j =
          (Γo (1 : Fin 2)).length -
            (∑ i : Fin (l + 1) with i < j, kt i) - kt j := by
        rw [hlen (1 : Fin 2)]
        omega
      rw [hi]
      exact (hbaset j).trans (by
        change (Γo (1 : Fin 2)).base.twist _ = Δ.base.twist _
        rw [hbase₁])
  · refine B.headTail_forall h (hquo (0 : Fin 2)) ?_
    intro j
    exact hquot j
  · exact ⟨headTailTensorEquiv B F T h hcomparison htrans π τ σ E (J.symm.trans Et)⟩

/-- All ordered shapes follow from the independent strong-constituent existence,
and proper two-block head calculation. Flattened comparison and intrinsic
normalized upper Jacquet transitivity are published theorems. -/
theorem segmentQuotientJacquetFactors_of_headFormula
    (hex : SegmentSpecialConstituentExistence.{uF,max uF uV} F T)
    (hformula : SegmentHeadJacquetFormula.{uF,max uF uV} F T) :
    SegmentQuotientJacquetFactors.{uF,uV} F T := by
  let := T.topology
  have hcomparison : Parabolic.FlattenedNormalizedJacquetComparisonStatement.{uF,max uF uV} :=
    Parabolic.flattenedJacquetComparison.{0,uF,max uF uV}.2
  have H : ∀ b : ℕ,
      ∀ (Δ : T.Segment.{max uF uV,uF})
        (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
        (B : BlockShape Δ.degree),
        B.length = b → T.IsSegmentQuotient Δ π →
          Subsingleton (B.JacquetModule π.representation) ∨ FactorBranch T Δ π B := by
    intro b
    induction b using Nat.strong_induction_on with
    | h b ih =>
      intro Δ π B hB hπ
      by_cases hsmall : b ≤ 2
      · exact segmentQuotientJacquetFactors_length_le_two T hex hformula Δ π hπ B
          (by omega)
      · have h : B.length = (b - 2) + 2 := by omega
        refine factors_headTail_step T hcomparison Δ π B h
          (Parabolic.normalizedRefinementJacquetTransitivity F T _ _) ?_ ?_
        · exact segmentQuotientJacquetFactors_length_le_two T hex hformula Δ π hπ
            (B.headTailShape h) (by rw [BlockShape.headTailShape_length])
        · intro Θ τ hd hτ
          exact ih ((b - 2) + 1) (by omega) Θ τ
            ((B.tailShape h).rankCast hd.symm) rfl hτ
  intro Δ π hπ B
  exact H B.length Δ π B rfl hπ

/-- With the published strong-constituent existence theorem, only the proper
two-block head calculation remains as a hypothesis. -/
theorem segmentQuotientJacquetFactors_of_segmentHeadJacquetFormula
    (hformula : SegmentHeadJacquetFormula.{uF,max uF uV} F T) :
    SegmentQuotientJacquetFactors.{uF,uV} F T :=
  segmentQuotientJacquetFactors_of_headFormula T
    (segmentSpecialConstituentExistence.{uF,max uF uV} F T) hformula

/-- Every ordered Jacquet module of a weak segment quotient is zero or the
tensor product of weak quotients of the successive descending subsegments. -/
theorem segmentQuotientJacquetFactors
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    SegmentQuotientJacquetFactors.{uF,uV} F T :=
  segmentQuotientJacquetFactors_of_segmentHeadJacquetFormula T
    (segmentHeadJacquetFormula.{uF,max uF uV} F T)

end Langlands.Classification
