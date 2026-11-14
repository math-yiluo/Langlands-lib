import Langlands.AllFieldBZ.Group.GL.BlockIwahoriBasis
import Langlands.AllFieldBZ.Group.GL.UnramifiedCharacter
import Langlands.AllFieldBZ.HarmonicAnalysis.Conductor
import Langlands.AllFieldBZ.Representation.CuspidalSupport.AssociationReduction
import Langlands.AllFieldBZ.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof
import Langlands.AllFieldBZ.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.AllFieldBZ.Representation.Tensor.FactorMatchingStatement
import Langlands.Representation.Tensor.FactorMatchingProof

/-!
# All-field port of `Langlands.Representation.Tensor.FactorMatchingProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Tensor.FactorMatchingProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.FiniteTensor.FactorMatchingProof
open Langlands.FiniteTensor.FactorMatchingProof
open Langlands.CuspidalSupport hiding AssociatedCuspidalInductionFactorsTheorem AssociatedCuspidalInductionHomTheorem AssociatedGeometricPieceEquivalenceTheorem AssociatedGeometricPieceVanishingTheorem AssociatedJacquetFiltrationTheorem CuspidalEmbeddingTheorem CuspidalInductionLengthTheorem IrreducibleQuasicuspidalLeviAdmissibilityTheorem MinimalNonzeroJacquetTheorem MinimalWeylTransportQuasicuspidalTheorem NonassociatedJacquetSubquotientsTheorem NormalizedQuasicuspidalEmbeddingTheorem PadicAssociatedGeometricPiecesTheorem TotalConjugatingCountTheorem TwoBlockAssociatedCuspidalInductionFactorsTheorem ZeroRankCuspidalEmbeddingTheorem associatedCuspidalInductionFactors_of_adjacent associatedCuspidalInductionFactors_of_length_lt_two associatedGeometricPieceEquivalence factors_of_blockMap factors_step fullRefinedInductionEquiv fullRefinedJacquetEquiv isIrreducible_normalizedParabolicInduced_singleBlock minimalNonzeroJacquet normalizedQuasicuspidalEmbedding normalizedQuasicuspidalEmbedding_of refinedHalfModulus_eq_one_of_full refinedInverseHalfModulus_eq_one_of_full refinedModulus_eq_one_of_full totalConjugatingCount
open Langlands.AllFieldBZ.CuspidalSupport
universe uK uG uH uV uW uX uY

section Algebra
variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]

variable {H : Type uH} [Monoid H]

private noncomputable def _root_.Langlands.FiniteTensor.FactorMatchingProof.tensorEquiv
    {V : Type uV} {W : Type uW} {X : Type uX} {Y : Type uY}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    {ρ : Representation k G V} {σ : Representation k G W}
    {τ : Representation k G X} {υ : Representation k G Y}
    (e : ρ.Equiv σ) (f : τ.Equiv υ) :
    (Representation.tprod ρ τ).Equiv (Representation.tprod σ υ) :=
  Representation.Equiv.mk (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv)
    (fun g => (e.toIntertwiningMap.tensor f.toIntertwiningMap).isIntertwining' g)

private theorem _root_.Langlands.FiniteTensor.FactorMatchingProof.tensor_right_matching_of_graded
    {A : Rep.{uV} k G} {B : Rep.{uV} k G}
    {A' : Rep.{uW} k G} {B' : Rep.{uW} k G} {n : ℕ}
    (s : ObjectRepFiltration A n) (t : ObjectRepFiltration A' n)
    (p : Equiv.Perm (Fin n))
    (h : ∀ i, HaveSameJordanHolderFactors
      (Rep.of (Representation.tprod (s.gradedRepresentation i).ρ B.ρ))
      (Rep.of (Representation.tprod (t.gradedRepresentation (p i)).ρ B'.ρ))) :
    HaveSameJordanHolderFactors
      (Rep.of (Representation.tprod A.ρ B.ρ))
      (Rep.of (Representation.tprod A'.ρ B'.ρ)) := by
  apply gradedJordanHolderRefinement k G _ _ n (s.tensorRight B) (t.tensorRight B') p
  intro i
  exact haveSameJordanHolderFactors_transport (h i) (s.tensorRightGradedEquiv B i).symm
    (t.tensorRightGradedEquiv B' (p i)).symm

end Algebra
section Admissible
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem _root_.Langlands.FiniteTensor.FactorMatchingProof.graded_admissible
    (hG : ∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ K ≤ H)
    {A : Rep.{uV} ℂ G} {n : ℕ} (s : ObjectRepFiltration A n)
    (ha : IsAdmissible A.ρ) (i : Fin n) :
    IsAdmissible (s.gradedRepresentation i).ρ := by
  have hu : IsAdmissible (s.subrepresentation i.succ).toRepresentation :=
    isAdmissible_of_injective
      { toLinearMap := (s.subrepresentation i.succ).toSubmodule.subtype
        isIntertwining' := fun _ => rfl }
      Subtype.val_injective ha
  exact Unramified.SphericalExistence.isAdmissible_of_surjective hG
    (s.gradedProjection i).hom (s.gradedProjection_surjective i) hu

end Admissible
section Binary
open scoped TensorProduct
private abbrev _root_.Langlands.FiniteTensor.FactorMatchingProof.pairType (X Y : Type uV) : PUnit.{1} ⊕ PUnit.{1} → Type uV :=
  Sum.elim (fun _ => X) (fun _ => Y)

variable {G H : Type uG} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  {V W : Type uV} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

set_option backward.isDefEq.respectTransparency false in
private theorem _root_.Langlands.FiniteTensor.FactorMatchingProof.binary_irreducible
    (ρ : Representation ℂ G V) (σ : Representation ℂ H W)
    (ha : IsAdmissible ρ) (hb : IsAdmissible σ)
    (hi : ρ.IsIrreducible) (hj : σ.IsIrreducible) :
    (Representation.tprod (ρ.comp (MonoidHom.fst G H))
      (σ.comp (MonoidHom.snd G H))).IsIrreducible := by
  let τ : ∀ i, Representation ℂ ((pairType G H) i) ((pairType V W) i) := Sum.rec (fun _ => ρ) (fun _ => σ)
  let : ∀ i, (τ i).IsIrreducible := Sum.rec (fun _ => hi) (fun _ => hj)
  have ht := Langlands.FiniteTensor.isIrreducible_external τ (by
    intro i φ
    cases i with
    | inl a => exact (admissibleSchur_scalarEndomorphism ρ ha hi φ).exists
    | inr a => exact (admissibleSchur_scalarEndomorphism σ hb hj φ).exists)
  let f : G × H →* (∀ i, (pairType G H) i) :=
    { toFun := fun g => Sum.rec (fun _ => g.1) (fun _ => g.2)
      map_one' := by
        funext i
        cases i <;> rfl
      map_mul' := by
        intro a b
        funext i
        cases i <;> rfl }
  have hf : Function.Surjective f := by
    intro g
    refine ⟨(g (.inl PUnit.unit), g (.inr PUnit.unit)), ?_⟩
    funext i
    cases i with
    | inl a => cases a; rfl
    | inr a => cases a; rfl
  let L0 := PiTensorProduct.tmulEquivDep ℂ (pairType V W)
  let L1 := L0.symm
  let L2 :=
      (TensorProduct.congr
        (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : PUnit.{1} => V) PUnit.unit)
        (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : PUnit.{1} => W) PUnit.unit))
  let L := L1.trans L2
  have hL : ∀ v : ∀ i, (pairType V W) i, L (PiTensorProduct.tprod ℂ v) =
      v (.inl PUnit.unit) ⊗ₜ[ℂ] v (.inr PUnit.unit) := by
    intro v
    have h := congrArg L2 (PiTensorProduct.tmulEquivDep_symm_apply ℂ (pairType V W) v)
    exact h.trans (by simp [L2])
  let e : Representation.Equiv ((Langlands.FiniteTensor.external τ).comp f)
      (Representation.tprod (ρ.comp (MonoidHom.fst G H))
        (σ.comp (MonoidHom.snd G H))) :=
    Representation.Equiv.mk L (fun g => by
      ext v
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, MonoidHom.comp_apply, Langlands.FiniteTensor.external_tprod, hL,
        Representation.tprod_apply, TensorProduct.map_tmul]
      rfl)
  exact (JordanHolderTransportProof.subrepOrderIso e).isSimpleOrder_iff.mp
    ((isIrreducible_comp_iff _ f hf).mpr ht)

end Binary
section SimpleMatching
variable {G H : Type uG} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]

private theorem _root_.Langlands.FiniteTensor.FactorMatchingProof.binary_simple_matching
    {A : Rep.{uV} ℂ G} {B : Rep.{uV} ℂ H}
    {A' : Rep.{uW} ℂ G} {B' : Rep.{uW} ℂ H}
    (ha : IsAdmissible A.ρ) (hb : IsAdmissible B.ρ)
    (hi : A.ρ.IsIrreducible) (hj : B.ρ.IsIrreducible)
    (e : A.ρ.Equiv A'.ρ) (f : B.ρ.Equiv B'.ρ) :
    HaveSameJordanHolderFactors
      (Rep.of (Representation.tprod (A.ρ.comp (MonoidHom.fst G H))
        (B.ρ.comp (MonoidHom.snd G H))))
      (Rep.of (Representation.tprod (A'.ρ.comp (MonoidHom.fst G H))
        (B'.ρ.comp (MonoidHom.snd G H)))) :=
  haveSameJordanHolderFactors_of_isIrreducible
    (binary_irreducible A.ρ B.ρ ha hb hi hj)
    (tensorEquiv (equivComp e (MonoidHom.fst G H)) (equivComp f (MonoidHom.snd G H)))

variable [IsTopologicalGroup H]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem _root_.Langlands.FiniteTensor.FactorMatchingProof.simple_left_matching
    (hH : ∀ K : OpenSubgroup H, ∃ L : OpenSubgroup H, IsCompact (L : Set H) ∧ L ≤ K)
    {A : Rep.{uV} ℂ G} {B : Rep.{uV} ℂ H}
    {A' : Rep.{uW} ℂ G} {B' : Rep.{uW} ℂ H}
    (ha : IsAdmissible A.ρ) (hb : IsAdmissible B.ρ)
    (hi : A.ρ.IsIrreducible) (e : A.ρ.Equiv A'.ρ)
    (h : HaveSameJordanHolderFactors B B') :
    HaveSameJordanHolderFactors
      (Rep.of (Representation.tprod (A.ρ.comp (MonoidHom.fst G H))
        (B.ρ.comp (MonoidHom.snd G H))))
      (Rep.of (Representation.tprod (A'.ρ.comp (MonoidHom.fst G H))
        (B'.ρ.comp (MonoidHom.snd G H)))) := by
  obtain ⟨n, s, t, hs, ht, p, hp⟩ := h
  have hswap : HaveSameJordanHolderFactors
      (Rep.of (Representation.tprod (B.ρ.comp (MonoidHom.snd G H))
        (A.ρ.comp (MonoidHom.fst G H))))
      (Rep.of (Representation.tprod (B'.ρ.comp (MonoidHom.snd G H))
        (A'.ρ.comp (MonoidHom.fst G H)))) := by
    apply tensor_right_matching_of_graded
      (B := Rep.of (A.ρ.comp (MonoidHom.fst G H)))
      (B' := Rep.of (A'.ρ.comp (MonoidHom.fst G H)))
      (filtrationComp s (MonoidHom.snd G H) (fun b => ⟨(1, b), rfl⟩))
      (filtrationComp t (MonoidHom.snd G H) (fun b => ⟨(1, b), rfl⟩)) p
    intro i
    obtain ⟨f⟩ := hp i
    have hm := binary_simple_matching ha (graded_admissible hH s hb i) hi (hs i) e f
    apply haveSameJordanHolderFactors_transport hm
    · exact (Representation.TensorProduct.comm _ _).trans
        (tensorEquiv (gradedComp s (MonoidHom.snd G H) (fun b => ⟨(1, b), rfl⟩) i).symm
          (Representation.Equiv.refl _))
    · exact (Representation.TensorProduct.comm _ _).trans
        (tensorEquiv (gradedComp t (MonoidHom.snd G H) (fun b => ⟨(1, b), rfl⟩) (p i)).symm
          (Representation.Equiv.refl _))
  exact haveSameJordanHolderFactors_transport hswap (Representation.TensorProduct.comm _ _)
    (Representation.TensorProduct.comm _ _)

variable [IsTopologicalGroup G]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem _root_.Langlands.FiniteTensor.FactorMatchingProof.binary_matching
    (hG : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hH : ∀ K : OpenSubgroup H, ∃ L : OpenSubgroup H, IsCompact (L : Set H) ∧ L ≤ K)
    {A : Rep.{uV} ℂ G} {B : Rep.{uV} ℂ H}
    {A' : Rep.{uW} ℂ G} {B' : Rep.{uW} ℂ H}
    (ha : IsAdmissible A.ρ) (hb : IsAdmissible B.ρ)
    (hA : HaveSameJordanHolderFactors A A') (hB : HaveSameJordanHolderFactors B B') :
    HaveSameJordanHolderFactors
      (Rep.of (Representation.tprod (A.ρ.comp (MonoidHom.fst G H))
        (B.ρ.comp (MonoidHom.snd G H))))
      (Rep.of (Representation.tprod (A'.ρ.comp (MonoidHom.fst G H))
        (B'.ρ.comp (MonoidHom.snd G H)))) := by
  obtain ⟨n, s, t, hs, ht, p, hp⟩ := hA
  apply tensor_right_matching_of_graded
    (B := Rep.of (B.ρ.comp (MonoidHom.snd G H)))
    (B' := Rep.of (B'.ρ.comp (MonoidHom.snd G H)))
    (filtrationComp s (MonoidHom.fst G H) (fun a => ⟨(a, 1), rfl⟩))
    (filtrationComp t (MonoidHom.fst G H) (fun a => ⟨(a, 1), rfl⟩)) p
  intro i
  obtain ⟨e⟩ := hp i
  have hm := simple_left_matching hH (graded_admissible hG s ha i) hb (hs i) e hB
  apply haveSameJordanHolderFactors_transport hm
  · exact tensorEquiv (gradedComp s (MonoidHom.fst G H) (fun a => ⟨(a, 1), rfl⟩) i).symm
      (Representation.Equiv.refl _)
  · exact tensorEquiv (gradedComp t (MonoidHom.fst G H) (fun a => ⟨(a, 1), rfl⟩) (p i)).symm
      (Representation.Equiv.refl _)

end SimpleMatching
section Topology
private theorem _root_.Langlands.FiniteTensor.FactorMatchingProof.compactOpen_cofinal (G : Type uG) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [TotallyDisconnectedSpace G] :
    ∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ K ≤ H := by
  intro H
  obtain ⟨K, hKH, hK, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ H
  exact ⟨K, hK, hKH⟩

private theorem _root_.Langlands.FiniteTensor.FactorMatchingProof.fieldTotallyDisconnected {F : LocalFieldPackage.{uG}} (T : F.TopologicalData) :
    letI := T.topology
    TotallyDisconnectedSpace F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier using 1
    exact Valuation.toTopologicalSpace_eq (ValuativeRel.valuation F.Carrier)
  infer_instance

private theorem _root_.Langlands.FiniteTensor.FactorMatchingProof.generalLinearTotallyDisconnected {F : LocalFieldPackage.{uG}} (T : F.TopologicalData) (m : ℕ) :
    letI := T.topology
    TotallyDisconnectedSpace (GeneralLinear m F.Carrier) := by
  let := T.topology
  let := fieldTotallyDisconnected T
  let : TotallyDisconnectedSpace (Matrix (Fin m) (Fin m) F.Carrier) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin m → Fin m → F.Carrier))
  exact ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn
    Units.val_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

end Topology
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem _root_.Langlands.FiniteTensor.FactorMatchingProof.finite_matching :
    ∀ (r : ℕ) (H : Fin (r + 1) → Type uG) [∀ i, Group (H i)]
      [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)]
      [∀ i, T2Space (H i)] [∀ i, LocallyCompactSpace (H i)]
      [∀ i, TotallyDisconnectedSpace (H i)]
      (A : ∀ i, Rep.{uV} ℂ (H i)) (A' : ∀ i, Rep.{uW} ℂ (H i)),
      (∀ i, IsAdmissible (A i).ρ) →
      (∀ i, HaveSameJordanHolderFactors (A i) (A' i)) →
      HaveSameJordanHolderFactors
        (Rep.of (Langlands.FiniteTensor.external (fun i => (A i).ρ)))
        (Rep.of (Langlands.FiniteTensor.external (fun i => (A' i).ρ))) := by
  intro r
  induction r with
  | zero =>
      intro H _ _ _ _ _ _ A A' ha hm
      apply matching_of_comp (Langlands.FiniteTensor.evalOne H).symm
      exact haveSameJordanHolderFactors_transport (hm 0) (Langlands.FiniteTensor.singletonEquiv (fun i => (A i).ρ)).symm
        (Langlands.FiniteTensor.singletonEquiv (fun i => (A' i).ρ)).symm
  | succ r ih =>
      intro H _ _ _ _ _ _ A A' ha hm
      have htail := ih (fun j : Fin (r + 1) => H j.succ)
        (fun j => A j.succ) (fun j => A' j.succ)
        (fun j => ha j.succ) (fun j => hm j.succ)
      have htadm := Langlands.FiniteTensor.isAdmissible_external (fun j : Fin (r + 1) => (A j.succ).ρ)
        (fun j => ha j.succ)
      have hbin := binary_matching (compactOpen_cofinal (H 0))
        (compactOpen_cofinal (∀ j : Fin (r + 1), H j.succ)) (ha 0) htadm (hm 0) htail
      apply matching_of_comp (Langlands.FiniteTensor.headTail H).symm
      exact haveSameJordanHolderFactors_transport hbin (Langlands.FiniteTensor.headTailEquiv (fun i => (A i).ρ)).symm
        (Langlands.FiniteTensor.headTailEquiv (fun i => (A' i).ρ)).symm

end Langlands.AllFieldBZ.FiniteTensor.FactorMatchingProof
namespace Langlands.AllFieldBZ.FiniteTensor
open Langlands.FiniteTensor hiding PadicExternalTensorFactorsTheorem padicExternalTensorFactors
universe uF uV uW

open Langlands.FiniteTensor.FactorMatchingProof
open Langlands.GeneralLinear
/-- Factorwise matching preserves the actual Jordan–Hölder factors of the
finite external tensor over every positive-rank p-adic block Levi. -/
theorem padicExternalTensorFactors :
    PadicExternalTensorFactorsTheorem.{uF, uV, uW} := by
  intro F T n hn B
  let := T.topology
  intro A A' ha _ha' hm
  let (i : Fin B.length) :
      IsTopologicalGroup (GeneralLinear (B.size i) F.Carrier) :=
    T.generalLinearTopologicalGroup (B.size i)
  let (i : Fin B.length) : T2Space (GeneralLinear (B.size i) F.Carrier) :=
    T.generalLinearT2Space (B.size i)
  let (i : Fin B.length) :
      LocallyCompactSpace (GeneralLinear (B.size i) F.Carrier) :=
    T.generalLinearLocallyCompactSpace (B.size i)
  let (i : Fin B.length) :
      TotallyDisconnectedSpace (GeneralLinear (B.size i) F.Carrier) :=
    generalLinearTotallyDisconnected T (B.size i)
  have hf := finite_matching.{uF, uV, uW} B.length.pred
  have he : B.length.pred + 1 = B.length :=
    Nat.succ_pred_eq_of_pos (CuspidalSupport.length_pos_of_pos B hn)
  rw [he] at hf
  exact hf (fun i => GeneralLinear (B.size i) F.Carrier)
    (fun i => Rep.of (A i).representation) (fun i => Rep.of (A' i).representation) ha hm

end Langlands.AllFieldBZ.FiniteTensor
