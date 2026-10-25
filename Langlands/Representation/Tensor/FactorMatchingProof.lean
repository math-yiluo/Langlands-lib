import Langlands.Representation.Tensor.Filtration
import Langlands.Representation.Tensor.FactorMatchingStatement
import Langlands.Representation.Tensor.FiniteProperties
import Langlands.Representation.Tensor.FiniteEquivalences
import Langlands.Representation.Filtration.GradedRefinementProof
import Langlands.Representation.Filtration.JordanHolderProof
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Hecke.CommonInvarianceProof
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

namespace Langlands.FiniteTensor.FactorMatchingProof

open CuspidalSupport

universe uK uG uH uV uW uX uY

section Algebra

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]

private theorem matching_transport {A : Rep.{uV} k G} {B : Rep.{uW} k G}
    {C : Rep.{uX} k G} {D : Rep.{uY} k G}
    (h : HaveSameJordanHolderFactors A B)
    (e : A.ρ.Equiv C.ρ) (f : B.ρ.Equiv D.ρ) :
    HaveSameJordanHolderFactors C D := by
  obtain ⟨n, s, t, hs, ht, p, hp⟩ := h
  obtain ⟨s', hs', es⟩ := jordanHolderSeriesTransport k G A C e n s hs
  obtain ⟨t', ht', et⟩ := jordanHolderSeriesTransport k G B D f n t ht
  refine ⟨n, s', t', hs', ht', p, ?_⟩
  intro i
  obtain ⟨a⟩ := es i
  obtain ⟨b⟩ := hp i
  obtain ⟨c⟩ := et (p i)
  exact ⟨(a.symm.trans b).trans c⟩

variable {H : Type uH} [Monoid H]

private def filtrationComp {A : Rep.{uV} k G} {n : ℕ}
    (s : ObjectRepFiltration A n) (f : H →* G) (hf : Function.Surjective f) :
    ObjectRepFiltration (Rep.of (A.ρ.comp f)) n :=
  let e := (subrepresentationCompOrderIso A.ρ f hf).symm
  ObjectRepFiltration.ofSubrepresentations
    (fun i => e (s.subrepresentation i))
    (e.monotone.comp s.monotone_subrepresentation)
    (by rw [s.subrepresentation_zero]; exact e.map_bot)
    (by rw [s.subrepresentation_last]; exact e.map_top)

private def gradedComp {A : Rep.{uV} k G} {n : ℕ}
    (s : ObjectRepFiltration A n) (f : H →* G) (hf : Function.Surjective f)
    (i : Fin n) :
    ((filtrationComp s f hf).gradedRepresentation i).ρ.Equiv
      ((s.gradedRepresentation i).ρ.comp f) :=
  Representation.Equiv.mk (LinearEquiv.refl k _) (fun _ => rfl)

private def equivComp {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) (f : H →* G) : Representation.Equiv (ρ.comp f) (σ.comp f) :=
  Representation.Equiv.mk e.toLinearEquiv (fun h => e.isIntertwining' (f h))

private theorem matching_comp {A : Rep.{uV} k G} {B : Rep.{uW} k G}
    (h : HaveSameJordanHolderFactors A B) (f : H →* G) (hf : Function.Surjective f) :
    HaveSameJordanHolderFactors (Rep.of (A.ρ.comp f)) (Rep.of (B.ρ.comp f)) := by
  obtain ⟨n, s, t, hs, ht, p, hp⟩ := h
  refine ⟨n, filtrationComp s f hf, filtrationComp t f hf, ?_, ?_, p, ?_⟩
  · intro i
    exact (JordanHolderTransportProof.subrepOrderIso (gradedComp s f hf i)).isSimpleOrder_iff.mpr
      ((isIrreducible_comp_iff _ f hf).mpr (hs i))
  · intro i
    exact (JordanHolderTransportProof.subrepOrderIso (gradedComp t f hf i)).isSimpleOrder_iff.mpr
      ((isIrreducible_comp_iff _ f hf).mpr (ht i))
  · intro i
    obtain ⟨e⟩ := hp i
    exact ⟨((gradedComp s f hf i).trans (equivComp e f)).trans
      (gradedComp t f hf (p i)).symm⟩

private theorem matching_of_comp {A : Rep.{uV} k G} {B : Rep.{uW} k G}
    (e : H ≃* G)
    (h : HaveSameJordanHolderFactors
      (Rep.of (A.ρ.comp e.toMonoidHom)) (Rep.of (B.ρ.comp e.toMonoidHom))) :
    HaveSameJordanHolderFactors A B := by
  have h' := matching_comp h e.symm.toMonoidHom e.symm.surjective
  apply matching_transport h'
  · exact Representation.Equiv.mk (LinearEquiv.refl k _) (by
      intro g
      change A.ρ (e (e.symm g)) = A.ρ g
      rw [e.apply_symm_apply])
  · exact Representation.Equiv.mk (LinearEquiv.refl k _) (by
      intro g
      change B.ρ (e (e.symm g)) = B.ρ g
      rw [e.apply_symm_apply])

private noncomputable def tensorEquiv
    {V : Type uV} {W : Type uW} {X : Type uX} {Y : Type uY}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    {ρ : Representation k G V} {σ : Representation k G W}
    {τ : Representation k G X} {υ : Representation k G Y}
    (e : ρ.Equiv σ) (f : τ.Equiv υ) :
    (Representation.tprod ρ τ).Equiv (Representation.tprod σ υ) :=
  Representation.Equiv.mk (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv)
    (fun g => (e.toIntertwiningMap.tensor f.toIntertwiningMap).isIntertwining' g)

private theorem tensor_right_matching_of_graded
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
  exact matching_transport (h i) (s.tensorRightGradedEquiv B i).symm
    (t.tensorRightGradedEquiv B' (p i)).symm

end Algebra

section Admissible

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem graded_admissible
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

private abbrev pairType (X Y : Type uV) : PUnit.{1} ⊕ PUnit.{1} → Type uV :=
  Sum.elim (fun _ => X) (fun _ => Y)

private instance pairGroup (X Y : Type uG) [Group X] [Group Y] (i) :
    Group (pairType X Y i) :=
  Sum.rec (fun _ => (inferInstance : Group X)) (fun _ => (inferInstance : Group Y)) i

private instance pairAddCommGroup (X Y : Type uV) [AddCommGroup X] [AddCommGroup Y] (i) :
    AddCommGroup (pairType X Y i) :=
  Sum.rec (fun _ => (inferInstance : AddCommGroup X)) (fun _ => (inferInstance : AddCommGroup Y)) i

private instance pairModule (X Y : Type uV) [AddCommGroup X] [AddCommGroup Y]
    [Module ℂ X] [Module ℂ Y] (i) : Module ℂ (pairType X Y i) :=
  Sum.rec (fun _ => (inferInstance : Module ℂ X)) (fun _ => (inferInstance : Module ℂ Y)) i

variable {G H : Type uG} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  {V W : Type uV} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

set_option backward.isDefEq.respectTransparency false in
private theorem binary_irreducible
    (ρ : Representation ℂ G V) (σ : Representation ℂ H W)
    (ha : IsAdmissible ρ) (hb : IsAdmissible σ)
    (hi : ρ.IsIrreducible) (hj : σ.IsIrreducible) :
    (Representation.tprod (ρ.comp (MonoidHom.fst G H))
      (σ.comp (MonoidHom.snd G H))).IsIrreducible := by
  let τ : ∀ i, Representation ℂ ((pairType G H) i) ((pairType V W) i) := Sum.rec (fun _ => ρ) (fun _ => σ)
  let : ∀ i, (τ i).IsIrreducible := Sum.rec (fun _ => hi) (fun _ => hj)
  have ht := isIrreducible_external τ (by
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
  let e : Representation.Equiv ((external τ).comp f)
      (Representation.tprod (ρ.comp (MonoidHom.fst G H))
        (σ.comp (MonoidHom.snd G H))) :=
    Representation.Equiv.mk L (fun g => by
      ext v
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, MonoidHom.comp_apply, external_tprod, hL,
        Representation.tprod_apply, TensorProduct.map_tmul]
      rfl)
  exact (JordanHolderTransportProof.subrepOrderIso e).isSimpleOrder_iff.mp
    ((isIrreducible_comp_iff _ f hf).mpr ht)

end Binary

section SimpleMatching

variable {G H : Type uG} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]

private theorem binary_simple_matching
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
private theorem simple_left_matching
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
    apply matching_transport hm
    · exact (Representation.TensorProduct.comm _ _).trans
        (tensorEquiv (gradedComp s (MonoidHom.snd G H) (fun b => ⟨(1, b), rfl⟩) i).symm
          (Representation.Equiv.refl _))
    · exact (Representation.TensorProduct.comm _ _).trans
        (tensorEquiv (gradedComp t (MonoidHom.snd G H) (fun b => ⟨(1, b), rfl⟩) (p i)).symm
          (Representation.Equiv.refl _))
  exact matching_transport hswap (Representation.TensorProduct.comm _ _)
    (Representation.TensorProduct.comm _ _)

variable [IsTopologicalGroup G]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem binary_matching
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
  apply matching_transport hm
  · exact tensorEquiv (gradedComp s (MonoidHom.fst G H) (fun a => ⟨(a, 1), rfl⟩) i).symm
      (Representation.Equiv.refl _)
  · exact tensorEquiv (gradedComp t (MonoidHom.fst G H) (fun a => ⟨(a, 1), rfl⟩) (p i)).symm
      (Representation.Equiv.refl _)

end SimpleMatching

section Topology

private theorem compactOpen_cofinal (G : Type uG) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [TotallyDisconnectedSpace G] :
    ∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ K ≤ H := by
  intro H
  obtain ⟨K, hKH, hK, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ H
  exact ⟨K, hK, hKH⟩

private theorem fieldTotallyDisconnected {p : ℕ} [Fact p.Prime]
    {F : PadicField.{uG} p} (T : F.TopologicalData) :
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

private theorem generalLinearTotallyDisconnected {p : ℕ} [Fact p.Prime]
    {F : PadicField.{uG} p} (T : F.TopologicalData) (m : ℕ) :
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
private theorem finite_matching :
    ∀ (r : ℕ) (H : Fin (r + 1) → Type uG) [∀ i, Group (H i)]
      [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)]
      [∀ i, T2Space (H i)] [∀ i, LocallyCompactSpace (H i)]
      [∀ i, TotallyDisconnectedSpace (H i)]
      (A : ∀ i, Rep.{uV} ℂ (H i)) (A' : ∀ i, Rep.{uW} ℂ (H i)),
      (∀ i, IsAdmissible (A i).ρ) →
      (∀ i, HaveSameJordanHolderFactors (A i) (A' i)) →
      HaveSameJordanHolderFactors
        (Rep.of (external (fun i => (A i).ρ)))
        (Rep.of (external (fun i => (A' i).ρ))) := by
  intro r
  induction r with
  | zero =>
      intro H _ _ _ _ _ _ A A' ha hm
      apply matching_of_comp (evalOne H).symm
      exact matching_transport (hm 0) (singletonEquiv (fun i => (A i).ρ)).symm
        (singletonEquiv (fun i => (A' i).ρ)).symm
  | succ r ih =>
      intro H _ _ _ _ _ _ A A' ha hm
      have htail := ih (fun j : Fin (r + 1) => H j.succ)
        (fun j => A j.succ) (fun j => A' j.succ)
        (fun j => ha j.succ) (fun j => hm j.succ)
      have htadm := isAdmissible_external (fun j : Fin (r + 1) => (A j.succ).ρ)
        (fun j => ha j.succ)
      have hbin := binary_matching (compactOpen_cofinal (H 0))
        (compactOpen_cofinal (∀ j : Fin (r + 1), H j.succ)) (ha 0) htadm (hm 0) htail
      apply matching_of_comp (headTail H).symm
      exact matching_transport hbin (headTailEquiv (fun i => (A i).ρ)).symm
        (headTailEquiv (fun i => (A' i).ρ)).symm

end Langlands.FiniteTensor.FactorMatchingProof

namespace Langlands.FiniteTensor

universe uF uV uW

open FactorMatchingProof GeneralLinear

/-- Factorwise matching preserves the actual Jordan–Hölder factors of the
finite external tensor over every positive-rank p-adic block Levi. -/
theorem padicExternalTensorFactors :
    PadicExternalTensorFactorsTheorem.{uF, uV, uW} := by
  intro p _ F T n hn B
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

end Langlands.FiniteTensor
