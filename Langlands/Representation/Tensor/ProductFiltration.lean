import Langlands.Representation.Tensor.Filtration
import Langlands.Representation.Tensor.FiniteEquivalences
import Langlands.Representation.Filtration.ObjectTransport
import Langlands.Representation.Filtration.GradedRefinementProof
import Langlands.Representation.Filtration.IrreducibleMultiplicityProof

/-! Finite filtrations of binary and finite external tensor products. -/

noncomputable section

namespace Langlands.FiniteTensorFiltration

open LengthCriterionProof IntervalLiftProof

universe uK uG uA uB uV

section Equivalences

variable {k : Type uK} [CommRing k] {G : Type uG} [Monoid G]

/-- The tensor product of two actual representation equivalences. -/
def tprodCongr {V V' W W' : Type*} [AddCommGroup V] [Module k V] [AddCommGroup V']
    [Module k V'] [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']
    {ρ : Representation k G V} {ρ' : Representation k G V'}
    {σ : Representation k G W} {σ' : Representation k G W'}
    (e : ρ.Equiv ρ') (f : σ.Equiv σ') :
    (Representation.tprod ρ σ).Equiv (Representation.tprod ρ' σ') :=
  Representation.Equiv.mk (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv) (fun g => by
    apply TensorProduct.ext'
    intro v w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.congr_tmul,
      Representation.tprod_apply, TensorProduct.map_tmul]
    rw [Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply,
      Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply,
      e.toIntertwiningMap.isIntertwining, f.toIntertwiningMap.isIntertwining])

/-- Pull an actual representation equivalence back along a monoid homomorphism. -/
def compCongr {H : Type*} [Monoid H] {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) (φ : H →* G) : Representation.Equiv (ρ.comp φ) (σ.comp φ) :=
  Representation.Equiv.mk e.toLinearEquiv (fun h => e.isIntertwining' (φ h))

/-- Pulling back along an equivalence and then along its inverse changes nothing. -/
def compSymmComp {H : Type*} [Monoid H] {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (φ : H ≃* G) :
    Representation.Equiv ((ρ.comp φ.toMonoidHom).comp φ.symm.toMonoidHom) ρ :=
  Representation.Equiv.mk (LinearEquiv.refl k V) (fun g => by
    ext v
    simp)

/-- Equal indices of a filtration have equivalent graded pieces. -/
def gradedCongr {A : Rep.{uA} k G} {n : ℕ} (s : ObjectRepFiltration A n) {i j : Fin n}
    (h : i = j) : (s.gradedRepresentation i).ρ.Equiv (s.gradedRepresentation j).ρ := by
  subst h
  exact Representation.Equiv.refl _

end Equivalences

section External

variable {k : Type uK} [CommRing k] {ι : Type*} {H : ι → Type uG} [∀ i, Group (H i)]
  {V W : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]

/-- The external tensor product of a family of actual representation equivalences. -/
def externalCongr {ρ : ∀ i, Representation k (H i) (V i)}
    {σ : ∀ i, Representation k (H i) (W i)} (e : ∀ i, (ρ i).Equiv (σ i)) :
    (FiniteTensor.external ρ).Equiv (FiniteTensor.external σ) :=
  Representation.Equiv.mk (PiTensorProduct.congr fun i => (e i).toLinearEquiv) (fun g => by
    ext v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      FiniteTensor.external_tprod, PiTensorProduct.congr_tprod]
    congr 1
    funext i
    rw [Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply,
      (e i).toIntertwiningMap.isIntertwining])

end External

section Splice

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]

/-- Refine a supplied filtration by supplied filtrations of all its graded pieces.
No simplicity of any graded piece is required. -/
theorem exists_splice {A : Rep.{uA} k G} {n : ℕ} (f : ObjectRepFiltration A n)
    (m : Fin n → ℕ) (t : ∀ i, ObjectRepFiltration (f.gradedRepresentation i) (m i)) :
    ∃ (N : ℕ) (s : ObjectRepFiltration A N) (E : Fin N ≃ (Σ i, Fin (m i))),
      ∀ j, Nonempty ((s.gradedRepresentation j).ρ.Equiv
        ((t (E j).1).gradedRepresentation (E j).2).ρ) := by
  let r : SetRel (Subrepresentation A.ρ) (Subrepresentation A.ρ) :=
    {(X, Y) : Subrepresentation A.ρ × Subrepresentation A.ρ | X ≤ Y}
  let c : Fin n → RelSeries r := fun i =>
    ⟨m i, fun j => pull (f.subrepresentation i.castSucc) (f.subrepresentation i.succ)
      ((t i).subrepresentation j),
      fun j => pull_mono _ _ ((t i).monotone_subrepresentation (Fin.castSucc_le_succ j))⟩
  have hhead : ∀ i, (c i).head = f.subrepresentation i.castSucc := by
    intro i
    change pull _ _ ((t i).subrepresentation 0) = _
    rw [(t i).subrepresentation_zero]
    exact pull_bot (f.monotone_subrepresentation (Fin.castSucc_le_succ i))
  have hlast : ∀ i, (c i).last = f.subrepresentation i.succ := by
    intro i
    change pull _ _ ((t i).subrepresentation (Fin.last (m i))) = _
    rw [(t i).subrepresentation_last]
    exact pull_top _ _
  obtain ⟨d, hd0, hd1, e, he⟩ :=
    GradedRefinementProof.concatenate r n f.subrepresentation c hhead hlast
  let s : ObjectRepFiltration A d.length :=
    ObjectRepFiltration.ofSubrepresentations d
      (Fin.monotone_iff_le_succ.mpr (fun i => d.step i))
      (hd0.trans f.subrepresentation_zero) (hd1.trans f.subrepresentation_last)
  refine ⟨d.length, s, e, fun j => ?_⟩
  change Nonempty ((quotientRep (d j.castSucc) (d j.succ)).Equiv
    (quotientRep ((t (e j).1).subrepresentation (e j).2.castSucc)
      ((t (e j).1).subrepresentation (e j).2.succ)))
  rw [(he j).1, (he j).2]
  exact nonempty_quotient_pull_equiv _ _ _ _

end Splice

section Binary

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]

/-- Supplied filtrations of two factors give a filtration of their actual tensor
product whose graded pieces are the tensor products of pairs of graded pieces. -/
theorem exists_tprod {A : Rep.{uA} k G} {B : Rep.{uB} k G} {n m : ℕ}
    (s : ObjectRepFiltration A n) (t : ObjectRepFiltration B m) :
    ∃ (N : ℕ) (f : ObjectRepFiltration (Rep.of (Representation.tprod A.ρ B.ρ)) N)
      (E : Fin N ≃ Fin n × Fin m),
      ∀ j, Nonempty ((f.gradedRepresentation j).ρ.Equiv
        (Representation.tprod (s.gradedRepresentation (E j).1).ρ
          (t.gradedRepresentation (E j).2).ρ)) := by
  let u := s.tensorRight B
  let inner : ∀ a, ObjectRepFiltration (u.gradedRepresentation a) m := fun a =>
    LengthTwo.transport (s.tensorRightGradedEquiv B a).symm
      (t.tensorLeft (s.gradedRepresentation a))
  obtain ⟨N, f, E, hE⟩ := exists_splice u (fun _ => m) inner
  refine ⟨N, f, E.trans (Equiv.sigmaEquivProd _ _), fun j => ?_⟩
  obtain ⟨φ⟩ := hE j
  exact ⟨φ.trans (((t.tensorLeft (s.gradedRepresentation (E j).1)).equivTransportGradedEquiv
    (s.tensorRightGradedEquiv B (E j).1).symm (E j).2).symm.trans
      (t.tensorLeftGradedEquiv (s.gradedRepresentation (E j).1) (E j).2))⟩

end Binary

section Finite

variable {k : Type uK} [Field k]

/-- Supplied filtrations of finitely many factors give a filtration of their actual
external tensor product whose graded pieces are the external tensor products of the
chosen graded pieces, one from each factor, every choice occurring exactly once. -/
theorem exists_external : ∀ (K : ℕ) {H : Fin K → Type uG} [∀ i, Group (H i)]
    (A : ∀ i, Rep.{uV} k (H i)) (r : Fin K → ℕ) (s : ∀ i, ObjectRepFiltration (A i) (r i)),
    ∃ (N : ℕ) (f : ObjectRepFiltration (Rep.of (FiniteTensor.external fun i => (A i).ρ)) N)
      (E : Fin N ≃ ∀ i, Fin (r i)),
      ∀ j, Nonempty ((f.gradedRepresentation j).ρ.Equiv
        (FiniteTensor.external fun i => ((s i).gradedRepresentation (E j i)).ρ))
  | 0, H, _, A, r, s => by
    refine ⟨1, LengthTwo.oneStep _, Equiv.ofUnique _ _, fun j => ?_⟩
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    exact ⟨(IrreducibleMultiplicityProof.oneStepGradedEquiv
      (Rep.of (FiniteTensor.external fun i => (A i).ρ))).trans
        (externalCongr fun i => i.elim0)⟩
  | K + 1, H, _, A, r, s => by
    obtain ⟨N', f', E', hE'⟩ := exists_external K (fun j => A j.succ) (fun j => r j.succ)
      (fun j => s j.succ)
    let ρ : ∀ i, Representation k (H i) (A i) := fun i => (A i).ρ
    let fst := MonoidHom.fst (H 0) (∀ j : Fin K, H j.succ)
    let snd := MonoidHom.snd (H 0) (∀ j : Fin K, H j.succ)
    let hT := (FiniteTensor.headTail H).symm.symm.toMonoidHom
    obtain ⟨N, g, E2, hE2⟩ := exists_tprod ((s 0).comp fst) (f'.comp snd)
    let g1 : ObjectRepFiltration
        (Rep.of ((FiniteTensor.external ρ).comp (FiniteTensor.headTail H).symm.toMonoidHom)) N :=
      LengthTwo.transport (FiniteTensor.headTailEquiv ρ).symm g
    let g2 := g1.comp hT
    let c := compSymmComp (k := k) (FiniteTensor.external ρ) (FiniteTensor.headTail H).symm
    let f : ObjectRepFiltration (Rep.of (FiniteTensor.external ρ)) N :=
      LengthTwo.transport c g2
    let E : Fin N ≃ ∀ i, Fin (r i) :=
      E2.trans (((Equiv.refl _).prodCongr E').trans (Fin.consEquiv fun i => Fin (r i)))
    refine ⟨N, f, E, fun j => ?_⟩
    obtain ⟨φ⟩ := hE2 j
    obtain ⟨ψ⟩ := hE' (E2 j).2
    let τ : ∀ i, Representation k (H i) ((s i).gradedRepresentation (E j i)) :=
      fun i => ((s i).gradedRepresentation (E j i)).ρ
    have h0 : (E2 j).1 = E j 0 := by simp [E]
    have hsucc : ∀ j' : Fin K, E' (E2 j).2 j' = E j j'.succ := by simp [E]
    let χ : ((g.gradedRepresentation j).ρ).Equiv
        (Representation.tprod ((τ 0).comp fst)
          ((FiniteTensor.external fun j' : Fin K => τ j'.succ).comp snd)) :=
      φ.trans (tprodCongr
        ((((s 0).compGradedEquiv fst (E2 j).1)).trans
          (compCongr (gradedCongr (s 0) h0) fst))
        ((f'.compGradedEquiv snd (E2 j).2).trans
          (compCongr (ψ.trans (externalCongr fun j' => gradedCongr (s j'.succ) (hsucc j')))
            snd)))
    exact ⟨(g2.equivTransportGradedEquiv (B := Rep.of (FiniteTensor.external ρ)) c j).symm.trans
      ((g1.compGradedEquiv hT j).trans
        ((compCongr (g.equivTransportGradedEquiv (B := Rep.of ((FiniteTensor.external ρ).comp
          (FiniteTensor.headTail H).symm.toMonoidHom)) (FiniteTensor.headTailEquiv ρ).symm j).symm
          hT).trans
          ((compCongr χ hT).trans
            ((compCongr (FiniteTensor.headTailEquiv τ).symm hT).trans
              (compSymmComp (FiniteTensor.external τ) (FiniteTensor.headTail H).symm)))))⟩

end Finite

end Langlands.FiniteTensorFiltration
