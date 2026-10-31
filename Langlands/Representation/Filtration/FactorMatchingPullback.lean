import Langlands.Representation.Filtration.JordanHolderTransportProof
import Langlands.Representation.CuspidalSupport.AssociationReduction

/-! # Pullback of matching Jordan–Hölder factors

Generic helpers relocated from the finite tensor matching proof.
-/

namespace Langlands.FiniteTensor.FactorMatchingProof

open CuspidalSupport

universe uK uG uH uV uW

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
variable {H : Type uH} [Monoid H]

def filtrationComp {A : Rep.{uV} k G} {n : ℕ}
    (s : ObjectRepFiltration A n) (f : H →* G) (hf : Function.Surjective f) :
    ObjectRepFiltration (Rep.of (A.ρ.comp f)) n :=
  let e := (subrepresentationCompOrderIso A.ρ f hf).symm
  ObjectRepFiltration.ofSubrepresentations
    (fun i => e (s.subrepresentation i))
    (e.monotone.comp s.monotone_subrepresentation)
    (by rw [s.subrepresentation_zero]; exact e.map_bot)
    (by rw [s.subrepresentation_last]; exact e.map_top)

def gradedComp {A : Rep.{uV} k G} {n : ℕ}
    (s : ObjectRepFiltration A n) (f : H →* G) (hf : Function.Surjective f)
    (i : Fin n) :
    ((filtrationComp s f hf).gradedRepresentation i).ρ.Equiv
      ((s.gradedRepresentation i).ρ.comp f) :=
  Representation.Equiv.mk (LinearEquiv.refl k _) (fun _ => rfl)

def equivComp {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) (f : H →* G) : Representation.Equiv (ρ.comp f) (σ.comp f) :=
  Representation.Equiv.mk e.toLinearEquiv (fun h => e.isIntertwining' (f h))

theorem matching_comp {A : Rep.{uV} k G} {B : Rep.{uW} k G}
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

theorem matching_of_comp {A : Rep.{uV} k G} {B : Rep.{uW} k G}
    (e : H ≃* G)
    (h : HaveSameJordanHolderFactors
      (Rep.of (A.ρ.comp e.toMonoidHom)) (Rep.of (B.ρ.comp e.toMonoidHom))) :
    HaveSameJordanHolderFactors A B := by
  have h' := matching_comp h e.symm.toMonoidHom e.symm.surjective
  apply haveSameJordanHolderFactors_transport h'
  · exact Representation.Equiv.mk (LinearEquiv.refl k _) (by
      intro g
      change A.ρ (e (e.symm g)) = A.ρ g
      rw [e.apply_symm_apply])
  · exact Representation.Equiv.mk (LinearEquiv.refl k _) (by
      intro g
      change B.ρ (e (e.symm g)) = B.ρ g
      rw [e.apply_symm_apply])

end Langlands.FiniteTensor.FactorMatchingProof
