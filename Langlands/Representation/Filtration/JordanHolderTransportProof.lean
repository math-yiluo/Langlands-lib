import Langlands.Representation.Filtration.JordanHolderStatement
import Langlands.Representation.Filtration.LengthCriterionProof

/-! Transport of a supplied actual Jordan–Hölder series along an equivalence. -/

namespace Langlands

universe uK uG uA uB uC uD

namespace JordanHolderTransportProof

open LengthCriterionProof

section Equiv

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
  {V : Type uA} [AddCommGroup V] [Module k V] {ρ : Representation k G V}
  {W : Type uB} [AddCommGroup W] [Module k W] {σ : Representation k G W}

theorem equiv_apply_rep (φ : ρ.Equiv σ) (g : G) (v : V) :
    φ.toLinearEquiv (ρ g v) = σ g (φ.toLinearEquiv v) :=
  LinearMap.congr_fun (φ.isIntertwining' g) v

/-- The image of an invariant subspace under an equivalence of representations. -/
def mapSub (φ : ρ.Equiv σ) (S : Subrepresentation ρ) : Subrepresentation σ where
  toSubmodule := S.toSubmodule.map (φ.toLinearEquiv : V →ₗ[k] W)
  apply_mem_toSubmodule g := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, S.apply_mem_toSubmodule g hv, equiv_apply_rep φ g v⟩

theorem mem_mapSub_iff (φ : ρ.Equiv σ) (S : Subrepresentation ρ) {w : W} :
    w ∈ mapSub φ S ↔ φ.toLinearEquiv.symm w ∈ S :=
  Submodule.mem_map_equiv S.toSubmodule

/-- Taking images is an isomorphism of invariant-subspace lattices. -/
def subrepOrderIso (φ : ρ.Equiv σ) : Subrepresentation ρ ≃o Subrepresentation σ where
  toFun := mapSub φ
  invFun := mapSub φ.symm
  left_inv S := by
    apply SetLike.ext
    intro v
    rw [mem_mapSub_iff, mem_mapSub_iff]
    change φ.toLinearEquiv.symm (φ.toLinearEquiv v) ∈ S ↔ v ∈ S
    rw [LinearEquiv.symm_apply_apply]
  right_inv U := by
    apply SetLike.ext
    intro w
    rw [mem_mapSub_iff, mem_mapSub_iff]
    change φ.toLinearEquiv (φ.toLinearEquiv.symm w) ∈ U ↔ w ∈ U
    rw [LinearEquiv.apply_symm_apply]
  map_rel_iff' {S T} := by
    constructor
    · intro h v hv
      have hv' : φ.toLinearEquiv v ∈ mapSub φ T := h ⟨v, hv, rfl⟩
      rw [mem_mapSub_iff, LinearEquiv.symm_apply_apply] at hv'
      exact hv'
    · rintro h _ ⟨v, hv, rfl⟩
      exact ⟨v, h hv, rfl⟩

@[simp]
theorem subrepOrderIso_apply (φ : ρ.Equiv σ) (S : Subrepresentation ρ) :
    subrepOrderIso φ S = mapSub φ S := rfl

/-- The upper invariant subspace and its image are linearly equivalent. -/
abbrev upperEquiv (φ : ρ.Equiv σ) (T : Subrepresentation ρ) :
    T.toSubmodule ≃ₗ[k] (mapSub φ T).toSubmodule :=
  φ.toLinearEquiv.submoduleMap T.toSubmodule

theorem map_lower (φ : ρ.Equiv σ) (S T : Subrepresentation ρ) :
    (lower S T).map (upperEquiv φ T : T.toSubmodule →ₗ[k] (mapSub φ T).toSubmodule) =
      lower (mapSub φ S) (mapSub φ T) := by
  ext y
  rw [Submodule.mem_map_equiv]
  exact (mem_mapSub_iff φ S).symm

/-- The image of each successive quotient under an equivalence is equivariantly
isomorphic to the original successive quotient. -/
noncomputable def quotientEquiv (φ : ρ.Equiv σ) (S T : Subrepresentation ρ) :
    (quotientRep S T).Equiv (quotientRep (mapSub φ S) (mapSub φ T)) :=
  Representation.Equiv.mk
    (Submodule.Quotient.equiv (lower S T) (lower (mapSub φ S) (mapSub φ T))
      (upperEquiv φ T) (map_lower φ S T))
    (by
      intro g
      apply Submodule.linearMap_qext
      apply LinearMap.ext
      intro x
      change (lower (mapSub φ S) (mapSub φ T)).mkQ (upperEquiv φ T (T.toRepresentation g x)) =
        (lower (mapSub φ S) (mapSub φ T)).mkQ
          ((mapSub φ T).toRepresentation g (upperEquiv φ T x))
      congr 1
      exact Subtype.ext (equiv_apply_rep φ g x))

end Equiv

end JordanHolderTransportProof

open JordanHolderTransportProof LengthCriterionProof

/-- An equivalence carries a supplied actual composition series to its image series,
with an actual equivariant isomorphism of graded quotients at every index. -/
theorem jordanHolderSeriesTransport : JordanHolderSeriesTransportStatement.{uK, uG, uA, uB} := by
  intro k _ G _ A B φ n s hs
  let e := subrepOrderIso φ
  let t : ObjectRepFiltration B n :=
    ObjectRepFiltration.ofSubrepresentations (fun i => e (s.subrepresentation i))
      (e.monotone.comp s.monotone_subrepresentation)
      (by
        change e (s.subrepresentation 0) = ⊥
        rw [s.subrepresentation_zero]
        exact e.map_bot)
      (by
        change e (s.subrepresentation (Fin.last n)) = ⊤
        rw [s.subrepresentation_last]
        exact e.map_top)
  refine ⟨t, (hasSimpleFactors_iff_covBy t).mpr fun i => ?_, fun i => ?_⟩
  · exact (apply_covBy_apply_iff e).mpr ((hasSimpleFactors_iff_covBy s).mp hs i)
  · exact ⟨quotientEquiv φ (s.subrepresentation i.castSucc) (s.subrepresentation i.succ)⟩

/-- Transport matching composition series along two actual representation equivalences. -/
theorem haveSameJordanHolderFactors_transport
    {k : Type uK} [Field k] {G : Type uG} [Monoid G]
    {A : Rep.{uA} k G} {B : Rep.{uB} k G}
    {C : Rep.{uC} k G} {D : Rep.{uD} k G}
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

end Langlands
