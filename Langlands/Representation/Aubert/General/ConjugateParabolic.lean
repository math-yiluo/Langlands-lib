import Langlands.Representation.Aubert.General.Parabolic

/-! # Actual conjugate parabolic data -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uG uV

section Algebra

variable {G : Type uG} [Group G]

/-- The actual conjugate `g H g⁻¹`, specified by inverse-conjugation membership. -/
def conjugateSubgroup (g : G) (H : Subgroup G) : Subgroup G :=
  H.comap (MulAut.conj g⁻¹).toMonoidHom

@[simp]
theorem mem_conjugateSubgroup (g : G) (H : Subgroup G) (x : G) :
    x ∈ conjugateSubgroup g H ↔ g⁻¹ * x * g ∈ H := by
  simp [conjugateSubgroup]

/-- A literal conjugation-membership witness identifies the actual subgroup. -/
theorem conjugateSubgroup_eq (g : G) {M N : Subgroup G}
    (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M) :
    conjugateSubgroup g M = N := by
  ext x
  exact (mem_conjugateSubgroup g M x).trans (hMN x).symm

/-- Complementary subgroups remain complementary under a group isomorphism. -/
theorem isComplement'_comap_equiv {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) {M U : Subgroup K} (h : M.IsComplement' U) :
    (M.comap e.toMonoidHom).IsComplement' (U.comap e.toMonoidHom) := by
  constructor
  · intro a b hab
    have hab' : (e (a.1 : H), e (a.2 : H)) =
        (e (b.1 : H), e (b.2 : H)) := by
      let aK : M × U := (⟨e a.1, a.1.2⟩, ⟨e a.2, a.2.2⟩)
      let bK : M × U := (⟨e b.1, b.1.2⟩, ⟨e b.2, b.2.2⟩)
      have hh : aK = bK := h.1 (by
        simpa only [map_mul] using congrArg e hab)
      exact congrArg (fun q : M × U => ((q.1 : K), (q.2 : K))) hh
    exact Prod.ext (Subtype.ext (e.injective (congrArg Prod.fst hab')))
      (Subtype.ext (e.injective (congrArg Prod.snd hab')))
  · intro x
    obtain ⟨⟨m, u⟩, hmu⟩ := h.2 (e x)
    refine ⟨(⟨e.symm m, ?_⟩, ⟨e.symm u, ?_⟩), ?_⟩
    · change e (e.symm m) ∈ M
      simp
    · change e (e.symm u) ∈ U
      simp
    · apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using hmu

end Algebra

section Topology

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Conjugation preserves closedness of the actual subgroup. -/
theorem isClosed_conjugateSubgroup (g : G) {H : Subgroup G}
    (hH : IsClosed (H : Set G)) : IsClosed (conjugateSubgroup g H : Set G) := by
  have heq : (conjugateSubgroup g H : Set G) =
      (fun x : G => g⁻¹ * x * g) ⁻¹' (H : Set G) := by
    ext x
    exact mem_conjugateSubgroup g H x
  rw [heq]
  exact hH.preimage (by fun_prop)

/-- Conjugation transports the whole actual semidirect decomposition. -/
theorem IsSemidirectDecomposition.conjugate {P M U : Subgroup G}
    (h : IsSemidirectDecomposition P M U) (g : G) :
    IsSemidirectDecomposition (conjugateSubgroup g P)
      (conjugateSubgroup g M) (conjugateSubgroup g U) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (mem_conjugateSubgroup g P x).mpr
      (h.levi_le ((mem_conjugateSubgroup g M x).mp hx))
  · intro x hx
    exact (mem_conjugateSubgroup g P x).mpr
      (h.unipotent_le ((mem_conjugateSubgroup g U x).mp hx))
  · exact (Subgroup.comap_mono h.le_normalizer).trans
      (Subgroup.le_normalizer_comap (MulAut.conj g⁻¹).toMonoidHom)
  · let e := conjugationEquiv g (mem_conjugateSubgroup g P)
    have hcomap (H : Subgroup G) :
        (H.subgroupOf P).comap e.toMonoidHom =
          (conjugateSubgroup g H).subgroupOf (conjugateSubgroup g P) := by
      ext x
      change g⁻¹ * (x : G) * g ∈ H ↔
        g⁻¹ * (x : G) * g⁻¹⁻¹ ∈ H
      rw [inv_inv]
    simpa only [hcomap] using isComplement'_comap_equiv e.toMulEquiv h.isComplement'

/-- The transported decomposition with any actual Levi identified by the literal
inverse-conjugation membership condition. -/
theorem IsSemidirectDecomposition.conjugateWithLevi {P M U N : Subgroup G}
    (h : IsSemidirectDecomposition P M U) (g : G)
    (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M) :
    IsSemidirectDecomposition (conjugateSubgroup g P) N (conjugateSubgroup g U) := by
  rw [← conjugateSubgroup_eq g hMN]
  exact h.conjugate g

end Topology

end Langlands.Aubert.General
