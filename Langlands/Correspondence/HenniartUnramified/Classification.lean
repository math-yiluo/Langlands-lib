import Langlands.Correspondence.HenniartUnramified.Types

/-! # Representations attached to inertia types of finite period -/

noncomputable section

namespace Langlands.FiniteRepresentation.SplitDegree

open Representation

universe uG uH uV uW

theorem nontrivial_of_isIrreducible {J : Type*} [Group J] {V : Type uV} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ J V) (h : ρ.IsIrreducible) : Nontrivial V := by
  let := h
  exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ J) ρ.asModule

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {D : SplitDegree G}
variable {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {E : SplitDegree H}
variable {m : ℕ}

namespace Stage

variable (S : Stage D E (m + 1))

section Period

variable (A : {A : FiniteRepresentation.{0, uG, uW} ℂ D.inertia // D.IsType A})
  (hp : Function.minimalPeriod (D.conjType 1) (D.toClass A) = m + 1)

include hp in
theorem exists_stageRep :
    ∃ τ : Representation ℂ H A.1, S.block τ 0 = A.1.representation ∧
      τ.comp E.inertia.subtype = A.1.representation.comp S.ιJ ∧
      (FiniteRepresentation.of τ).IsContinuous := by
  obtain ⟨τ, h1, h2, h3⟩ :=
    S.exists_extension A.1.representation (conj_equiv_of_minimalPeriod A hp).some
  exact ⟨τ, h1, h2, h3 A.2.1⟩

/-- A stage extension of a type of minimal period `m + 1`. -/
def stageRep : Representation ℂ H A.1 := Classical.choose (S.exists_stageRep A hp)

theorem block_stageRep : S.block (S.stageRep A hp) 0 = A.1.representation :=
  (Classical.choose_spec (S.exists_stageRep A hp)).1

theorem continuous_stageRep : (FiniteRepresentation.of (S.stageRep A hp)).IsContinuous :=
  (Classical.choose_spec (S.exists_stageRep A hp)).2.2

theorem block_stageRep_eq (k : ℕ) :
    S.block (S.stageRep A hp) k = A.1.representation.comp (D.cj k) := by
  rw [block_eq_comp, block_stageRep]

theorem stageRep_hirr : ∀ k : Fin (m + 1), (S.block (S.stageRep A hp) k).IsIrreducible := by
  intro k
  rw [block_stageRep_eq]
  exact (D.conjObj k A).2.2

theorem stageRep_hdist : ∀ j k : Fin (m + 1), j ≠ k →
    ∀ T : (S.block (S.stageRep A hp) j).IntertwiningMap (S.block (S.stageRep A hp) k), T = 0 := by
  intro j k hjk
  rw [block_stageRep_eq, block_stageRep_eq]
  exact conj_dist_of_minimalPeriod A hp j k hjk

/-- The coinduction attached to a type of minimal period `m + 1`. -/
def typeCoind : Representation ℂ G (Fin (m + 1) → A.1) := S.coind (S.stageRep A hp)

theorem typeCoind_isIrreducible : (S.typeCoind A hp).IsIrreducible := by
  have := nontrivial_of_isIrreducible _ A.2.2
  exact S.coind_isIrreducible _ (S.stageRep_hirr A hp) (S.stageRep_hdist A hp)

theorem typeCoind_continuous : (FiniteRepresentation.of (S.typeCoind A hp)).IsContinuous :=
  S.continuous_coind _ (S.continuous_stageRep A hp)

theorem typeCoind_twist_iff (u : ℂˣ) :
    Nonempty (Representation.Equiv
      (Langlands.twist (Weil.Local.unramifiedCharacter D.degree u).toMonoidHom (S.typeCoind A hp))
      (S.typeCoind A hp)) ↔ u ^ (m + 1) = 1 := by
  have := nontrivial_of_isIrreducible _ A.2.2
  constructor
  · rintro ⟨e⟩
    exact S.pow_eq_one_of_twist_equiv _ (S.stageRep_hirr A hp) (S.stageRep_hdist A hp) u e
  · exact S.twist_equiv_of_pow_eq_one _ u

omit [IsTopologicalGroup G] in
theorem finrank_typeCoind :
    Module.finrank ℂ (Fin (m + 1) → A.1) = (m + 1) * Module.finrank ℂ A.1 := by
  rw [Module.finrank_pi_fintype]
  simp

/-- The coordinate projection to the `k`th conjugate type. -/
def projType (k : Fin (m + 1)) : Representation.IntertwiningMap
    ((S.typeCoind A hp).comp D.inertia.subtype) (D.conjObj k A).1.representation :=
  ⟨LinearMap.proj k, fun n => by
    apply LinearMap.ext
    intro v
    change (S.coind (S.stageRep A hp) n v) k = A.1.representation (D.cj k n) (v k)
    rw [coind_inertia, inertiaRep_apply, ← block_apply, block_stageRep_eq]
    rfl⟩

theorem projType_ne_zero (k : Fin (m + 1)) : S.projType A hp k ≠ 0 := by
  have := nontrivial_of_isIrreducible _ A.2.2
  intro h
  obtain ⟨a, ha⟩ := exists_ne (0 : A.1)
  apply ha
  have h1 := congrArg (fun F : Representation.IntertwiningMap _ _ => F (Pi.single k a)) h
  have h2 : (Pi.single k a : Fin (m + 1) → A.1) k = 0 := h1
  simpa using h2

/-- Every irreducible representation containing the type is a twist of the coinduction. -/
theorem twist_equiv_typeCoind {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    [FiniteDimensional ℂ V'] (σ' : Representation ℂ G V') (hσ' : σ'.IsIrreducible)
    (P : Representation.IntertwiningMap (σ'.comp D.inertia.subtype) A.1.representation)
    (hP : P ≠ 0) :
    ∃ u : ℂˣ, Nonempty (Representation.Equiv
      (Langlands.twist (Weil.Local.unramifiedCharacter D.degree u).toMonoidHom σ')
      (S.typeCoind A hp)) := by
  have := nontrivial_of_isIrreducible _ A.2.2
  let P' : Representation.IntertwiningMap (σ'.comp D.inertia.subtype)
      (S.block (S.stageRep A hp) 0) :=
    ⟨P.toLinearMap, fun n => by rw [S.block_stageRep A hp]; exact P.isIntertwining' n⟩
  have hP' : P' ≠ 0 := by
    intro h0
    have h1 := congrArg Representation.IntertwiningMap.toLinearMap h0
    exact hP (Representation.IntertwiningMap.ext h1)
  exact S.twist_equiv_coind_of_occurs _ (S.stageRep_hirr A hp) (S.stageRep_hdist A hp) σ' hσ'
    P' hP'

/-- The types occurring in the coinduction are the conjugates of the given type. -/
theorem occurs_typeCoind (B : {B : FiniteRepresentation.{0, uG, uW} ℂ D.inertia // D.IsType B})
    (Q : Representation.IntertwiningMap ((S.typeCoind A hp).comp D.inertia.subtype)
      B.1.representation) (hQ : Q ≠ 0) :
    ∃ k : Fin (m + 1), D.toClass B = D.conjType k (D.toClass A) := by
  obtain ⟨k, ⟨e⟩⟩ := exists_block_equiv (fun k : Fin (m + 1) => S.block (S.stageRep A hp) k)
    B.1.representation B.2.2 (S.stageRep_hirr A hp) Q.toLinearMap
    (fun n => by
      have := Q.isIntertwining' n
      change Q.toLinearMap ∘ₗ S.coind (S.stageRep A hp) n =
        B.1.representation n ∘ₗ Q.toLinearMap at this
      rw [coind_inertia] at this
      exact this)
    (fun h0 => hQ (Representation.IntertwiningMap.ext h0))
  refine ⟨k, ?_⟩
  rw [conjType_mk]
  apply ((D.toClass_eq_iff _ _).mpr _).symm
  rw [conjObj_representation, ← S.block_stageRep_eq A hp]
  exact ⟨e⟩

theorem typeCoind_trivial_iff (N : Subgroup G) [N.Normal] :
    (∀ n : D.inertia, (n : G) ∈ N → S.typeCoind A hp n = 1) ↔
      (∀ n : D.inertia, (n : G) ∈ N → A.1.representation n = 1) := by
  rw [typeCoind, coind_trivial_iff, block_stageRep]

end Period

section Fixed

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The type of a stage representation is fixed by conjugation with `lift ^ (m + 1)`. -/
def blockConjEquiv (τ : Representation ℂ H V) :
    Representation.Equiv (S.block τ 0) ((S.block τ 0).comp (D.cj (m + 1))) :=
  Representation.Equiv.mk (LinearMap.GeneralLinearGroup.toLinearEquiv (τ.asGroupHom E.lift))
    fun n => by
    apply LinearMap.ext
    intro v
    change τ E.lift (τ (S.κ (D.cj 0 n)) v) = τ (S.κ (D.cj 0 (D.cj (m + 1) n))) (τ E.lift v)
    rw [cj_zero, cj_zero, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
      S.κ_conj_lift]

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- A stage representation whose inertia restriction is irreducible has an irreducible type. -/
theorem block_isIrreducible (τ : Representation ℂ H V)
    (hτ : Representation.IsIrreducible (τ.comp E.inertia.subtype)) :
    (S.block τ 0).IsIrreducible := by
  have h : S.block τ 0 = (τ.comp E.inertia.subtype).comp S.κJ := by
    ext n : 1
    simp [cj_zero]
  rw [h]
  exact isIrreducible_comp_surjective _ _ (fun h => ⟨S.ιJ h, S.κJ_ιJ h⟩) hτ

end Fixed

end Stage

end Langlands.FiniteRepresentation.SplitDegree
