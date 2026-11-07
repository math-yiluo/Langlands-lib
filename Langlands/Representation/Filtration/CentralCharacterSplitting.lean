import Langlands.Representation.Filtration.CentralEigenspaceSplitting
import Langlands.Representation.Exponents.Central
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Splitting an actual finite filtration with distinct central characters. -/

noncomputable section

open CategoryTheory

namespace Langlands.CentralCharacterSplitting

universe uK uG uV

variable {k : Type uK} [Field k] {G : Type uG} [Group G]

/-- The action of the multiplicative monoid of the group algebra. -/
def algebraRepresentation {V : Type uV} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : Representation k (MonoidAlgebra k G) V :=
  ρ.asAlgebraHom.toMonoidHom

/-- An invariant subspace is stable under every group-algebra operator. -/
def algebraSubrepresentation {V : Type uV} [AddCommGroup V] [Module k V]
    {ρ : Representation k G V} (S : Subrepresentation ρ) :
    Subrepresentation (algebraRepresentation ρ) where
  toSubmodule := S.toSubmodule
  apply_mem_toSubmodule x v hv := by
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp [algebraRepresentation]
    | add x y hx hy =>
        simpa [algebraRepresentation] using S.toSubmodule.add_mem hx hy
    | single g a =>
        simpa [algebraRepresentation] using
          S.toSubmodule.smul_mem a (S.apply_mem_toSubmodule g hv)

/-- A filtration extended to the multiplicative group-algebra action has the
same vector spaces and the same actual successive quotients. -/
def algebraFiltration {A : Rep.{uV} k G} {n : ℕ} (s : ObjectRepFiltration A n) :
    ObjectRepFiltration (Rep.of (algebraRepresentation A.ρ)) n :=
  ObjectRepFiltration.ofSubrepresentations
    (fun i => algebraSubrepresentation (s.subrepresentation i))
    (fun _ _ hij => s.monotone_subrepresentation hij)
    (by
      apply Subrepresentation.toSubmodule_injective
      change (s.subrepresentation 0).toSubmodule = (⊥ : Subrepresentation A.ρ).toSubmodule
      exact congrArg Subrepresentation.toSubmodule s.subrepresentation_zero)
    (by
      apply Subrepresentation.toSubmodule_injective
      change (s.subrepresentation (Fin.last n)).toSubmodule =
        (⊤ : Subrepresentation A.ρ).toSubmodule
      exact congrArg Subrepresentation.toSubmodule s.subrepresentation_last)

theorem algebraFiltration_graded_action {A : Rep.{uV} k G} {n : ℕ}
    (s : ObjectRepFiltration A n) (i : Fin n) (x : MonoidAlgebra k G)
    (v : s.gradedRepresentation i) :
    ((algebraFiltration s).gradedRepresentation i).ρ x v =
      algebraRepresentation (s.gradedRepresentation i).ρ x v := by
  obtain ⟨w, rfl⟩ := s.gradedProjection_surjective i v
  let q := (s.gradedProjection i).hom
  change q ⟨A.ρ.asAlgebraHom x w, _⟩ =
    (s.gradedRepresentation i).ρ.asAlgebraHom x (q w)
  induction x using MonoidAlgebra.induction_linear with
  | zero => exact map_zero q
  | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply]
      change q (⟨A.ρ.asAlgebraHom x w,
          (algebraSubrepresentation (s.subrepresentation i.succ)).apply_mem_toSubmodule
            x w.property⟩ + ⟨A.ρ.asAlgebraHom y w,
          (algebraSubrepresentation (s.subrepresentation i.succ)).apply_mem_toSubmodule
            y w.property⟩) =
        (s.gradedRepresentation i).ρ.asAlgebraHom x (q w) +
          (s.gradedRepresentation i).ρ.asAlgebraHom y (q w)
      rw [map_add, hx, hy]
  | single g a =>
      simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply]
      change q (a • ((s.subrepresentation i.succ).toRepresentation g w)) =
        a • (s.gradedRepresentation i).ρ g (q w)
      rw [map_smul, q.isIntertwining]

/-- The finite linear combination of the specified central group elements. -/
def centralAlgebra :
    (Subgroup.center G →₀ k) →ₗ[k] MonoidAlgebra k G :=
  Finsupp.linearCombination k (fun z => MonoidAlgebra.of k G (z : G))

/-- The value of a character on a finite linear combination. -/
def characterValue (χ : Subgroup.center G →* kˣ) :
    (Subgroup.center G →₀ k) →ₗ[k] k :=
  Finsupp.linearCombination k (fun z => (χ z : k))

theorem centralAlgebra_commute (t : Subgroup.center G →₀ k)
    (x : MonoidAlgebra k G) : centralAlgebra t * x = x * centralAlgebra t := by
  induction t using Finsupp.induction_linear with
  | zero => simp
  | add t u ht hu => simp [map_add, add_mul, mul_add, ht, hu]
  | single z a =>
      induction x using MonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy => simp [mul_add, add_mul, hx, hy]
      | single g b =>
          simp only [centralAlgebra, Finsupp.linearCombination_single,
            MonoidAlgebra.of_apply, MonoidAlgebra.smul_single, smul_eq_mul, mul_one,
            MonoidAlgebra.single_mul_single]
          rw [Subgroup.mem_center_iff.mp z.property g, mul_comm a b]

theorem centralAlgebra_acts_scalar {V : Type uV} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (χ : Subgroup.center G →* kˣ) (v : V)
    (hχ : ∀ z : Subgroup.center G, ρ (z : G) v = (χ z : k) • v)
    (t : Subgroup.center G →₀ k) :
    algebraRepresentation ρ (centralAlgebra t) v = characterValue χ t • v := by
  induction t using Finsupp.induction_linear with
  | zero => simp [algebraRepresentation]
  | add t u ht hu =>
      change ρ.asAlgebraHom (centralAlgebra t) v = _ at ht
      change ρ.asAlgebraHom (centralAlgebra u) v = _ at hu
      simp [algebraRepresentation, map_add, ht, hu, add_smul]
  | single z a =>
      simp [centralAlgebra, characterValue, algebraRepresentation, hχ, smul_smul]

theorem exists_separating_centralAlgebra [Infinite k] {n : ℕ}
    (χ : Fin n → Subgroup.center G →* kˣ) (hχ : Function.Injective χ) :
    ∃ t : Subgroup.center G →₀ k, Function.Injective (fun i => characterValue (χ i) t) := by
  let I := {p : Fin n × Fin n // p.1 ≠ p.2}
  let f (p : I) := characterValue (χ p.val.1) - characterValue (χ p.val.2)
  have hf : ∀ p : I, ∃ t, f p t ≠ 0 := by
    intro p
    have hne : χ p.val.1 ≠ χ p.val.2 := fun h => p.property (hχ h)
    obtain ⟨z, hz⟩ := DFunLike.ne_iff.mp hne
    refine ⟨Finsupp.single z 1, ?_⟩
    simpa [f, characterValue, sub_ne_zero, Units.val_inj] using hz
  obtain ⟨t, ht⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f hf
  refine ⟨t, fun i j hij => ?_⟩
  by_contra h
  exact ht ⟨(i, j), h⟩ (by simpa [f] using sub_eq_zero.mpr hij)

/-- The actual scalar central-character spaces are independent, identify with
the successive quotients, and split every invariant subspace. -/
def HasCentralCharacterSplitting {A : Rep.{uV} k G} {n : ℕ}
    (s : ObjectRepFiltration A n) (χ : Fin n → Subgroup.center G →* kˣ) : Prop :=
  (∀ i, Nonempty ((centralCharacterSpace A.ρ (χ i) 1).toRepresentation.Equiv
    (s.gradedRepresentation i).ρ)) ∧
  iSupIndep (fun i => (centralCharacterSpace A.ρ (χ i) 1).toSubmodule) ∧
  ∀ S : Subrepresentation A.ρ, S = ⨆ i, S ⊓ centralCharacterSpace A.ρ (χ i) 1

/-- Renard VI.8.5's filtration lemma, with no irreducibility assumption on the
quotients or finite-dimensionality assumption on the representation. -/
theorem splitting_of_distinct_centralCharacters [Infinite k]
    {A : Rep.{uV} k G} {n : ℕ} (s : ObjectRepFiltration A n)
    (χ : Fin n → Subgroup.center G →* kˣ) (hχ : Function.Injective χ)
    (hgr : ∀ (i : Fin n) (z : Subgroup.center G) (v : s.gradedRepresentation i),
      (s.gradedRepresentation i).ρ (z : G) v = (χ i z : k) • v) :
    HasCentralCharacterSplitting s χ := by
  classical
  obtain ⟨t, ht⟩ := exists_separating_centralAlgebra χ hχ
  let B := Rep.of (algebraRepresentation A.ρ)
  let sb := algebraFiltration s
  let z := centralAlgebra t
  let hz : ∀ x, z * x = x * z := centralAlgebra_commute t
  let c : Fin n → k := fun i => characterValue (χ i) t
  have hg : ∀ (i : Fin n) (v : sb.gradedRepresentation i),
      (sb.gradedRepresentation i).ρ z v = c i • v := by
    intro i v
    exact (algebraFiltration_graded_action s i (centralAlgebra t) v).trans
      (centralAlgebra_acts_scalar _ (χ i) v (fun z => hgr i z v) t)
  let E (i : Fin n) := CentralEigenspaceSplitting.eigenSubrep B.ρ z hz (c i)
  let S (i : Fin n) : Subrepresentation A.ρ := {
    toSubmodule := (E i).toSubmodule
    apply_mem_toSubmodule g v hv := by
      have h := (E i).apply_mem_toSubmodule (MonoidAlgebra.of k G g) hv
      change A.ρ.asAlgebraHom (MonoidAlgebra.of k G g) v ∈ (E i).toSubmodule at h
      rw [Representation.asAlgebraHom_of] at h
      exact h }
  let q (i : Fin n) :
      (S i).toRepresentation.IntertwiningMap (s.gradedRepresentation i).ρ := {
    toLinearMap := (CentralEigenspaceSplitting.eigenToGraded sb z hz c ht hg i).toLinearMap
    isIntertwining' g := by
      ext v
      exact Rep.hom_comm_apply (s.gradedProjection i) g
        (Submodule.inclusion
          (CentralEigenspaceSplitting.eigenSubrep_le sb z hz c ht hg i i.succ (by simp)) v) }
  have hq (i : Fin n) : Function.Bijective (q i) :=
    CentralEigenspaceSplitting.eigenToGraded_bijective sb z hz c ht hg i
  have hS (i : Fin n) : S i = centralCharacterSpace A.ρ (χ i) 1 := by
    apply le_antisymm
    · intro v hv
      rw [mem_centralCharacterSpace_one]
      intro a
      let w : (S i).toSubmodule := ⟨v, hv⟩
      have hw : (S i).toRepresentation (a : G) w = (χ i a : k) • w := by
        apply (hq i).1
        rw [(q i).isIntertwining, map_smul, hgr]
      exact congrArg Subtype.val hw
    · intro v hv
      change v ∈ CentralEigenspaceSplitting.eigenSubrep B.ρ z hz (c i)
      apply CentralEigenspaceSplitting.mem_eigenSubrep.mpr
      exact centralAlgebra_acts_scalar A.ρ (χ i) v
        ((mem_centralCharacterSpace_one A.ρ (χ i) v).mp hv) t
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [← hS i]
    exact ⟨(q i).ofBijective (hq i)⟩
  · have h := (Module.End.eigenspaces_iSupIndep (B.ρ z)).comp ht
    change iSupIndep (fun i => (S i).toSubmodule) at h
    simpa only [hS] using h
  · intro T
    have h := CentralEigenspaceSplitting.eq_iSup_inf sb z hz c ht hg
      (algebraSubrepresentation T)
    apply Subrepresentation.toSubmodule_injective
    have h' := congrArg Subrepresentation.toSubmodule h
    rw [Langlands.Subrepresentation.toSubmodule_iSup] at h' ⊢
    change T.toSubmodule = ⨆ i, T.toSubmodule ⊓ (S i).toSubmodule at h'
    simpa only [hS, Subrepresentation.toSubmodule_inf] using h'

theorem iSup_centralCharacterSpace_eq_top [Infinite k]
    {A : Rep.{uV} k G} {n : ℕ} (s : ObjectRepFiltration A n)
    (χ : Fin n → Subgroup.center G →* kˣ) (hχ : Function.Injective χ)
    (hgr : ∀ (i : Fin n) (z : Subgroup.center G) (v : s.gradedRepresentation i),
      (s.gradedRepresentation i).ρ (z : G) v = (χ i z : k) • v) :
    (⨆ i, centralCharacterSpace A.ρ (χ i) 1) = ⊤ := by
  have h := (splitting_of_distinct_centralCharacters s χ hχ hgr).2.2 ⊤
  simpa using h.symm

end Langlands.CentralCharacterSplitting
