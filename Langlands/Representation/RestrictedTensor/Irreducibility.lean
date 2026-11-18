import Langlands.Representation.RestrictedTensor.LocalSeparation
import Langlands.Representation.Tensor.FiniteProperties

/-! # Irreducibility of actual algebraic restricted tensor representations -/

noncomputable section
open scoped Classical TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

universe uK uI uG uV

namespace Langlands.RestrictedTensor

variable {K : Type uK} [Field K] {ι : Type uI}
  {G : ι → Type uG} [∀ i, Group (G i)]
  {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
  (H : ∀ i, Subgroup (G i)) (ρ : ∀ i, Representation K (G i) (V i))
  (E : Finset ι) (e : ∀ i, V i)
  (he : ∀ i ∉ E, ∀ g ∈ H i, ρ i g (e i) = e i)

/-- Extend a finite tuple of group elements by the identity. -/
def stageGroupElement (S : Finset ι) (g : ∀ i : S, G i) : RestrictedGroup G H :=
  ⟨fun i => if h : i ∈ S then g ⟨i, h⟩ else 1,
    S.eventually_cofinite_notMem.mono (fun i hi => by
      change (if h : i ∈ S then g ⟨i, h⟩ else 1) ∈ H i
      rw [dite_eq_right hi]
      exact (H i).one_mem)⟩

/-- Finite stage embeddings intertwine the full external product action. -/
theorem of_external (S : Index E) (g : ∀ i : S.1, G i)
    (z : Stage K V S.1) :
    of K V E e S (FiniteTensor.external (fun i : S.1 => ρ i) g z) =
      representation H ρ E e he (stageGroupElement H S.1 g) (of K V E e S z) := by
  have hlin : (of K V E e S).comp (FiniteTensor.external (fun i : S.1 => ρ i) g) =
      (representation H ρ E e he (stageGroupElement H S.1 g)).comp (of K V E e S) := by
    ext v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      FiniteTensor.external_tprod]
    change pure E e S (fun i => ρ i (g i) (v i)) =
      representation H ρ E e he (stageGroupElement H S.1 g) (pure E e S v)
    rw [representation_pure_of_mem H ρ E e he _ S
      (fun i hi => by simp [stageGroupElement, hi])]
    congr 1
    funext i
    simp [stageGroupElement, i.property]
  exact LinearMap.congr_fun hlin z

/-- Irreducible local factors with scalar self-intertwiners have irreducible
actual algebraic restricted tensor product. -/
theorem representation_isIrreducible
    (hne : ∀ i ∉ E, e i ≠ 0) [∀ i, (ρ i).IsIrreducible]
    (hscalar : ∀ i, ∀ f : (ρ i).IntertwiningMap (ρ i),
      ∃ c : K, f = c • Representation.IntertwiningMap.id (ρ i)) :
    (representation H ρ E e he).IsIrreducible := by
  classical
  have hstage (N : Subrepresentation (representation H ρ E e he)) (S : Index E)
      (z : Stage K V S.1) (hz : of K V E e S z ∈ N) (hz0 : z ≠ 0) :
      ∀ t : Stage K V S.1, of K V E e S t ∈ N := by
    let NS : Subrepresentation (FiniteTensor.external (fun i : S.1 => ρ i)) :=
      { toSubmodule := N.toSubmodule.comap (of K V E e S)
        apply_mem_toSubmodule := by
          intro g x hx
          change of K V E e S (FiniteTensor.external (fun i : S.1 => ρ i) g x) ∈ N
          rw [of_external H ρ E e he]
          exact N.apply_mem_toSubmodule _ hx }
    let : (FiniteTensor.external (fun i : S.1 => ρ i)).IsIrreducible :=
      FiniteTensor.isIrreducible_external (fun i : S.1 => ρ i) (fun i => hscalar i)
    have htop : NS = ⊤ := (eq_bot_or_eq_top NS).resolve_left (fun hbot => by
      have hm : z ∈ NS := hz
      rw [hbot] at hm
      exact hz0 ((Submodule.mem_bot K).mp hm))
    intro t
    have hm : t ∈ NS := htop ▸ Submodule.mem_top
    exact hm
  have hmain (N : Subrepresentation (representation H ρ E e he))
      (x : Space K V E e) (hx : x ∈ N) (hx0 : x ≠ 0) : N = ⊤ := by
    obtain ⟨S, z, rfl⟩ := exists_of E e x
    apply Subrepresentation.ext
    apply top_unique
    intro y _
    obtain ⟨T, t, rfl⟩ := exists_of E e y
    let U : Index E := ⟨S.1 ∪ T.1, S.2.trans Finset.subset_union_left⟩
    have hSU : S ≤ U := Finset.subset_union_left
    have hTU : T ≤ U := Finset.subset_union_right
    have hzU : of K V E e U (transition e hSU z) ∈ N := by
      rwa [of_transition]
    have hzU0 : transition e hSU z ≠ 0 := by
      intro hz
      apply hx0
      rw [← of_transition E e hSU, hz, map_zero]
    have htU := hstage N U (transition e hSU z) hzU hzU0 (transition e hTU t)
    rwa [of_transition] at htU
  let : ∀ i, Nontrivial (V i) := fun i =>
    IsSimpleModule.nontrivial (MonoidAlgebra K (G i)) (ρ i).asModule
  let := space_nontrivial (K := K) E e hne
  obtain ⟨x0, hx0⟩ := exists_ne (0 : Space K V E e)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => hx0 ?_⟩, eq_bot_or_eq_top := fun N => ?_ }
  · have hx : x0 ∈ (⊤ : Subrepresentation (representation H ρ E e he)) := Submodule.mem_top
    rw [← h] at hx
    exact (Submodule.mem_bot K).mp hx
  · by_cases hN : ∃ x ∈ N, x ≠ 0
    · obtain ⟨x, hx, hx0⟩ := hN
      exact Or.inr (hmain N x hx hx0)
    · left
      push Not at hN
      apply Subrepresentation.ext
      exact (Submodule.eq_bot_iff _).mpr hN

/-- The irreducibility property for all actual restricted tensor representations. -/
def RestrictedTensorIrreducibilityStatement : Prop :=
  ∀ (k : Type uK) [Field k] (I : Type uI) (G : I → Type uG) [∀ i, Group (G i)]
    (V : I → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (H : ∀ i, Subgroup (G i)) (ρ : ∀ i, Representation k (G i) (V i))
    (E : Finset I) (e : ∀ i, V i)
    (he : ∀ i ∉ E, ∀ g ∈ H i, ρ i g (e i) = e i),
    (∀ i ∉ E, e i ≠ 0) → (∀ i, (ρ i).IsIrreducible) →
    (∀ i, ∀ f : (ρ i).IntertwiningMap (ρ i),
      ∃ c : k, f = c • Representation.IntertwiningMap.id (ρ i)) →
    (representation H ρ E e he).IsIrreducible

/-- Finite external tensor simplicity passes to the actual restricted tensor limit. -/
theorem restrictedTensorIrreducibility :
    RestrictedTensorIrreducibilityStatement.{uK, uI, uG, uV} := by
  intro k _ I G _ V _ _ H ρ E e he hne hI hscalar
  let := hI
  exact representation_isIrreducible H ρ E e he hne hscalar

end Langlands.RestrictedTensor
