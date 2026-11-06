import Langlands.WeilDeligne.ParameterNormalFormHelpers
import Langlands.WeilDeligne.DecompositionExistenceProof
import Langlands.WeilDeligne.Parameters

/-!
# Block normal form of Frobenius-semisimple parameters

Proof of `Blocks.ParameterNormalForm`, by reduction to
`Blocks.DecompositionExistence` (proved in
`Langlands.WeilDeligne.DecompositionExistenceProof`).
-/

noncomputable section

open scoped TensorProduct

namespace Langlands.WeilDeligneRepresentation.ParameterNormalForm

open Blocks

universe uG uV

section Kernels

variable {G : Type uG} [Group G]

/-- If an element acts trivially on a block of positive length, it acts
trivially on the Weil factor. -/
theorem representation_eq_one_of_block (ν : G →* ℂˣ)
    (σ : FiniteRepresentation.{0, uG, uV} ℂ G) {m : ℕ} (hm : 0 < m) {x : G}
    (hx : (block ν σ m).representation x = 1) : σ.representation x = 1 := by
  classical
  let j : Fin m := ⟨0, hm⟩
  apply LinearMap.ext
  intro v
  have h := LinearMap.congr_fun hx (v ⊗ₜ[ℂ] Pi.single j 1)
  change TensorProduct.map (σ.representation x) (Special.action ν m x)
    (v ⊗ₜ[ℂ] Pi.single j 1) = v ⊗ₜ[ℂ] Pi.single j 1 at h
  have hj : Special.action ν m x (Pi.single j 1) = Pi.single j 1 := by
    funext l
    by_cases hl : l = j
    · subst hl
      simp [j]
    · simp [hl]
  rw [TensorProduct.map_tmul, hj] at h
  have h' := congrArg
    ((TensorProduct.rid ℂ σ).toLinearMap ∘ₗ TensorProduct.map LinearMap.id (LinearMap.proj j)) h
  simpa using h'

/-- If an element acts trivially on a direct sum, it acts trivially on every
summand. -/
theorem representation_eq_one_of_directSum {ι : Type*} [Fintype ι]
    (A : ι → FiniteRepresentation.{0, uG, uV} ℂ G) {x : G}
    (hx : (FiniteRepresentation.directSum A).representation x = 1) (i : ι) :
    (A i).representation x = 1 := by
  classical
  apply LinearMap.ext
  intro v
  have h := LinearMap.congr_fun hx (DirectSum.lof ℂ ι (fun i => A i) i v)
  change DirectSum.lmap (fun i => (A i).representation x) (DirectSum.lof ℂ ι (fun i => A i) i v) =
    DirectSum.lof ℂ ι (fun i => A i) i v at h
  rw [DirectSum.lmap_lof] at h
  exact DirectSum.of_injective (β := fun i => A i) i h

end Kernels

section Topological

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- With compact inertia, an open inertia kernel gives finite inertia image. -/
theorem hasFiniteInertiaImage_of_hasOpenInertiaKernel {I : Subgroup G} [CompactSpace I]
    {A : FiniteRepresentation.{0, uG, uV} ℂ G} (hA : A.HasOpenInertiaKernel I) :
    A.HasFiniteInertiaImage I :=
  Langlands.Weil.finite_range_of_open_kernel (A.representation.comp I.subtype) hA

omit [IsTopologicalGroup G] in
/-- A representation in which inertia acts trivially has open inertia kernel. -/
theorem hasOpenInertiaKernel_of_forall {I : Subgroup G}
    {A : FiniteRepresentation.{0, uG, uV} ℂ G} (hA : ∀ i ∈ I, A.representation i = 1) :
    A.HasOpenInertiaKernel I := by
  have : (A.inertiaKernel I : Set I) = Set.univ := by
    ext i
    exact iff_of_true (hA i i.2) (Set.mem_univ _)
  rw [FiniteRepresentation.HasOpenInertiaKernel, this]
  exact isOpen_univ

variable (ν : G →* ℂˣ) (degree : G →* Multiplicative ℤ)

/-- **Clause 1.** A Frobenius-semisimple parameter is a finite sum of blocks with
irreducible Weil factors with open inertia kernel, given the decomposition
theorem for pairs with semisimple Weil part. -/
theorem exists_blocks (h : DecompositionExistence.{uG, uV})
    (hdeg : Function.Surjective degree) [CompactSpace degree.ker]
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (hA : IsFrobeniusSemisimpleParameter degree.ker degree A) :
    ∃ (k : ℕ) (d : Fin k → BlockDatum.{0, uG, uV} ℂ G),
      (∀ i, (d i).IsIrreducible ∧ (d i).representation.HasOpenInertiaKernel degree.ker) ∧
      Nonempty (WeilDeligneRepresentation.Equiv A
        (WeilDeligneRepresentation.directSum fun i => (d i).pair ν)) := by
  obtain ⟨Φ, hΦ⟩ := hdeg (Multiplicative.ofAdd 1)
  have hfin : A.toFiniteRepresentation.HasFiniteInertiaImage degree.ker :=
    hasFiniteInertiaImage_of_hasOpenInertiaKernel hA.1
  have hss : A.toFiniteRepresentation.IsSemisimple :=
    isSemisimpleRepresentation_of_isSemisimple A.representation degree hΦ hfin
      (hA.2 Φ (by simp [hΦ]))
  obtain ⟨k, d, hirr, ⟨e⟩⟩ := h G ν A hss
  refine ⟨k, d, fun i => ⟨hirr i, ?_⟩, ⟨e⟩⟩
  have hsum : (WeilDeligneRepresentation.directSum fun i => (d i).pair ν).toFiniteRepresentation
      |>.HasOpenInertiaKernel degree.ker :=
    FiniteRepresentation.hasOpenInertiaKernel_of_injective degree.ker
      e.symm.representationEquiv.toIntertwiningMap e.symm.representationEquiv.injective hA.1
  refine Subgroup.isOpen_mono (fun x hx => ?_) hsum
  have hx' : (FiniteRepresentation.directSum fun i =>
      ((d i).pair ν).toFiniteRepresentation).representation (x : G) = 1 := hx
  exact representation_eq_one_of_block ν (d i).representation (d i).length_pos
    (representation_eq_one_of_directSum _ hx' i)

/-- **Clause 2.** A finite sum of blocks with irreducible Weil factors with open
inertia kernel is a Frobenius-semisimple parameter. -/
theorem isFrobeniusSemisimpleParameter_directSum (q : ℕ)
    (hdeg : Function.Surjective degree) (hnorm : Frobenius.NormCompatible (ν := ν) degree q)
    [CompactSpace degree.ker] (k : ℕ) (d : Fin k → BlockDatum.{0, uG, uV} ℂ G)
    (hd : ∀ i, (d i).IsIrreducible ∧ (d i).representation.HasOpenInertiaKernel degree.ker) :
    IsFrobeniusSemisimpleParameter degree.ker degree
      (WeilDeligneRepresentation.directSum fun i => (d i).pair ν) := by
  obtain ⟨Φ, hΦ⟩ := hdeg (Multiplicative.ofAdd 1)
  constructor
  · refine FiniteRepresentation.hasOpenInertiaKernel_directSum degree.ker fun i => ?_
    refine FiniteRepresentation.hasOpenInertiaKernel_tensor degree.ker (hd i).2 ?_
    refine hasOpenInertiaKernel_of_forall fun x hx => ?_
    have hν : (ν x : ℂ) = 1 := by
      rw [hnorm.2 x, MonoidHom.mem_ker.mp hx]
      simp
    apply LinearMap.ext
    intro v
    funext j
    change (ν x : ℂ) ^ j.val * v j = v j
    simp [hν]
  · intro g hg
    change Module.End.IsSemisimple (DirectSum.lmap fun i =>
      TensorProduct.map ((d i).representation.representation g)
        (LinearMap.pi fun j : Fin (d i).length =>
          (ν g : ℂ) ^ j.val • (LinearMap.proj j : (Fin (d i).length → ℂ) →ₗ[ℂ] ℂ)))
    refine isSemisimple_lmap _ fun i => isSemisimple_map_diag _ ?_ _ _
    have hfin : (d i).representation.HasFiniteInertiaImage degree.ker :=
      hasFiniteInertiaImage_of_hasOpenInertiaKernel (hd i).2
    have hss : (d i).representation.IsSemisimple := by
      have := (hd i).1
      unfold BlockDatum.IsIrreducible Representation.IsIrreducible at this
      infer_instance
    exact isSemisimple_of_isSemisimpleRepresentation _ degree hΦ hfin hss hg

omit [IsTopologicalGroup G] in
/-- **Clause 3.** Every rank has a Frobenius-semisimple parameter class: the
trivial representation on `ℂ^n` with zero monodromy. -/
theorem nonempty_classesOfRank (n : ℕ) :
    Nonempty (FrobeniusSemisimpleParameterClassesOfRank.{uG, uV} (ν := ν)
      degree.ker degree n) := by
  let T : FiniteRepresentation.{0, uG, uV} ℂ G :=
    FiniteRepresentation.of (Representation.trivial ℂ G (ULift.{uV} (Fin n → ℂ)))
  have hT : IsFrobeniusSemisimpleParameter degree.ker degree (zeroMonodromy ν T) := by
    constructor
    · exact hasOpenInertiaKernel_of_forall fun _ _ => rfl
    · intro g _
      exact Module.End.isSemisimple_id
  refine ⟨⟨Quotient.mk _ ⟨zeroMonodromy ν T, hT⟩, ?_⟩⟩
  change Module.finrank ℂ (ULift.{uV} (Fin n → ℂ)) = n
  rw [finrank_ulift, Module.finrank_fin_fun]

end Topological

/-- `Blocks.ParameterNormalForm` follows from `Blocks.DecompositionExistence`. -/
theorem parameterNormalForm_of_decompositionExistence (h : DecompositionExistence.{uG, uV}) :
    ParameterNormalForm.{uG, uV} := by
  intro G _ _ _ ν degree q hdeg hnorm _
  exact ⟨exists_blocks ν degree h hdeg,
    isFrobeniusSemisimpleParameter_directSum ν degree q hdeg hnorm,
    nonempty_classesOfRank ν degree⟩

end Langlands.WeilDeligneRepresentation.ParameterNormalForm

namespace Langlands.WeilDeligneRepresentation.Blocks

universe uG uV

/-- **Block normal form of Frobenius-semisimple parameters.** -/
theorem parameterNormalForm : ParameterNormalForm.{uG, uV} :=
  ParameterNormalForm.parameterNormalForm_of_decompositionExistence decompositionExistence

end Langlands.WeilDeligneRepresentation.Blocks
