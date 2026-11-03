import Langlands.Representation.Aubert.General.FirstAdjointnessConsequences
import Langlands.Representation.Unitary.AdmissibleSemisimplicityProof
import Langlands.Representation.Category.Contragredient
import Mathlib.LinearAlgebra.Projection

/-! # Irreducibility of semisimple induction detected by its actual Jacquet module -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.General

universe uG uV

open CategoryTheory SmoothRep Jacquet.Localization

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (σ : SmoothRep.{0, uG, uV} ℂ M)

include hδ

/-- A nonzero idempotent endomorphism of actual induction must be the identity
if its actual normalized Jacquet module is irreducible. -/
theorem induction_idempotent_eq_id_of_irreducible_jacquet
    (hJac : ((jacquetFunctor h hU).obj ((normalizedInductionFunctor h hU).obj σ)).IsIrreducible)
    (p : ((normalizedInductionFunctor h hU).obj σ).representation.IntertwiningMap ((normalizedInductionFunctor h hU).obj σ).representation)
    (hp : p ≠ 0) (hpp : p.comp p = p) :
    p = Representation.IntertwiningMap.id ((normalizedInductionFunctor h hU).obj σ).representation := by
  let := hJac
  let q := Representation.IntertwiningMap.id ((normalizedInductionFunctor h hU).obj σ).representation - p
  have hpq : p.comp q = 0 := by
    ext v
    change p (v - p v) = 0
    rw [map_sub]
    have hv := congrArg (fun f : ((normalizedInductionFunctor h hU).obj σ).representation.IntertwiningMap ((normalizedInductionFunctor h hU).obj σ).representation => f v) hpp
    simpa only [Representation.IntertwiningMap.comp_apply, sub_eq_zero] using hv.symm
  have hinj : Function.Injective (FirstAdjointness.equiv h hU hδ ((normalizedInductionFunctor h hU).obj σ) σ p) :=
    (Representation.IsIrreducible.injective_or_eq_zero
      (FirstAdjointness.equiv h hU hδ ((normalizedInductionFunctor h hU).obj σ) σ p)).resolve_right
        (FirstAdjointness.equiv_ne_zero h hU hδ ((normalizedInductionFunctor h hU).obj σ) σ p hp)
  have hnat := FirstAdjointness.equiv_comp h hU hδ ((normalizedInductionFunctor h hU).obj σ) σ (ofHom q) p
  have hrq : hom ((jacquetFunctor h hU).map (ofHom q)) = 0 := by
    apply Representation.IntertwiningMap.ext
    ext v
    apply hinj
    have hv := congrArg (fun f => f v) hnat
    simpa [hpq] using hv.symm
  have hq : q = 0 := by
    apply (FirstAdjointness.equiv h hU hδ ((normalizedInductionFunctor h hU).obj σ) σ).injective
    have hn := FirstAdjointness.equiv_comp h hU hδ ((normalizedInductionFunctor h hU).obj σ) σ (ofHom q)
      (Representation.IntertwiningMap.id ((normalizedInductionFunctor h hU).obj σ).representation)
    rw [hrq] at hn
    rw [map_zero]
    ext v
    have hv := congrArg (fun f => f v) hn
    simpa [Representation.IntertwiningMap.comp] using hv
  exact (sub_eq_zero.mp hq).symm

/-- Actual normalized induction is irreducible if it is algebraically
semisimple and its actual normalized Jacquet module is irreducible. -/
theorem isIrreducible_induction_of_semisimple_irreducible_jacquet
    (hsem : Representation.IsSemisimpleRepresentation ((normalizedInductionFunctor h hU).obj σ).representation)
    (hJac : ((jacquetFunctor h hU).obj ((normalizedInductionFunctor h hU).obj σ)).IsIrreducible) :
    ((normalizedInductionFunctor h hU).obj σ).IsIrreducible := by
  classical
  let := hsem
  let := hJac
  have hne : (⊥ : Subrepresentation ((normalizedInductionFunctor h hU).obj σ).representation) ≠ ⊤ := by
    intro he
    have hz (v : ((normalizedInductionFunctor h hU).obj σ)) : v = 0 := by
      have hv : v ∈ (⊥ : Subrepresentation ((normalizedInductionFunctor h hU).obj σ).representation) := by
        rw [he]
        trivial
      exact hv
    have hzq (q : (jacquetFunctor h hU).obj ((normalizedInductionFunctor h hU).obj σ)) : q = 0 := by
      obtain ⟨v, rfl⟩ := mk_surjective ((normalizedInductionFunctor h hU).obj σ).representation U 1 q
      rw [hz v]
      rfl
    apply (bot_ne_top :
      (⊥ : Subrepresentation ((jacquetFunctor h hU).obj ((normalizedInductionFunctor h hU).obj σ)).representation) ≠ ⊤)
    ext q
    change q = 0 ↔ True
    exact ⟨fun _ => trivial, fun _ => hzq q⟩
  refine { exists_pair_ne := ⟨⊥, ⊤, hne⟩, eq_bot_or_eq_top := ?_ }
  intro S
  by_cases hS : S = ⊥
  · exact Or.inl hS
  · right
    obtain ⟨C, hC⟩ := exists_isCompl S
    have hSC : IsCompl S.toSubmodule C.toSubmodule :=
      ⟨disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule hC.inf_eq_bot),
        codisjoint_iff.mpr (congrArg Subrepresentation.toSubmodule hC.sup_eq_top)⟩
    let p : ((normalizedInductionFunctor h hU).obj σ).representation.IntertwiningMap ((normalizedInductionFunctor h hU).obj σ).representation :=
      { toLinearMap := S.toSubmodule.projection C.toSubmodule hSC
        isIntertwining' := fun g => by
          ext v
          have hv := Submodule.sub_projection_mem hSC v
          have hsum : ((normalizedInductionFunctor h hU).obj σ).representation g v =
              ((normalizedInductionFunctor h hU).obj σ).representation g (S.toSubmodule.projection C.toSubmodule hSC v) +
                ((normalizedInductionFunctor h hU).obj σ).representation g
                  (v - S.toSubmodule.projection C.toSubmodule hSC v) := by
            rw [← map_add, add_sub_cancel]
          simp only [LinearMap.comp_apply]
          rw [hsum, map_add,
            Submodule.projection_apply_of_mem_left hSC
              (S.apply_mem_toSubmodule g (Submodule.projection_apply_mem hSC v)),
            Submodule.projection_apply_of_mem_right hSC (C.apply_mem_toSubmodule g hv),
            add_zero] }
    have hpfix (v : ((normalizedInductionFunctor h hU).obj σ)) (hv : v ∈ S) : p v = v :=
      Submodule.projection_apply_of_mem_left hSC hv
    have hpmem (v : ((normalizedInductionFunctor h hU).obj σ)) : p v ∈ S := Submodule.projection_apply_mem hSC v
    have hp : p ≠ 0 := by
      intro hp0
      apply hS
      apply le_antisymm _ bot_le
      intro v hv
      change v = 0
      rw [← hpfix v hv, hp0]
      rfl
    have hpp : p.comp p = p := by
      ext v
      exact hpfix (p v) (hpmem v)
    have hpone := induction_idempotent_eq_id_of_irreducible_jacquet h hU hδ σ hJac p hp hpp
    apply le_antisymm le_top
    intro v _
    have hv := hpmem v
    rw [hpone] at hv
    exact hv

/-- The admissible unitary version needs no finite-length hypothesis. -/
theorem isIrreducible_induction_of_unitary_irreducible_jacquet
    (hG : CompactOpenCofinal G)
    (hA : ((normalizedInductionFunctor h hU).obj σ).IsAdmissible) (hunitary : IsUnitarizable ((normalizedInductionFunctor h hU).obj σ).representation)
    (hJac : ((jacquetFunctor h hU).obj ((normalizedInductionFunctor h hU).obj σ)).IsIrreducible) :
    ((normalizedInductionFunctor h hU).obj σ).IsIrreducible :=
  isIrreducible_induction_of_semisimple_irreducible_jacquet h hU hδ σ
    (admissibleUnitarySemisimplicity G hG ((normalizedInductionFunctor h hU).obj σ) ((normalizedInductionFunctor h hU).obj σ).representation hA hunitary) hJac

/-- The actual inclusion of any nonzero invariant subspace of such an
induction is an equivalence onto the whole induced representation. -/
def unitaryInductionSubrepresentationEquiv
    (hG : CompactOpenCofinal G)
    (hA : ((normalizedInductionFunctor h hU).obj σ).IsAdmissible) (hunitary : IsUnitarizable ((normalizedInductionFunctor h hU).obj σ).representation)
    (hJac : ((jacquetFunctor h hU).obj ((normalizedInductionFunctor h hU).obj σ)).IsIrreducible)
    (S : Subrepresentation ((normalizedInductionFunctor h hU).obj σ).representation) (hS : S ≠ ⊥) :
    S.toRepresentation.Equiv ((normalizedInductionFunctor h hU).obj σ).representation := by
  letI := isIrreducible_induction_of_unitary_irreducible_jacquet h hU hδ σ
    hG hA hunitary hJac
  have htop : S = ⊤ := (eq_bot_or_eq_top S).resolve_left hS
  let j : S.toRepresentation.IntertwiningMap ((normalizedInductionFunctor h hU).obj σ).representation :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  exact j.ofBijective ⟨Subtype.val_injective, fun v => ⟨⟨v, by rw [htop]; trivial⟩, rfl⟩⟩

@[simp]
theorem unitaryInductionSubrepresentationEquiv_apply
    (hG : CompactOpenCofinal G)
    (hA : ((normalizedInductionFunctor h hU).obj σ).IsAdmissible) (hunitary : IsUnitarizable ((normalizedInductionFunctor h hU).obj σ).representation)
    (hJac : ((jacquetFunctor h hU).obj ((normalizedInductionFunctor h hU).obj σ)).IsIrreducible)
    (S : Subrepresentation ((normalizedInductionFunctor h hU).obj σ).representation) (hS : S ≠ ⊥) (v : S) :
    unitaryInductionSubrepresentationEquiv h hU hδ σ hG hA hunitary hJac S hS v = v.val :=
  rfl

end Langlands.Aubert.General
