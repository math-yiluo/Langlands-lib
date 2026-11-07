import Langlands.GroupScheme.Reductive.RootDatumGaloisRoots
import Mathlib.LinearAlgebra.RootSystem.Base

/-! # Ordinary Galois actions on simple roots of descended positive systems -/

noncomputable section

universe u v w

namespace RootPairing.Base

variable {J : Type v} [Finite J] {M N : Type w} [AddCommGroup M] [AddCommGroup N]
    (P : RootDatum J M N) (b : P.Base)

/-- A positive root is simple exactly when it is not a sum of two positive roots. -/
theorem mem_support_iff_positive_indecomposable (i : J) :
    i ∈ b.support ↔ b.IsPos i ∧
      ∀ j l, b.IsPos j → b.IsPos l → P.root i ≠ P.root j + P.root l := by
  constructor
  · intro hi
    refine ⟨b.isPos_of_mem_support hi, ?_⟩
    intro j l hj hl heq
    have hh := b.height_add heq
    rw [b.height_one_of_mem_support hi] at hh
    change 0 < b.height j at hj
    change 0 < b.height l at hl
    omega
  · rintro ⟨hi, hindecomp⟩
    have h : i ∈ b.support ∨ ∃ j l, b.IsPos j ∧ b.IsPos l ∧
        P.root i = P.root j + P.root l := by
      apply hi.induction_on_add
      · intro j hj
        exact Or.inl hj
      · intro j l z hz hj hl
        apply Or.inr
        refine ⟨j, l, ?_, b.isPos_of_mem_support hl, hz⟩
        rcases hj with hj | ⟨a, c, ha, hc, hac⟩
        · exact b.isPos_of_mem_support hj
        · exact ha.add hc hac
    rcases h with h | ⟨j, l, hj, hl, heq⟩
    · exact h
    · exact False.elim (hindecomp j l hj hl heq)

/-- Preserving positive roots forces an actual root permutation to preserve the
simple-root support. Only root transport, not coroot transport, is needed. -/
theorem mem_support_equiv_iff_of_isPos
    (e : Equiv.Perm J) (f : M ≃ₗ[ℤ] M)
    (hf : ∀ j, P.root (e j) = f (P.root j))
    (hpos : ∀ j, b.IsPos (e j) ↔ b.IsPos j) (i : J) :
    e i ∈ b.support ↔ i ∈ b.support := by
  rw [mem_support_iff_positive_indecomposable P b,
    mem_support_iff_positive_indecomposable P b, hpos]
  constructor
  · rintro ⟨hi, h⟩
    refine ⟨hi, ?_⟩
    intro j l hj hl heq
    apply h (e j) (e l) ((hpos j).mpr hj) ((hpos l).mpr hl)
    rw [hf, hf, hf, heq, map_add]
  · rintro ⟨hi, h⟩
    refine ⟨hi, ?_⟩
    intro j l hj hl heq
    apply h (e.symm j) (e.symm l)
      ((hpos (e.symm j)).mp (by simpa using hj))
      ((hpos (e.symm l)).mp (by simpa using hl))
    apply f.injective
    rw [map_add, ← hf, ← hf, ← hf]
    simpa using heq

end RootPairing.Base

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable (k E : Type u) [Field k] [Field E] [Algebra k E]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G)

local instance baseChangeAffineSimple :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k E))
  infer_instance

variable {J : Type v} [Finite J]
    {P : RootDatum J
      (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))
      (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))}
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map i) P) (b : P.Base)
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    (j : T.toGrp ⟶ H)
    (hpos : ∀ a, b.IsPos a ↔ P.root a ∈
      roots ((GroupScheme.baseChange (algebraBaseMap k E)).map j))

omit [Finite J] in
include hpos in
/-- A descended actual positive root set is stable under ordinary Galois transport. -/
theorem IsRootDatumOf.galoisRootIndexEquiv_isPos_iff
    (σ : E ≃ₐ[k] E) (a : J) :
    b.IsPos (IsRootDatumOf.galoisRootIndexEquiv k E i hP σ a) ↔ b.IsPos a := by
  rw [hpos, hpos]
  exact IsRootDatumOf.galoisRootIndexEquiv_mem_roots_iff k E i hP j σ a

include hpos in
/-- No Weyl correction is needed for a base whose positive roots are the roots
of the supplied descended map. -/
theorem IsRootDatumOf.galoisRootIndexEquiv_mem_support_iff
    (σ : E ≃ₐ[k] E) (a : J) :
    IsRootDatumOf.galoisRootIndexEquiv k E i hP σ a ∈ b.support ↔ a ∈ b.support :=
  b.mem_support_equiv_iff_of_isPos P
    (IsRootDatumOf.galoisRootIndexEquiv k E i hP σ)
    (characterLattice.galoisEquiv k E T σ)
    (IsRootDatumOf.galoisRootIndexEquiv_root k E i hP σ)
    (IsRootDatumOf.galoisRootIndexEquiv_isPos_iff k E i hP b j hpos σ) a

/-- Restrict the actual ordinary root-index action to the simple-root support. -/
def IsRootDatumOf.galoisSimpleRootIndexAction :
    (E ≃ₐ[k] E) →* Equiv.Perm b.support where
  toFun σ := Equiv.subtypeEquiv
    (IsRootDatumOf.galoisRootIndexEquiv k E i hP σ)
    (fun a => (IsRootDatumOf.galoisRootIndexEquiv_mem_support_iff
      k E i hP b j hpos σ a).symm)
  map_one' := by
    ext a
    exact congrArg (fun e : Equiv.Perm J => e a.val)
      (map_one (IsRootDatumOf.galoisRootIndexAction k E i hP))
  map_mul' σ τ := by
    ext a
    exact congrArg (fun e : Equiv.Perm J => e a.val)
      (map_mul (IsRootDatumOf.galoisRootIndexAction k E i hP) σ τ)

@[simp]
theorem IsRootDatumOf.galoisSimpleRootIndexAction_root
    (σ : E ≃ₐ[k] E) (a : b.support) :
    P.root (IsRootDatumOf.galoisSimpleRootIndexAction k E i hP b j hpos σ a) =
      characterLattice.galoisRepresentation k E T σ (P.root a) :=
  IsRootDatumOf.galoisRootIndexEquiv_root k E i hP σ a

variable {r : ℕ} (e : Fin r ≃ b.support)

/-- Transfer the actual simple-root action to any supplied ordering. -/
def IsRootDatumOf.galoisOrderedSimpleRootAction :
    (E ≃ₐ[k] E) →* Equiv.Perm (Fin r) :=
  e.symm.permCongrHom.toMonoidHom.comp
    (IsRootDatumOf.galoisSimpleRootIndexAction k E i hP b j hpos)

@[simp]
theorem IsRootDatumOf.galoisOrderedSimpleRootAction_apply
    (σ : E ≃ₐ[k] E) (a : Fin r) :
    e (IsRootDatumOf.galoisOrderedSimpleRootAction k E i hP b j hpos e σ a) =
      IsRootDatumOf.galoisSimpleRootIndexAction k E i hP b j hpos σ (e a) := by
  change e (e.symm _) = _
  exact e.apply_symm_apply _

/-- The ordered coordinate permutation transports the corresponding actual root
by the ordinary Galois representation. -/
@[simp]
theorem IsRootDatumOf.galoisOrderedSimpleRootAction_root
    (σ : E ≃ₐ[k] E) (a : Fin r) :
    P.root (e (IsRootDatumOf.galoisOrderedSimpleRootAction k E i hP b j hpos e σ a)) =
      characterLattice.galoisRepresentation k E T σ (P.root (e a)) := by
  rw [IsRootDatumOf.galoisOrderedSimpleRootAction_apply]
  exact IsRootDatumOf.galoisSimpleRootIndexAction_root k E i hP b j hpos σ (e a)

end Langlands.GroupScheme
