import Langlands.GroupScheme.Rational.IndependentStandardCocharacter
import Langlands.GroupScheme.Rational.RootFiniteness
import Mathlib.LinearAlgebra.RootSystem.BaseExists

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

private def rationalLatticeFunctional (ν : cocharacterLattice T) :
    (ℚ ⊗[ℤ] characterLattice T) →ₗ[ℚ] ℚ :=
  (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).toLinearMap.comp
    (((latticePairing T).flip ν).baseChange ℚ)

private theorem rationalLatticeFunctional_toRat
    (ν : cocharacterLattice T) (α : characterLattice T) :
    rationalLatticeFunctional ν (toRat α) = (latticePairing T α ν : ℚ) := by
  simp [rationalLatticeFunctional, toRat, zsmul_eq_mul]

variable {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (ν : cocharacterLattice T)

/-- Negation of an actual relative root is a relative root under the published
root-system realization and splitness. -/
theorem HasRelativeRootSystem.neg_mem_relativeRoots
    (h : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    {α : characterLattice T} (hα : α ∈ relativeRoots i) :
    -α ∈ relativeRoots i := by
  obtain ⟨R, _, P, _, _, _, hroots, _, _⟩ := h
  have hx : toRat α ∈ Subtype.val '' Set.range P.root := by
    rw [hroots]
    exact Set.mem_image_of_mem _ hα
  obtain ⟨x, hx, hxα⟩ := hx
  have hneg : -(x : ℚ ⊗[ℤ] characterLattice T) ∈ toRat '' relativeRoots i := by
    rw [← hroots]
    exact ⟨-x, P.neg_mem_range_root_iff.mpr hx, rfl⟩
  obtain ⟨β, hβ, hβeq⟩ := hneg
  have hβα : β = -α := hT.character_toRat_injective (by
    rw [map_neg, ← hxα]
    exact hβeq)
  exact hβα ▸ hβ

/-- The rationalized actual simple relative roots are independent under the
published relative-root-system hypothesis. Reducedness is not needed. -/
theorem HasRelativeRootSystem.linearIndependent_simpleRelativeRoots
    (h : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (hν : IsGenericCocharacter i ν) :
    LinearIndependent ℚ
      (fun α : simpleRelativeRoots i ν => toRat (α : characterLattice T)) := by
  classical
  obtain ⟨R, hR, P, hP, hcrys, _, hroots, _, _⟩ := h
  have := hR
  have := hP
  have := hcrys
  let V := ℚ ⊗[ℤ] characterLattice T
  let W := relativeRootSpan i
  let f : W →ₗ[ℚ] ℚ := (rationalLatticeFunctional ν).comp W.subtype
  have hrep (j : R) :
      ∃ α ∈ relativeRoots i, toRat α = (P.root j : V) := by
    have hx : (P.root j : V) ∈ toRat '' relativeRoots i := by
      rw [← hroots]
      exact ⟨P.root j, ⟨j, rfl⟩, rfl⟩
    exact hx
  choose r hr hrat using hrep
  have hfr (j : R) : f (P.root j) = (latticePairing T (r j) ν : ℚ) := by
    change rationalLatticeFunctional ν (P.root j : V) = _
    rw [← hrat j, rationalLatticeFunctional_toRat]
  have hf (j : R) : f (P.root j) ≠ 0 := by
    rw [hfr]
    exact_mod_cast hν (r j) (hr j)
  have hindex (α : simpleRelativeRoots i ν) :
      ∃ j : R, (P.root j : V) = toRat (α : characterLattice T) := by
    have hx : toRat (α : characterLattice T) ∈
        Subtype.val '' Set.range P.root := by
      rw [hroots]
      exact ⟨α, α.2.1.1, rfl⟩
    obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hx
    exact ⟨j, hj⟩
  choose a ha using hindex
  have hbase (α : simpleRelativeRoots i ν) :
      a α ∈ IsAddIndecomposable.baseOf P.root f.toAddMonoidHom := by
    have hfa : f (P.root (a α)) = (latticePairing T α ν : ℚ) := by
      change rationalLatticeFunctional ν (P.root (a α) : V) = _
      rw [ha, rationalLatticeFunctional_toRat]
    refine ⟨?_, fun j hj l hl heq => ?_⟩
    · change 0 < f (P.root (a α))
      rw [hfa]
      exact_mod_cast α.2.1.2
    · exfalso
      apply α.2.2
      have hj' : 0 < latticePairing T (r j) ν := by
        change 0 < f (P.root j) at hj
        rw [hfr] at hj
        exact_mod_cast hj
      have hl' : 0 < latticePairing T (r l) ν := by
        change 0 < f (P.root l) at hl
        rw [hfr] at hl
        exact_mod_cast hl
      refine ⟨r j, ⟨hr j, hj'⟩, r l, ⟨hr l, hl'⟩, ?_⟩
      apply hT.character_toRat_injective
      rw [map_add, hrat j, hrat l, ← ha α]
      exact congrArg Subtype.val heq
  let a' : simpleRelativeRoots i ν →
      IsAddIndecomposable.baseOf P.root f.toAddMonoidHom := fun α => ⟨a α, hbase α⟩
  have ha' : Function.Injective a' := by
    intro α β hab
    apply Subtype.ext
    apply hT.character_toRat_injective
    rw [← ha α, ← ha β]
    exact congrArg (fun j : IsAddIndecomposable.baseOf P.root f.toAddMonoidHom =>
      (P.root j : V)) hab
  have hli := (P.linearIndepOn_root_baseOf f.toAddMonoidHom hf).comp a' ha'
  have hli' := hli.map' W.subtype (by simp)
  convert hli' using 1
  funext α
  exact (ha α).symm

/-- A relative-root-system realization supplies the root independence needed
for standard-cocharacter existence. -/
theorem HasRelativeRootSystem.exists_standardCocharacter
    (h : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν) :
    ∃ zeta : cocharacterLattice T, IsStandardCocharacter i ν J zeta :=
  exists_standardCocharacter_of_linearIndependent i ν hT
    (h.linearIndependent_simpleRelativeRoots i ν hT hν) J hJ

/-- A standard cocharacter chosen from the published relative-root-system
realization. -/
def standardCocharacterOfRelativeRootSystem
    (h : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν) :
    cocharacterLattice T :=
  (h.exists_standardCocharacter i ν hT hν J hJ).choose

theorem standardCocharacterOfRelativeRootSystem_spec
    (h : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν) :
    IsStandardCocharacter i ν J
      (standardCocharacterOfRelativeRootSystem i ν h hT hν J hJ) :=
  (h.exists_standardCocharacter i ν hT hν J hJ).choose_spec

end Langlands.GroupScheme
