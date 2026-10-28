import Langlands.Representation.CuspidalSupport.MinimalRefinedJacquetStatement
import Langlands.Group.GL.NestedRefinement

/-!
# Nonzero quasicuspidal refined Jacquet descent in a product Levi

A proof of `MinimalNonzeroRefinedJacquetTheorem` (BZ77 sections 2.3(c) and
2.14(1)). The refinement with one block in every outer block has trivial
radical, so its refined Jacquet module is a copy of the representation. Among
the refinements with nonzero refined Jacquet module, take one whose flattened
shape has the largest number of blocks. If a proper refinement of the flattened
shape had nonzero coinvariants for the pulled-back normalized action, the
composed refinement would have a longer flattened shape and, through a
surjection onto those coinvariants, a nonzero refined Jacquet module.
-/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric Parabolic

universe u uF uV

namespace MinimalRefinedJacquet

section Groups

variable {R : Type u} [CommRing R]

/-- Reindexing along an equality of ranks carries the radical of the rank-cast
shape into the radical of the original shape. -/
theorem reindex_mem_unipotentSubgroup {a b : ℕ} (D : BlockShape b) (h : a = b)
    {g : GeneralLinear a R} (hg : g ∈ (D.rankCast h.symm).unipotentSubgroup R) :
    reindex (R := R) (finCongr h) g ∈ D.unipotentSubgroup R := by
  subst h
  exact hg

variable {n : ℕ} (B : BlockShape n)

/-- The refinement keeping every outer block as a single inner block. -/
def wholeRefinement : BlockRefinement B := fun i =>
  { length := 1
    size := fun _ => B.size i
    positive := fun _ => B.positive i
    sum_eq := by simp }

/-- The refined radical of the whole refinement is trivial. -/
theorem eq_one_of_mem_refinedUnipotent_wholeRefinement {g : B.Levi R}
    (hg : g ∈ refinedUnipotent R B (wholeRefinement B)) : g = 1 := by
  funext i
  obtain ⟨u, hu, hgu⟩ := (mem_refinedUnipotent R B _ g).mp hg i
  rw [← hgu]
  exact (wholeRefinement B i).unipotentRadical_val_eq_one R le_rfl ⟨u, hu⟩

variable (S : BlockRefinement B) (S' : BlockRefinement (B.flatten S))

/-- Every outer component of a radical element of the composed refinement lies
in the middle parabolic, with middle diagonal blocks in the radical of the
refinement pulled back inside that block. -/
theorem exists_mem_parabolic_of_mem_composeRefinement {g : B.Levi R}
    (hg : g ∈ refinedUnipotent R B (B.composeRefinement S S')) (i : Fin B.length) :
    ∃ hP : g i ∈ (S i).parabolic R,
      (S i).leviProjection R ⟨g i, hP⟩ ∈
        refinedUnipotent R (S i) (B.refinementWithin S S' i) :=
  (mem_leviPreimage_iff R (S i) _ (g i)).mp
    ((S i).flatten_unipotentSubgroup_le (B.refinementWithin S S' i) R
      ((mem_refinedUnipotent R B _ g).mp hg i))

/-- The composed refined radical lies in the middle refined parabolic. -/
theorem composeRefinement_refinedUnipotent_le :
    refinedUnipotent R B (B.composeRefinement S S') ≤ refinedParabolic R B S := by
  intro g hg
  rw [mem_refinedParabolic]
  exact fun i => (exists_mem_parabolic_of_mem_composeRefinement B S S' hg i).1

/-- The nested coordinates of the middle Levi projection are the blockwise Levi
projections. -/
theorem refinedLeviEquiv_symm_refinedLeviProjection (q : refinedParabolic R B S)
    (i : Fin B.length) :
    (refinedLeviEquiv R B S).symm (refinedLeviProjection R B S q) i =
      (S i).leviProjection R (refinedParabolicEval R B S i q) := by
  change (refinedLeviEquiv R B S).symm (refinedLeviEquiv R B S
    (fun i => (S i).leviProjection R (refinedParabolicEval R B S i q))) i = _
  rw [MulEquiv.symm_apply_apply]

/-- The middle Levi part of a composed radical element has every inner
coordinate in the radical of the pulled-back refinement. -/
theorem refinedLeviEquiv_symm_mem {g : B.Levi R}
    (hg : g ∈ refinedUnipotent R B (B.composeRefinement S S')) (i : Fin B.length) :
    (refinedLeviEquiv R B S).symm
        (refinedLeviProjection R B S ⟨g, composeRefinement_refinedUnipotent_le B S S' hg⟩) i ∈
      refinedUnipotent R (S i) (B.refinementWithin S S' i) := by
  rw [refinedLeviEquiv_symm_refinedLeviProjection]
  exact (exists_mem_parabolic_of_mem_composeRefinement B S S' hg i).2

/-- The coordinate equivalence of the target statement, from the flattened Levi
onto the refined Levi. -/
abbrev flattenLeviEquiv : (B.flatten S).Levi R ≃* refinedLevi R B S :=
  BlockShape.leviRefinementEquiv (B.flatten S) B S (B.flattenBlockEquiv S)
    (fun q => (B.flatten_size_flattenBlockEquiv S q).symm) R

/-- An element of the refined Levi whose inner coordinates lie in the radicals of
the pulled-back refinements comes from the refined radical of `S'` in the
flattened Levi. -/
theorem flattenLeviEquiv_symm_mem (m : refinedLevi R B S)
    (hm : ∀ i, (refinedLeviEquiv R B S).symm m i ∈
      refinedUnipotent R (S i) (B.refinementWithin S S' i)) :
    (flattenLeviEquiv B S).symm m ∈ refinedUnipotent R (B.flatten S) S' := by
  rw [mem_refinedUnipotent]
  intro k
  obtain ⟨⟨i, j⟩, rfl⟩ := (B.flattenBlockEquiv S).surjective k
  change (BlockShape.nestedLeviEquiv (B.flatten S) B S (B.flattenBlockEquiv S)
      (fun q => (B.flatten_size_flattenBlockEquiv S q).symm) R).symm
    ((refinedLeviEquiv R B S).symm m) (B.flattenBlockEquiv S ⟨i, j⟩) ∈ _
  rw [BlockShape.nestedLeviEquiv_symm_apply]
  exact reindex_mem_unipotentSubgroup _ _
    ((mem_refinedUnipotent R (S i) _ _).mp (hm i) j)

end Groups

section Modulus

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
variable (B : BlockShape n) (S : BlockRefinement B) (S' : BlockRefinement (B.flatten S))

/-- The full refined modulus is trivial on such a middle Levi element. -/
theorem refinedLeviModulus_eq_one (m : refinedLevi F.Carrier B S)
    (hm : ∀ i, (refinedLeviEquiv F.Carrier B S).symm m i ∈
      refinedUnipotent F.Carrier (S i) (B.refinementWithin S S' i)) :
    T.refinedLeviModulus B S m = 1 := by
  rw [T.refinedLeviModulus_apply B S]
  exact Finset.prod_eq_one fun i _ =>
    T.leviModulus_refinedUnipotent (S i) (B.refinementWithin S S' i) ⟨_, hm i⟩

end Modulus

section Representation

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (B : BlockShape n) (S : BlockRefinement B) (S' : BlockRefinement (B.flatten S))
  (ρ : Representation ℂ (B.Levi F.Carrier) V)

/-- The normalized refined Jacquet action pulled back to the flattened Levi, as
in the target statement. -/
abbrev flattenedAction :
    Representation ℂ ((B.flatten S).Levi F.Carrier) (RefinedJacquetModule B S ρ) :=
  (T.normalizedRefinedJacquet B S ρ).comp (flattenLeviEquiv B S).toMonoidHom

/-- A radical element of the composed refinement acts trivially on the iterated
coinvariants: its middle radical part dies in the refined Jacquet module, and its
middle Levi part has trivial normalization and comes from the radical of `S'`. -/
theorem mk_refinedJacquetMk_composeRefinement {g : B.Levi F.Carrier}
    (hg : g ∈ refinedUnipotent F.Carrier B (B.composeRefinement S S')) (v : V) :
    Jacquet.mk (flattenedAction T B S ρ) (refinedUnipotent F.Carrier (B.flatten S) S')
        (refinedJacquetMk B S ρ (ρ g v)) =
      Jacquet.mk (flattenedAction T B S ρ) (refinedUnipotent F.Carrier (B.flatten S) S')
        (refinedJacquetMk B S ρ v) := by
  let q : refinedParabolic F.Carrier B S :=
    ⟨g, composeRefinement_refinedUnipotent_le B S S' hg⟩
  let m := refinedLeviProjection F.Carrier B S q
  have hm : ∀ i, (refinedLeviEquiv F.Carrier B S).symm m i ∈
      refinedUnipotent F.Carrier (S i) (B.refinementWithin S S' i) :=
    refinedLeviEquiv_symm_mem B S S' hg
  have hq : g = ((refinedUnipotentPart F.Carrier B S q).val : B.Levi F.Carrier) * m.val :=
    congrArg Subtype.val (inv_mul_cancel_right q (refinedLeviSection F.Carrier B S m)).symm
  have hu : ((refinedUnipotentPart F.Carrier B S q).val : B.Levi F.Carrier) ∈
      refinedUnipotent F.Carrier B S :=
    (mem_refinedUnipotentRadical F.Carrier B S _).mp
      (refinedUnipotentPart F.Carrier B S q).property
  have h1 : refinedJacquetMk B S ρ (ρ g v) = refinedJacquetMk B S ρ (ρ m.val v) := by
    rw [hq, map_mul, Module.End.mul_apply]
    exact Jacquet.mk_apply_subgroup ρ (refinedUnipotent F.Carrier B S) ⟨_, hu⟩ _
  have hδ : T.refinedLeviInverseHalfModulus B S m = 1 :=
    (Jacquet.inverseHalfCharacter_eq_one _ m).mpr (refinedLeviModulus_eq_one T B S S' m hm)
  have h2 : flattenedAction T B S ρ ((flattenLeviEquiv B S).symm m)
      (refinedJacquetMk B S ρ v) = refinedJacquetMk B S ρ (ρ m.val v) := by
    change T.normalizedRefinedJacquet B S ρ
      ((flattenLeviEquiv B S) ((flattenLeviEquiv B S).symm m)) _ = _
    rw [MulEquiv.apply_symm_apply, T.normalizedRefinedJacquet_mk, hδ, Units.val_one, one_smul]
  rw [h1, ← h2]
  exact Jacquet.mk_apply_subgroup (flattenedAction T B S ρ)
    (refinedUnipotent F.Carrier (B.flatten S) S')
    ⟨_, flattenLeviEquiv_symm_mem B S S' m hm⟩ _

/-- The refined Jacquet module of the composed refinement maps onto the
coinvariants of the pulled-back normalized action for `S'`. -/
def composeJacquetMap :
    RefinedJacquetModule B (B.composeRefinement S S') ρ →ₗ[ℂ]
      Jacquet.Coinvariants (flattenedAction T B S ρ)
        (refinedUnipotent F.Carrier (B.flatten S) S') :=
  Jacquet.lift ρ (refinedUnipotent F.Carrier B (B.composeRefinement S S'))
    (Jacquet.mk (flattenedAction T B S ρ) (refinedUnipotent F.Carrier (B.flatten S) S') ∘ₗ
      refinedJacquetMk B S ρ)
    (fun u => LinearMap.ext fun v =>
      mk_refinedJacquetMk_composeRefinement T B S S' ρ u.property v)

theorem composeJacquetMap_surjective : Function.Surjective (composeJacquetMap T B S S' ρ) := by
  intro y
  obtain ⟨x, rfl⟩ := Jacquet.mk_surjective _ _ y
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective _ _ x
  exact ⟨refinedJacquetMk B (B.composeRefinement S S') ρ v, rfl⟩

/-- Nonzero iterated coinvariants give a nonzero composed refined Jacquet module. -/
theorem nontrivial_composeRefinement
    (h : Nontrivial (Jacquet.Coinvariants (flattenedAction T B S ρ)
      (refinedUnipotent F.Carrier (B.flatten S) S'))) :
    Nontrivial (RefinedJacquetModule B (B.composeRefinement S S') ρ) :=
  (composeJacquetMap_surjective T B S S' ρ).nontrivial

/-- The whole refinement has a nonzero refined Jacquet module when `V` is nonzero. -/
theorem nontrivial_wholeRefinement [Nontrivial V] :
    Nontrivial (RefinedJacquetModule B (wholeRefinement B) ρ) := by
  have hinj : Function.Injective (refinedJacquetMk B (wholeRefinement B) ρ) := by
    rw [← LinearMap.ker_eq_bot, Jacquet.ker_mk, Jacquet.relations_eq_span,
      Submodule.span_eq_bot]
    rintro _ ⟨⟨u, w⟩, rfl⟩
    have hu : (u : B.Levi F.Carrier) = 1 :=
      eq_one_of_mem_refinedUnipotent_wholeRefinement B u.property
    simp [hu]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact ⟨⟨refinedJacquetMk B (wholeRefinement B) ρ v, 0,
    fun h => hv (hinj (h.trans (map_zero _).symm))⟩⟩

end Representation

end MinimalRefinedJacquet

open MinimalRefinedJacquet

/-- Nonzero quasicuspidal refined Jacquet descent for every product Levi, every
rank including zero, and independent universes. -/
theorem minimalNonzeroRefinedJacquet {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : MinimalNonzeroRefinedJacquetTheorem.{uF, uV} F T := by
  let _ := T.topology
  intro n B A hA
  classical
  let P : ℕ → Prop := fun k =>
    ∃ S : BlockRefinement B, (B.flatten S).length = k ∧
      Nontrivial (RefinedJacquetModule B S A.representation)
  have hP₀ : P (B.flatten (wholeRefinement B)).length :=
    ⟨wholeRefinement B, rfl, nontrivial_wholeRefinement B A.representation⟩
  obtain ⟨S, hSk, hJ⟩ :=
    Nat.findGreatest_spec (P := P) (B.flatten (wholeRefinement B)).length_le hP₀
  refine ⟨S, hJ, fun S' hS' => ?_⟩
  by_contra hne
  rw [not_subsingleton_iff_nontrivial] at hne
  have hJ' := nontrivial_composeRefinement T B S S' A.representation hne
  have hlt : Nat.findGreatest P n < (B.flatten (B.composeRefinement S S')).length := by
    rw [← hSk, ← B.flatten_composeRefinement S S']
    exact (B.flatten S).length_lt_flatten S' F.Carrier hS'
  exact Nat.findGreatest_is_greatest hlt (B.flatten (B.composeRefinement S S')).length_le
    ⟨B.composeRefinement S S', rfl, hJ'⟩

/-- The specialization to the saturated carrier universe remains available. -/
example {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    MinimalNonzeroRefinedJacquetTheorem.{uF, max uF uV} F T :=
  minimalNonzeroRefinedJacquet.{uF, max uF uV} F T

end Langlands.CuspidalSupport
