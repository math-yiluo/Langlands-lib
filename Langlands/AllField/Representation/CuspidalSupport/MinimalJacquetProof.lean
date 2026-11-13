import Langlands.Representation.CuspidalSupport.MinimalJacquetProof
import Langlands.AllField.Representation.CuspidalSupport.MinimalJacquetStatement
import Langlands.AllField.Representation.Parabolic.RefinementComposition
/-!
# Nonzero quasicuspidal Jacquet descent

A proof of `MinimalNonzeroJacquetTheorem` (BZ77 section 2.14(1)). A block shape
with at most one block has trivial radical, so the Jacquet module of a nonzero
representation along it is nonzero. Among the shapes with nonzero normalized
Jacquet module, take one with the largest number of blocks. If a proper
refinement of it had nonzero inner coinvariants, the flattened shape would have
more blocks and, through a surjection onto those coinvariants, a nonzero Jacquet
module.
-/

noncomputable section

namespace Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
open Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

open Langlands.Geometric

universe u uV

section Order

variable {n : ℕ} (B : BlockShape n)

end Order

section Flatten

variable {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

variable (R : Type u) [CommRing R]

end Flatten

section WholeGroup

variable {n : ℕ} (B : BlockShape n) (R : Type u) [CommRing R]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

end WholeGroup

end Langlands.AllField.GeneralLinear.BlockShape

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding MinimalNonzeroJacquetTheorem minimalNonzeroJacquet
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.Geometric
open Langlands.Parabolic

universe uF uV

namespace MinimalJacquet
open Langlands.CuspidalSupport.MinimalJacquet hiding flattenJacquetMap flattenJacquetMap_surjective mk_jacquetMk_composedUnipotent nontrivial_flatten
open Langlands.AllField.CuspidalSupport.MinimalJacquet
open Langlands.CuspidalSupport hiding MinimalNonzeroJacquetTheorem minimalNonzeroJacquet
open Langlands.AllField.CuspidalSupport

variable {F : Type uF} [Field F] (T : LocalFieldData F) {n : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (B : BlockShape n) (S : BlockRefinement B)
  (ρ : Representation ℂ (GeneralLinear n F) V)

/-- An element of the composite radical acts trivially on the inner coinvariants of
the outer normalized Jacquet module, since the outer half-modulus is trivial on the
inner radical. -/
theorem mk_jacquetMk_composedUnipotent {g : GeneralLinear n F}
    (hg : g ∈ composedUnipotent F B S) (v : V) :
    Jacquet.mk (T.normalizedJacquet B ρ) (refinedUnipotent F B S)
        (B.jacquetMk ρ (ρ g v)) =
      Jacquet.mk (T.normalizedJacquet B ρ) (refinedUnipotent F B S)
        (B.jacquetMk ρ v) := by
  obtain ⟨hgP, hm⟩ := (mem_leviPreimage_iff F B _ g).mp hg
  let q : B.parabolic F := ⟨g, hgP⟩
  let m := B.leviProjection F q
  have hq : q = (B.unipotentPart F q).val * B.leviInParabolic F m :=
    (inv_mul_cancel_right q (B.leviInParabolic F m)).symm
  have h1 : B.jacquetMk ρ (ρ g v) = B.jacquetMk ρ (ρ (B.leviEmbedding F m) v) := by
    change B.jacquetMk ρ ((ρ.comp (B.parabolic F).subtype) q v) = _
    rw [hq, map_mul, Module.End.mul_apply]
    exact Jacquet.mk_apply_subgroup (ρ.comp (B.parabolic F).subtype)
      (B.unipotentRadical F) (B.unipotentPart F q) _
  have hm1 : T.leviHalfModulus B m = 1 := T.leviHalfModulus_refinedUnipotent B S ⟨m, hm⟩
  have h2 : T.normalizedJacquet B ρ m (B.jacquetMk ρ v) =
      B.jacquetMk ρ (ρ (B.leviEmbedding F m) v) := by
    rw [T.normalizedJacquet_mk_eq_inv_halfModulus, hm1, inv_one, one_smul]
  rw [h1, ← h2]
  exact Jacquet.mk_apply_subgroup (T.normalizedJacquet B ρ)
    (refinedUnipotent F B S) ⟨m, hm⟩ _

/-- The flattened Jacquet module maps onto the inner coinvariants of the outer
normalized Jacquet module. -/
def flattenJacquetMap :
    (B.flatten S).JacquetModule ρ →ₗ[ℂ]
      Jacquet.Coinvariants (T.normalizedJacquet B ρ) (refinedUnipotent F B S) :=
  Jacquet.lift (ρ.comp ((B.flatten S).parabolic F).subtype)
    ((B.flatten S).unipotentRadical F)
    (Jacquet.mk (T.normalizedJacquet B ρ) (refinedUnipotent F B S) ∘ₗ
      B.jacquetMk ρ)
    (fun u => LinearMap.ext fun v =>
      mk_jacquetMk_composedUnipotent T B S ρ
        (B.flatten_unipotentSubgroup_le S F ⟨u, u.property, rfl⟩) v)

theorem flattenJacquetMap_surjective : Function.Surjective (flattenJacquetMap T B S ρ) := by
  intro y
  obtain ⟨x, rfl⟩ := Jacquet.mk_surjective _ _ y
  obtain ⟨v, rfl⟩ := B.jacquetMk_surjective ρ x
  exact ⟨(B.flatten S).jacquetMk ρ v, rfl⟩

/-- Nonzero inner coinvariants give a nonzero flattened Jacquet module. -/
theorem nontrivial_flatten
    (h : Nontrivial
      (Jacquet.Coinvariants (T.normalizedJacquet B ρ) (refinedUnipotent F B S))) :
    Nontrivial ((B.flatten S).JacquetModule ρ) :=
  (flattenJacquetMap_surjective T B S ρ).nontrivial

end MinimalJacquet

open Langlands.CuspidalSupport.MinimalJacquet hiding flattenJacquetMap flattenJacquetMap_surjective mk_jacquetMk_composedUnipotent nontrivial_flatten
open Langlands.AllField.CuspidalSupport.MinimalJacquet

/-- Nonzero quasicuspidal Jacquet descent for every rank, including rank zero. -/
theorem minimalNonzeroJacquet : MinimalNonzeroJacquetTheorem.{uF, uV} := by
  intro F _ T n A hA
  let := T.topology
  let := T.generalLinearTopology n
  classical
  let ρ := A.representation
  let P : ℕ → Prop := fun k =>
    ∃ B : BlockShape n, B.length = k ∧ Nontrivial (B.JacquetModule ρ)
  obtain ⟨B₀, hB₀⟩ := BlockShape.exists_length_le_one n
  have hP₀ : P B₀.length :=
    ⟨B₀, rfl, B₀.nontrivial_jacquetModule_of_length_le_one F hB₀ ρ⟩
  obtain ⟨B, hBk, hJ⟩ := Nat.findGreatest_spec (P := P) B₀.length_le hP₀
  refine ⟨B, hJ, fun S hS => ?_⟩
  by_contra hne
  rw [not_subsingleton_iff_nontrivial] at hne
  have hJ' := nontrivial_flatten T B S ρ hne
  have hlt : Nat.findGreatest P n < (B.flatten S).length := by
    rw [← hBk]
    exact B.length_lt_flatten S F hS
  exact Nat.findGreatest_is_greatest hlt (B.flatten S).length_le ⟨B.flatten S, rfl, hJ'⟩

end Langlands.AllField.CuspidalSupport
