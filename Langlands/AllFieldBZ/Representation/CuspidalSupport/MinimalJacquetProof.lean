import Langlands.AllFieldBZ.Representation.CuspidalSupport.MinimalJacquetStatement
import Langlands.AllFieldBZ.Representation.Parabolic.RefinementComposition
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.MinimalJacquetProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.MinimalJacquetProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
open Langlands.Geometric
universe u uV

section Order
variable {n : ℕ} (B : Langlands.GeneralLinear.BlockShape n)

end Order
section Flatten
variable {n : ℕ} (B : Langlands.GeneralLinear.BlockShape n) (S : BlockRefinement B)

variable (R : Type u) [CommRing R]

end Flatten
section WholeGroup
variable {n : ℕ} (B : Langlands.GeneralLinear.BlockShape n) (R : Type u) [CommRing R]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

end WholeGroup
end Langlands.AllFieldBZ.GeneralLinear.BlockShape
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding MinimalNonzeroJacquetTheorem minimalNonzeroJacquet
open Langlands.GeneralLinear
open Langlands.Geometric
open Langlands.Parabolic
universe uF uV

namespace MinimalJacquet
open Langlands.CuspidalSupport.MinimalJacquet hiding flattenJacquetMap flattenJacquetMap_surjective mk_jacquetMk_composedUnipotent nontrivial_flatten
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData) {n : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (B : BlockShape n) (S : BlockRefinement B)
  (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)

/-- An element of the composite radical acts trivially on the inner coinvariants of
the outer normalized Jacquet module, since the outer half-modulus is trivial on the
inner radical. -/
theorem mk_jacquetMk_composedUnipotent {g : GeneralLinear n F.Carrier}
    (hg : g ∈ composedUnipotent F.Carrier B S) (v : V) :
    Jacquet.mk (T.normalizedJacquet B ρ) (refinedUnipotent F.Carrier B S)
        (B.jacquetMk ρ (ρ g v)) =
      Jacquet.mk (T.normalizedJacquet B ρ) (refinedUnipotent F.Carrier B S)
        (B.jacquetMk ρ v) := by
  obtain ⟨hgP, hm⟩ := (mem_leviPreimage_iff F.Carrier B _ g).mp hg
  let q : B.parabolic F.Carrier := ⟨g, hgP⟩
  let m := B.leviProjection F.Carrier q
  have hq : q = (B.unipotentPart F.Carrier q).val * B.leviInParabolic F.Carrier m :=
    (inv_mul_cancel_right q (B.leviInParabolic F.Carrier m)).symm
  have h1 : B.jacquetMk ρ (ρ g v) = B.jacquetMk ρ (ρ (B.leviEmbedding F.Carrier m) v) := by
    change B.jacquetMk ρ ((ρ.comp (B.parabolic F.Carrier).subtype) q v) = _
    rw [hq, map_mul, Module.End.mul_apply]
    exact Jacquet.mk_apply_subgroup (ρ.comp (B.parabolic F.Carrier).subtype)
      (B.unipotentRadical F.Carrier) (B.unipotentPart F.Carrier q) _
  have hm1 : T.leviHalfModulus B m = 1 := T.leviHalfModulus_refinedUnipotent B S ⟨m, hm⟩
  have h2 : T.normalizedJacquet B ρ m (B.jacquetMk ρ v) =
      B.jacquetMk ρ (ρ (B.leviEmbedding F.Carrier m) v) := by
    rw [T.normalizedJacquet_mk_eq_inv_halfModulus, hm1, inv_one, one_smul]
  rw [h1, ← h2]
  exact Jacquet.mk_apply_subgroup (T.normalizedJacquet B ρ)
    (refinedUnipotent F.Carrier B S) ⟨m, hm⟩ _

/-- The flattened Jacquet module maps onto the inner coinvariants of the outer
normalized Jacquet module. -/
def flattenJacquetMap :
    (B.flatten S).JacquetModule ρ →ₗ[ℂ]
      Jacquet.Coinvariants (T.normalizedJacquet B ρ) (refinedUnipotent F.Carrier B S) :=
  Jacquet.lift (ρ.comp ((B.flatten S).parabolic F.Carrier).subtype)
    ((B.flatten S).unipotentRadical F.Carrier)
    (Jacquet.mk (T.normalizedJacquet B ρ) (refinedUnipotent F.Carrier B S) ∘ₗ
      B.jacquetMk ρ)
    (fun u => LinearMap.ext fun v =>
      mk_jacquetMk_composedUnipotent T B S ρ
        (B.flatten_unipotentSubgroup_le S F.Carrier ⟨u, u.property, rfl⟩) v)

theorem flattenJacquetMap_surjective : Function.Surjective (flattenJacquetMap T B S ρ) := by
  intro y
  obtain ⟨x, rfl⟩ := Jacquet.mk_surjective _ _ y
  obtain ⟨v, rfl⟩ := B.jacquetMk_surjective ρ x
  exact ⟨(B.flatten S).jacquetMk ρ v, rfl⟩

/-- Nonzero inner coinvariants give a nonzero flattened Jacquet module. -/
theorem nontrivial_flatten
    (h : Nontrivial
      (Jacquet.Coinvariants (T.normalizedJacquet B ρ) (refinedUnipotent F.Carrier B S))) :
    Nontrivial ((B.flatten S).JacquetModule ρ) :=
  (flattenJacquetMap_surjective T B S ρ).nontrivial

end MinimalJacquet
open Langlands.CuspidalSupport.MinimalJacquet hiding flattenJacquetMap flattenJacquetMap_surjective mk_jacquetMk_composedUnipotent nontrivial_flatten
/-- Nonzero quasicuspidal Jacquet descent for every rank, including rank zero. -/
theorem minimalNonzeroJacquet : MinimalNonzeroJacquetTheorem.{uF, uV} := by
  intro F T n A hA
  let := T.topology
  let := T.generalLinearTopology n
  classical
  let ρ := A.representation
  let P : ℕ → Prop := fun k =>
    ∃ B : BlockShape n, B.length = k ∧ Nontrivial (B.JacquetModule ρ)
  obtain ⟨B₀, hB₀⟩ := BlockShape.exists_length_le_one n
  have hP₀ : P B₀.length :=
    ⟨B₀, rfl, B₀.nontrivial_jacquetModule_of_length_le_one F.Carrier hB₀ ρ⟩
  obtain ⟨B, hBk, hJ⟩ := Nat.findGreatest_spec (P := P) B₀.length_le hP₀
  refine ⟨B, hJ, fun S hS => ?_⟩
  by_contra hne
  rw [not_subsingleton_iff_nontrivial] at hne
  have hJ' := Langlands.AllFieldBZ.CuspidalSupport.MinimalJacquet.nontrivial_flatten T B S ρ hne
  have hlt : Nat.findGreatest P n < (B.flatten S).length := by
    rw [← hBk]
    exact B.length_lt_flatten S F.Carrier hS
  exact Nat.findGreatest_is_greatest hlt (B.flatten S).length_le ⟨B.flatten S, rfl, hJ'⟩

end Langlands.AllFieldBZ.CuspidalSupport
